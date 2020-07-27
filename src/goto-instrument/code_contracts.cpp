/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#include "code_contracts.h"
#include "loop_utils.h"
#include "pointer_predicates.h"

#include <algorithm>
#include <cstring>
#include <iostream>

#include <analyses/local_may_alias.h>

#include <goto-programs/remove_skip.h>

#include <linking/static_lifetime_init.h>

#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/message.h>
#include <util/pointer_offset_size.h>
#include <util/replace_symbol.h>
#include "expr2c.h"

/// Predicate to be used with the exprt::visit() function. The function
/// found_return_value() will return `true` iff this predicate is called on an
/// expr that contains `__CPROVER_return_value`.
class return_value_visitort : public const_expr_visitort
{
public:
  return_value_visitort() : const_expr_visitort()
  {
  }

  // \brief Has this object been passed to exprt::visit() on an exprt whose
  //        descendants contain __CPROVER_return_value?
  bool found_return_value()
  {
    return found;
  }

  void operator()(const exprt &exp) override
  {
    if(exp.id() != ID_symbol)
      return;
    const symbol_exprt &sym = to_symbol_expr(exp);
    found |= sym.get_identifier() == CPROVER_PREFIX "return_value";
  }

protected:
  bool found;
};

exprt get_size_or_throw(const typet &type, const namespacet &ns, messaget &log)
{
    auto size_of_opt = size_of_expr(type, ns);
    if(!size_of_opt.has_value())
    {
        log.error().source_location = type.source_location();
        log.error() << "unable to determine size of type: " << type2c(type, ns)
                    << messaget::eom;
        throw 0;
    }

    exprt result = size_of_opt.value();
    result.add(ID_C_c_sizeof_type) = type;
    return result;
}

static void check_apply_invariants(
  goto_functionst::goto_functiont &goto_function,
  const local_may_aliast &local_may_alias,
  const goto_programt::targett loop_head,
  const loopt &loop)
{
  assert(!loop.empty());

  // find the last back edge
  goto_programt::targett loop_end=loop_head;
  for(loopt::const_iterator
      it=loop.begin();
      it!=loop.end();
      ++it)
    if((*it)->is_goto() &&
       (*it)->get_target()==loop_head &&
       (*it)->location_number>loop_end->location_number)
      loop_end=*it;

  // see whether we have an invariant
  exprt invariant = static_cast<const exprt &>(
    loop_end->get_condition().find(ID_C_spec_loop_invariant));
  if(invariant.is_nil())
    return;

  // change H: loop; E: ...
  // to
  // H: assert(invariant);
  // havoc;
  // assume(invariant);
  // if(guard) goto E:
  // loop;
  // assert(invariant);
  // assume(false);
  // E: ...

  // find out what can get changed in the loop
  modifiest modifies;
  get_modifies(local_may_alias, loop, modifies);

  // build the havocking code
  goto_programt havoc_code;

  // assert the invariant
  {
    goto_programt::targett a = havoc_code.add(
      goto_programt::make_assertion(invariant, loop_head->source_location));
    a->source_location.set_comment("Loop invariant violated before entry");
  }

  // havoc variables being written to
  build_havoc_code(loop_head, modifies, havoc_code);

  // assume the invariant
  havoc_code.add(
    goto_programt::make_assumption(invariant, loop_head->source_location));

  // non-deterministically skip the loop if it is a do-while loop
  if(!loop_head->is_goto())
  {
    havoc_code.add(goto_programt::make_goto(
      loop_end,
      side_effect_expr_nondett(bool_typet(), loop_head->source_location)));
  }

  // Now havoc at the loop head. Use insert_swap to
  // preserve jumps to loop head.
  goto_function.body.insert_before_swap(loop_head, havoc_code);

  // assert the invariant at the end of the loop body
  {
    goto_programt::instructiont a =
      goto_programt::make_assertion(invariant, loop_end->source_location);
    a.source_location.set_comment("Loop invariant not preserved");
    goto_function.body.insert_before_swap(loop_end, a);
    ++loop_end;
  }

  // change the back edge into assume(false) or assume(guard)
  loop_end->targets.clear();
  loop_end->type=ASSUME;
  if(loop_head->is_goto())
    loop_end->set_condition(false_exprt());
  else
    loop_end->set_condition(boolean_negate(loop_end->get_condition()));
}

bool code_contractst::has_contract(const irep_idt fun_name)
{
  const symbolt &f_sym = ns.lookup(fun_name);
  const code_typet &type = to_code_type(f_sym.type);
  const exprt assigns =
    static_cast<const exprt &>(type.find(ID_C_spec_assigns));
  const exprt ensures =
    static_cast<const exprt &>(type.find(ID_C_spec_ensures));

  return ensures.is_not_nil() || assigns.is_not_nil();
}

bool code_contractst::apply_contract(
  const irep_idt &func_id,
  goto_programt &goto_program,
  goto_programt::targett target)
{
  const code_function_callt &call = target->get_function_call();

  // Return if the function is not named in the call; currently we don't handle
  // function pointers.
  // TODO: handle function pointers.
  if(call.function().id()!=ID_symbol)
    return false;

  // Retrieve the function type, which is needed to extract the contract components.
  const irep_idt &function=
    to_symbol_expr(call.function()).get_identifier();
  const symbolt &f_sym=ns.lookup(function);
  const code_typet &type=to_code_type(f_sym.type);

  // Isolate each component of the contract.
  exprt assigns =
    static_cast<const exprt&>(type.find(ID_C_spec_assigns));
  exprt requires=
    static_cast<const exprt&>(type.find(ID_C_spec_requires));
  exprt ensures=
    static_cast<const exprt&>(type.find(ID_C_spec_ensures));

  // Check to see if the function  contract actually constrains its effect on
  // the program state; if not, return.
  if(ensures.is_nil() && assigns.is_nil())
    return false;

  // Create a replace_symbolt object, for replacing expressions in the callee
  // with expressions from the call site (e.g. the return value).
  replace_symbolt replace;
  if(type.return_type() != empty_typet())
  {
    // Check whether the function's return value is not disregarded.
    if(call.lhs().is_not_nil())
    {
      // If so, have it replaced appropriately.
      // For example, if foo() ensures that its return value is > 5, then
      // rewrite calls to foo as follows:
      // x = foo() -> assume(__CPROVER_return_value > 5) -> assume(x > 5)
      symbol_exprt ret_val(CPROVER_PREFIX "return_value", call.lhs().type());
      replace.insert(ret_val, call.lhs());
    }
    else
    {
      // If the function does return a value, but the return value is
      // disregarded, check if the postcondition includes the return value.
      return_value_visitort v;
      ensures.visit(v);
      if(v.found_return_value())
      {
        // The postcondition does mention __CPROVER_return_value, so mint a
        // fresh variable to replace __CPROVER_return_value with.
        const symbolt &fresh = get_fresh_aux_symbol(
          type.return_type(),
          id2string(function),
          "ignored_return_value",
          call.source_location(),
          symbol_table.lookup_ref(function).mode,
          ns,
          symbol_table);
        symbol_exprt ret_val(CPROVER_PREFIX "return_value", type.return_type());
        replace.insert(ret_val, fresh.symbol_expr());
      }
    }
  }

  // Replace formal parameters
  code_function_callt::argumentst::const_iterator a_it =
    call.arguments().begin();
  for(code_typet::parameterst::const_iterator
      p_it=type.parameters().begin();
      p_it!=type.parameters().end() &&
      a_it!=call.arguments().end();
      ++p_it, ++a_it)
  {
    if(!p_it->get_identifier().empty())
    {
      symbol_exprt p(p_it->get_identifier(), p_it->type());
      replace.insert(p, *a_it);
    }
  }

  // Replace expressions in the contract components.
  replace(assigns);
  replace(requires);
  replace(ensures);

  // Insert assertion of the precondition immediately before the call site.
  if(requires.is_not_nil())
  {
    goto_programt::instructiont a =
      goto_programt::make_assertion(requires, target->source_location);

    goto_program.insert_before_swap(target, a);
    ++target;
  }

  // Create a series of non-deterministic assignments to havoc the variables
  // in the assigns clause.
  if(assigns.is_not_nil())
  {
    assigns_clauset assigns_cause(assigns, *this, func_id, log);
    goto_programt assigns_havoc = assigns_cause.havoc_code(f_sym.location, func_id, f_sym.mode);

    // Insert the non-deterministic assignment immediately before the call site.
    int lines_to_iterate = assigns_havoc.instructions.size();
    goto_program.insert_before_swap(target, assigns_havoc);
    std::advance(target, lines_to_iterate);
  }

  // To remove the function call, replace it with an assumption statement
  // assuming the postcondition, if there is one. Otherwise, replace the
  // function call with a SKIP statement.
  if(ensures.is_not_nil())
  {
    *target = goto_programt::make_assumption(ensures, target->source_location);
  }
  else
  {
    *target = goto_programt::make_skip();
  }

  // Add this function to the set of replaced functions.
  summarized.insert(function);
  return false;
}

void code_contractst::code_contracts(
  goto_functionst::goto_functiont &goto_function)
{
  local_may_aliast local_may_alias(goto_function);
  natural_loops_mutablet natural_loops(goto_function.body);

  // iterate over the (natural) loops in the function
  for(natural_loops_mutablet::loop_mapt::const_iterator
      l_it=natural_loops.loop_map.begin();
      l_it!=natural_loops.loop_map.end();
      l_it++)
    check_apply_invariants(
      goto_function,
      local_may_alias,
      l_it->first,
      l_it->second);

  // look at all function calls
  Forall_goto_program_instructions(ins, goto_function.body)
  {
    if(ins->is_function_call())
    {
      const code_function_callt &call = ins->get_function_call();

      // TODO we don't handle function pointers
      if(call.function().id() == ID_symbol)
      {
        const irep_idt &fun_name =
          to_symbol_expr(call.function()).get_identifier();

        apply_contract(fun_name, goto_function.body, ins);

      }
    }
  }
}

const symbolt &code_contractst::new_tmp_symbol(
  const typet &type,
  const source_locationt &source_location,
  const irep_idt &function_id,
  const irep_idt &mode) const
{
  return get_fresh_aux_symbol(
    type,
    id2string(function_id) + "::tmp_cc",
    "tmp_cc",
    source_location,
    mode,
    symbol_table);
}

const namespacet &code_contractst::get_namespace() const
{
    return ns;
}

exprt code_contractst::create_alias_expression(
  const exprt &lhs,
  std::vector<exprt> &aliasable_references)
{
  bool first_iter = true;
  exprt running = false_exprt();
  for(auto aliasble : aliasable_references)
  {
    exprt left_ptr = exprt(ID_address_of, pointer_type(lhs.type()), {lhs});
    exprt right_ptr = aliasble;

    exprt same_objct = same_object(left_ptr, right_ptr);
    exprt same_offset = equal_exprt(lhs,  typecast_exprt(right_ptr, lhs.type()));

    auto left_size = size_of_expr(pointer_offset(left_ptr).type(), ns);
    const exprt &compatible = same_offset;
    if(first_iter)
    {
      running = compatible;
      first_iter = false;
    }
    else
    {
      running = or_exprt(running, compatible);
    }
  }

  return running;
}

void code_contractst::instrument_assn_statement(
  const std::string &func_name,
  goto_programt::instructionst::iterator &ins_it,
  goto_programt &program,
  exprt &assigns,
  std::set<dstringt> &freely_assignable_symbols,
  assigns_clauset &assigns_clause)
{
  INVARIANT(
    ins_it->is_assign(),
    "The first argument of instrument_assn_statement should always be"
    " an assignment");

  const exprt &lhs = ins_it->get_assign().lhs();

  if(lhs.id() == ID_symbol &&
     freely_assignable_symbols.find(to_symbol_expr(lhs).get_identifier())
     != freely_assignable_symbols.end())
  {
    return;
  }

  exprt left_ptr = exprt(ID_address_of, pointer_type(lhs.type()), {lhs});
  if(lhs.id() == ID_dereference)
  {
      left_ptr = to_dereference_expr(lhs).pointer();
  }

  exprt alias_expr = assigns_clause.alias_expression(lhs);
  exprt cast_alias = not_exprt(
          binary_predicate_exprt(typecast_exprt(typecast_exprt(not_exprt(alias_expr), signed_long_int_type()), signed_long_int_type()), ID_notequal, constant_exprt(irep_idt(dstringt("0")), signed_long_int_type())));

  goto_programt alias_assertion;
  alias_assertion.add(
    goto_programt::make_assertion(cast_alias, ins_it->source_location));

    int lines_to_iterate = alias_assertion.instructions.size();
    program.insert_before_swap(ins_it, alias_assertion);
    std::advance(ins_it, lines_to_iterate);
}

void code_contractst::instrument_call_statement(
  goto_programt::instructionst::iterator &ins_it,
  goto_programt &program,
  exprt &assigns,
  const irep_idt &func_id,
  std::set<dstringt> &freely_assignable_symbols,
  assigns_clauset &assigns_clause)
{
  INVARIANT(
    ins_it->is_function_call(),
    "The first argument of instrument_call_statement should always be "
    "a function call");

  code_function_callt call = ins_it->get_function_call();
  const irep_idt &called_name =
    to_symbol_expr(call.function()).get_identifier();

  if(std::strcmp(called_name.c_str(), "malloc") == 0)
  {
    // Make freshly allocated memory assignable, if we can determine its type.
    goto_programt::instructionst::iterator local_ins_it = ins_it;
    local_ins_it++;
    if(local_ins_it->is_assign())
    {
      const exprt &rhs = local_ins_it->get_assign().rhs();
      if(rhs.id() == ID_typecast)
      {
        typet cast_type = rhs.type();

        assigns_clause_targett *new_target = assigns_clause.add_pointer_target(rhs);
        goto_programt &pointer_capture = new_target->get_init_block();

        int lines_to_iterate = pointer_capture.instructions.size();
        program.insert_before_swap(local_ins_it, pointer_capture);
        std::advance(ins_it, lines_to_iterate + 1);
      }
      else
      {
        log.error() << "Malloc is called but the result is not cast. "
                    << "Excluding result from the assignable memory frame ."
                    << messaget::eom;
      }
    }
    return; // assume malloc edits no pre-existing memory objects.
  }

  if(call.lhs().is_not_nil() && call.lhs().id() == ID_symbol &&
    freely_assignable_symbols.find(to_symbol_expr(call.lhs()).get_identifier())
    == freely_assignable_symbols.end())
  {
      /*
    exprt alias_expr =
      create_alias_expression(call.lhs(), aliasable_references);
       */
    exprt alias_expr = assigns_clause.alias_expression(call.lhs());


      goto_programt alias_assertion;
    alias_assertion.add(
      goto_programt::make_assertion(alias_expr, ins_it->source_location));
    program.insert_before_swap(ins_it, alias_assertion);
    ++ins_it;
  }

  // TODO we don't handle function pointers
  if(call.function().id() == ID_symbol)
  {
    const symbolt &called_sym = ns.lookup(called_name);
    const code_typet &called_type = to_code_type(called_sym.type);

    auto called_func = goto_functions.function_map.find(called_name);
    if(called_func == goto_functions.function_map.end())
    {
      log.error() << "Could not find function '" << called_name
                  << "' in goto-program; not enforcing assigns clause."
                  << messaget::eom;
      return;
    }

    exprt called_assigns = static_cast<const exprt &>(
      called_func->second.type.find(ID_C_spec_assigns));
    if(called_assigns.is_nil()) // Called function has no assigns clause
    {
      // Fail if called function has no assigns clause.
      log.error() << "No assigns specification found for function '"
                  << called_name
                  << "' in goto-program; not enforcing assigns clause."
                  << messaget::eom;

      // Create a false assertion, so the analysis will fail if this function is called.
      goto_programt failing_assertion;
      failing_assertion.add(
        goto_programt::make_assertion(false_exprt(), ins_it->source_location));
      program.insert_before_swap(ins_it, failing_assertion);
      ++ins_it;

      return;
    }
    else // Called function has assigns clause
    {
      replace_symbolt replace;
      // Replace formal parameters
      code_function_callt::argumentst::const_iterator a_it =
        call.arguments().begin();
      for(code_typet::parameterst::const_iterator p_it =
            called_type.parameters().begin();
          p_it != called_type.parameters().end() &&
          a_it != call.arguments().end();
          ++p_it, ++a_it)
      {
        if(!p_it->get_identifier().empty())
        {
          symbol_exprt p(p_it->get_identifier(), p_it->type());
          replace.insert(p, *a_it);
        }
      }

      replace(called_assigns);

      // check compatibility of assigns clause with the called function
      assigns_clauset called_assigns_clause(called_assigns, *this, func_id, log);
      exprt compat = assigns_clause.compatible_expression(called_assigns_clause);
      goto_programt alias_assertion;
      alias_assertion.add(
              goto_programt::make_assertion(compat, ins_it->source_location));
      program.insert_before_swap(ins_it, alias_assertion);
      ++ins_it;
    }
  }
}

bool code_contractst::check_for_looped_mallocs(const goto_programt &program)
{
  // Collect all GOTOs and mallocs
  std::vector<goto_programt::instructiont> back_gotos;
  std::vector<goto_programt::instructiont> malloc_calls;

  int idx = 0;
  for(goto_programt::instructiont ins : program.instructions)
  {
    if(ins.is_backwards_goto())
    {
      back_gotos.push_back(ins);
    }
    if(ins.is_function_call())
    {
      code_function_callt call = ins.get_function_call();
      const irep_idt &called_name =
        to_symbol_expr(call.function()).get_identifier();

      if(std::strcmp(called_name.c_str(), "malloc") == 0)
      {
        malloc_calls.push_back(ins);
      }
    }
    idx++;
  }
  // Make sure there are no gotos that go back such that a malloc is between the goto and its destination (possible loop).
  for(auto goto_entry : back_gotos)
  {
    for(const auto &t : goto_entry.targets)
    {
      for(auto malloc_entry : malloc_calls)
      {
        if(malloc_entry.location_number >= t->location_number &&
          malloc_entry.location_number < goto_entry.location_number) {
          log.error() << "Call to malloc at location "
                      << malloc_entry.location_number << " falls between goto "
                      << "source location " << goto_entry.location_number
                      << " and it's destination at location "
                      << t->location_number << ". "
                      << "Unable to complete instrumentation, as this malloc "
                      << "may be in a loop."
                      << messaget::eom;
          throw 0;
        }
      }
    }
  }
  return false;
}

bool code_contractst::add_pointer_checks(const std::string &func_name)
{
  // Get the function object before instrumentation.
  auto old_fun = goto_functions.function_map.find(func_name);
  if(old_fun == goto_functions.function_map.end())
  {
    log.error() << "Could not find function '" << func_name
                << "' in goto-program; not enforcing contracts."
                << messaget::eom;
    return true;
  }
  goto_programt &program = old_fun->second.body;
  if(program.instructions.empty()) // empty function body
  {
    return false;
  }

  const irep_idt func_id(func_name);
  const symbolt &f_sym = ns.lookup(func_id);
  const code_typet &type = to_code_type(f_sym.type);

  exprt assigns_expr = static_cast<const exprt &>(type.find(ID_C_spec_assigns));
  assigns_clauset assigns(assigns_expr, *this, func_id, log);
  // Return if there are no reference checks to perform.
  if(assigns_expr.is_nil())
    return false;

  goto_programt::instructionst::iterator ins_it = program.instructions.begin();

  // Create temporary variables to hold the assigns clause targets before they can be modified.
  goto_programt standin_decls = assigns.init_block(f_sym.location);
  goto_programt mark_dead = assigns.dead_stmts(f_sym.location, func_name, f_sym.mode);

  // Create a list of variables that are okay to assign.
  std::set<dstringt> freely_assignable_symbols;
  for(code_typet::parametert param : type.parameters())
  {
    freely_assignable_symbols.insert(param.get_identifier());
  }

  int lines_to_iterate = standin_decls.instructions.size();
  program.insert_before_swap(ins_it, standin_decls);
  std::advance(ins_it, lines_to_iterate);

  if(check_for_looped_mallocs(program))
  {
    return true;
  }

  // Insert aliasing assertions
  for(; ins_it != program.instructions.end(); std::advance(ins_it, 1))
  {
    if(ins_it->is_decl())
    {
      freely_assignable_symbols.insert(ins_it->get_decl().symbol().get_identifier());

      assigns_clause_targett *new_target = assigns.add_target(ins_it->get_decl().symbol());
      goto_programt &pointer_capture = new_target->get_init_block();

      lines_to_iterate = pointer_capture.instructions.size();
      for(auto in : pointer_capture.instructions)
      {
        program.insert_after(ins_it, in);
        std::advance(ins_it, 1);
      }
    }
    else if(ins_it->is_assign())
    {
      instrument_assn_statement(func_name, ins_it, program, assigns_expr, freely_assignable_symbols, assigns);
    }
    else if(ins_it->is_function_call())
    {
      instrument_call_statement(ins_it, program, assigns_expr, func_id, freely_assignable_symbols, assigns);
    }
  }

  // walk the iterator back to the last statement
  while(!ins_it->is_end_function()) {std::advance(ins_it, -1);}

  // Make sure the temporary symbols are marked dead
  lines_to_iterate = mark_dead.instructions.size();
  program.insert_before_swap(ins_it, mark_dead);

  return false;
}

bool code_contractst::enforce_contract(const std::string &fun_to_enforce)
{
  // Add statements to the source function to ensure assigns clause is respected.
  add_pointer_checks(fun_to_enforce);

  // Rename source function
  std::stringstream ss;
  ss << CPROVER_PREFIX << "contracts_original_" << fun_to_enforce;
  const irep_idt mangled(ss.str());
  const irep_idt original(fun_to_enforce);

  auto old_fun = goto_functions.function_map.find(original);
  if(old_fun == goto_functions.function_map.end())
  {
    log.error() << "Could not find function '" << fun_to_enforce
                << "' in goto-program; not enforcing contracts."
                << messaget::eom;
    return true;
  }

  std::swap(goto_functions.function_map[mangled], old_fun->second);
  goto_functions.function_map.erase(old_fun);

  // Place a new symbol with the mangled name into the symbol table
  source_locationt sl;
  sl.set_file("instrumented for code contracts");
  sl.set_line("0");
  symbolt mangled_sym;
  const symbolt *original_sym = symbol_table.lookup(original);
  mangled_sym = *original_sym;
  mangled_sym.name = mangled;
  mangled_sym.base_name = mangled;
  mangled_sym.location = sl;
  const auto mangled_found = symbol_table.insert(std::move(mangled_sym));
  INVARIANT(
    mangled_found.second,
    "There should be no existing function called " + ss.str() +
      " in the symbol table because that name is a mangled name");


  // Insert wrapper function into goto_functions
  auto nexist_old_fun = goto_functions.function_map.find(original);
  INVARIANT(
    nexist_old_fun == goto_functions.function_map.end(),
    "There should be no function called " + fun_to_enforce +
      " in the function map because that function should have had its"
      " name mangled");

  auto mangled_fun = goto_functions.function_map.find(mangled);
  INVARIANT(
    mangled_fun != goto_functions.function_map.end(),
    "There should be a function called " + ss.str() +
      " in the function map because we inserted a fresh goto-program"
      " with that mangled name");

  goto_functiont &wrapper = goto_functions.function_map[original];
  wrapper.parameter_identifiers = mangled_fun->second.parameter_identifiers;
  if(mangled_fun->second.type.is_not_nil())
    wrapper.type = mangled_fun->second.type;
  wrapper.body.add(goto_programt::make_end_function(sl));
  add_contract_check(original, mangled, wrapper.body);

  return false;
}

void code_contractst::add_contract_check(
  const irep_idt &wrapper_fun,
  const irep_idt &mangled_fun,
  goto_programt &dest)
{
  assert(!dest.instructions.empty());

  goto_functionst::function_mapt::iterator f_it =
    goto_functions.function_map.find(mangled_fun);
  assert(f_it!=goto_functions.function_map.end());

  const goto_functionst::goto_functiont &gf=f_it->second;

  const exprt &assigns=
                 static_cast<const exprt&>(gf.type.find(ID_C_spec_assigns));
  const exprt &requires=
                 static_cast<const exprt&>(gf.type.find(ID_C_spec_requires));
  const exprt &ensures=
    static_cast<const exprt&>(gf.type.find(ID_C_spec_ensures));
  assert(ensures.is_not_nil() || assigns.is_not_nil());

  // build:
  // if(nondet)
  //   decl ret
  //   decl parameter1 ...
  //   assume(requires)  [optional]
  //   ret=function(parameter1, ...)
  //   assert(ensures)
  // skip: ...

  // build skip so that if(nondet) can refer to it
  goto_programt tmp_skip;
  goto_programt::targett skip =
    tmp_skip.add(goto_programt::make_skip(ensures.source_location()));

  goto_programt check;

  // prepare function call including all declarations
  const symbolt &function_symbol = ns.lookup(mangled_fun);
  code_function_callt call(function_symbol.symbol_expr());
  replace_symbolt replace;

  // decl ret
  code_returnt return_stmt;
  if(gf.type.return_type()!=empty_typet())
  {
    symbol_exprt r = new_tmp_symbol(
                       gf.type.return_type(),
                       skip->source_location,
                       wrapper_fun,
                       function_symbol.mode)
                       .symbol_expr();
    check.add(goto_programt::make_decl(r, skip->source_location));

    call.lhs()=r;
    return_stmt = code_returnt(r);

    symbol_exprt ret_val(CPROVER_PREFIX "return_value", call.lhs().type());
    replace.insert(ret_val, r);
  }

  // decl parameter1 ...
  for(const auto &parameter : gf.parameter_identifiers)
  {
    PRECONDITION(!parameter.empty());
    const symbolt &parameter_symbol = ns.lookup(parameter);

    symbol_exprt p = new_tmp_symbol(
                       parameter_symbol.type,
                       skip->source_location,
                       wrapper_fun,
                       parameter_symbol.mode)
                       .symbol_expr();
    check.add(goto_programt::make_decl(p, skip->source_location));
    check.add(goto_programt::make_assignment(p, parameter_symbol.symbol_expr(), skip->source_location));

    call.arguments().push_back(p);

    replace.insert(parameter_symbol.symbol_expr(), p);
  }

  // assume(requires)
  if(requires.is_not_nil())
  {
    // rewrite any use of parameters
    exprt requires_cond = requires;
    replace(requires_cond);

    check.add(goto_programt::make_assumption(
      requires_cond, requires.source_location()));
  }

  // ret=mangled_fun(parameter1, ...)
  check.add(goto_programt::make_function_call(call, skip->source_location));

  // rewrite any use of __CPROVER_return_value
  exprt ensures_cond = ensures;
  replace(ensures_cond);

  // assert(ensures)
  if(ensures.is_not_nil())
  {
    check.add(
      goto_programt::make_assertion(ensures_cond, ensures.source_location()));
  }

  if(gf.type.return_type()!=empty_typet())
  {
    check.add(goto_programt::make_return(return_stmt, skip->source_location));
  }

  // prepend the new code to dest
  check.destructive_append(tmp_skip);
  dest.destructive_insert(dest.instructions.begin(), check);
}

bool code_contractst::replace_calls(
  const std::set<std::string> &funs_to_replace)
{
  bool fail = false;
  for(const auto &fun : funs_to_replace)
  {
    if(!has_contract(fun))
    {
      log.error() << "Function '" << fun
                  << "' does not have a contract; "
                     "not replacing calls with contract."
                  << messaget::eom;
      fail = true;
    }
  }
  if(fail)
    return true;

  for(auto &goto_function : goto_functions.function_map)
  {
    Forall_goto_program_instructions(ins, goto_function.second.body)
    {
      if(ins->is_function_call())
      {
        const code_function_callt &call = ins->get_function_call();

        // TODO we don't handle function pointers
        if(call.function().id() != ID_symbol)
          continue;

        const irep_idt &fun_name =
          to_symbol_expr(call.function()).get_identifier();
        auto found = std::find(
          funs_to_replace.begin(), funs_to_replace.end(), id2string(fun_name));
        if(found == funs_to_replace.end())
          continue;


        fail |= apply_contract(fun_name, goto_function.second.body, ins);
      }
    }
  }

  if(fail)
    return true;

  for(auto &goto_function : goto_functions.function_map)
    remove_skip(goto_function.second.body);

  goto_functions.update();

  return false;
}

bool code_contractst::replace_calls()
{
  std::set<std::string> funs_to_replace;
  for(auto &goto_function : goto_functions.function_map)
  {
    if(has_contract(goto_function.first))
      funs_to_replace.insert(id2string(goto_function.first));
  }
  return replace_calls(funs_to_replace);
}

bool code_contractst::enforce_contracts()
{
  std::set<std::string> funs_to_enforce;
  for(auto &goto_function : goto_functions.function_map)
  {
    if(has_contract(goto_function.first))
      funs_to_enforce.insert(id2string(goto_function.first));
  }
  return enforce_contracts(funs_to_enforce);
}

bool code_contractst::enforce_contracts(
  const std::set<std::string> &funs_to_enforce)
{
  bool fail = false;
  for(const auto &fun : funs_to_enforce)
  {
    if(!has_contract(fun))
    {
      fail = true;
      log.error() << "Could not find function '" << fun
                  << "' in goto-program; not enforcing contracts."
                  << messaget::eom;
      continue;
    }

    if(!fail)
      fail |= enforce_contract(fun);
  }
  return fail;
}

/*********************************************
 *  Assigns Clause Target - Scalar
 ********************************************/
assigns_clause_scalar_targett::assigns_clause_scalar_targett(const exprt &obj_ptr, const code_contractst &contr, messaget &log_param, const irep_idt &func_id) :
        assigns_clause_targett(Scalar, pointer_for(obj_ptr), contr, log_param), local_standin_var(typet())
{
  const symbolt &f_sym = contract.get_namespace().lookup(func_id);

    // Declare a new symbol to stand in for the reference
    symbolt standin_symbol = contract.new_tmp_symbol(
            obj_pointer.type(),
            f_sym.location,
            func_id,
            f_sym.mode);

    local_standin_var = standin_symbol.symbol_expr();

    // Build standin variable initialization block
    init_block.add(goto_programt::make_decl(local_standin_var, f_sym.location));
    init_block.add(goto_programt::make_assignment(
            code_assignt(local_standin_var, obj_pointer), f_sym.location));

}

std::vector<symbol_exprt> assigns_clause_scalar_targett::temporary_declarations() const
{
    std::vector<symbol_exprt> result;
    result.push_back(local_standin_var);
    return result;
}

exprt assigns_clause_scalar_targett::alias_expression(const exprt &ptr)
{
    return same_object(ptr, local_standin_var);
}

exprt assigns_clause_scalar_targett::compatible_expression(
        const assigns_clause_targett &called_target)
{
    if(called_target.tgt_type == Scalar)
    {
      return alias_expression(called_target.get_direct_pointer());
    }
    else // Struct or Array
    {
        return false_exprt();
    }
}

goto_programt assigns_clause_scalar_targett::havoc_code(source_locationt loc) const
{
  goto_programt assigns_havoc;

  exprt lhs = dereference_exprt(obj_pointer);
  side_effect_expr_nondett rhs(lhs.type(), loc);

  goto_programt::targett t = assigns_havoc.add(goto_programt::make_assignment(
    code_assignt(std::move(lhs), std::move(rhs)), loc));
  t->code.add_source_location()=loc;

  return assigns_havoc;
}

/*********************************************
 *  Assigns Clause Target - Struct
 ********************************************/
assigns_clause_struct_targett::assigns_clause_struct_targett(const exprt &obj_ptr, const code_contractst &contr, messaget &log_param, const irep_idt &func_id) :
        assigns_clause_targett(Struct, pointer_for(obj_ptr), contr, log_param), main_struct_standin(typet())
{
    const symbolt &struct_sym = contract.get_namespace().lookup(to_tag_type(obj_ptr.type()));
    const symbolt &f_sym = contract.get_namespace().lookup(func_id);

    // Declare a new symbol to stand in for the reference
    symbolt struct_temp_symbol = contract.new_tmp_symbol(
      obj_pointer.type(),
            f_sym.location,
            func_id,
            f_sym.mode);
    main_struct_standin = struct_temp_symbol.symbol_expr();
    local_standin_vars.push_back(main_struct_standin);

    // Build standin variable initialization block
    init_block.add(goto_programt::make_decl(main_struct_standin, f_sym.location));
    init_block.add(goto_programt::make_assignment(
            code_assignt(main_struct_standin, obj_pointer), f_sym.location));


    // Handle component members
    std::vector<exprt> component_members;
    const struct_typet &struct_t = to_struct_type(struct_sym.type);
    for(struct_union_typet::componentt comp : struct_t.components())
    {
        exprt curr_member = member_exprt(obj_ptr, comp);
        component_members.push_back(curr_member);
    }

    while(!component_members.empty())
    {
        exprt curr_op = component_members.front();
        exprt op_addr = pointer_for(curr_op);

      // Declare a new symbol to stand in for the reference
        symbolt standin_symbol = contract.new_tmp_symbol(
          op_addr.type(),
                f_sym.location,
                func_id,
                f_sym.mode);

        symbol_exprt curr_standin = standin_symbol.symbol_expr();
        local_standin_vars.push_back(curr_standin);

        // Add to standin variable initialization block
        init_block.add(goto_programt::make_decl(curr_standin, f_sym.location));
        init_block.add(goto_programt::make_assignment(
                code_assignt(curr_standin, op_addr), f_sym.location));

        if(curr_op.type().id() == ID_struct_tag)
        {
            const symbolt &curr_struct_sym = contract.get_namespace().lookup(to_tag_type(curr_op.type()));

            const struct_typet &curr_struct_t = to_struct_type(curr_struct_sym.type);
            for(struct_union_typet::componentt comp : curr_struct_t.components())
            {
                exprt curr_member = member_exprt(curr_op, comp);
                component_members.push_back(curr_member);
            }
        }
      component_members.erase(component_members.begin());
    }
}

std::vector<symbol_exprt> assigns_clause_struct_targett::temporary_declarations() const
{
    return local_standin_vars;
}

exprt assigns_clause_struct_targett::alias_expression(const exprt &ptr)
{
    exprt running = false_exprt();
    bool first_iter = true;
    for(symbol_exprt sym : local_standin_vars)
    {
      typet ptr_concrete_type = dereference_exprt(ptr).type();
      auto left_size = size_of_expr(ptr_concrete_type, contract.get_namespace());
      typet standin_concrete_type = dereference_exprt(sym).type();
      auto right_size = size_of_expr(standin_concrete_type, contract.get_namespace());
        if(!left_size.has_value())
        {
            log.error().source_location = ptr.source_location();
            log.error() << "unable to determine size of type: " << type2c(ptr_concrete_type, contract.get_namespace())
                        << messaget::eom;
            throw 0;
        }
        if(!right_size.has_value())
        {
            log.error().source_location = ptr.source_location();
            log.error() << "unable to determine size of type: " << type2c(standin_concrete_type, contract.get_namespace())
                        << messaget::eom;
            throw 0;
        }
        if(std::strcmp(left_size.value().get(ID_value).c_str(), right_size.value().get(ID_value).c_str()) == 0)
        {
            exprt same_obj = same_object(ptr, sym);
            exprt same_offset = equal_exprt(pointer_offset(ptr), pointer_offset(sym));

            const exprt &compatible
                    = and_exprt(same_obj, same_offset);
            if(first_iter)
            {
                running = compatible;
                first_iter = false;
            }
            else
            {
                running = or_exprt(running, compatible);
            }
        }
    }

    return running;
}

exprt assigns_clause_struct_targett::compatible_expression(
        const assigns_clause_targett &called_target)
{
    if(called_target.tgt_type == Scalar)
    {
      return alias_expression(called_target.get_direct_pointer());
    }
    else if(called_target.tgt_type == Struct)
    {
        const assigns_clause_struct_targett &struct_target
                = static_cast<const assigns_clause_struct_targett &>(called_target);

        exprt same_obj = same_object(this->main_struct_standin, struct_target.obj_pointer);
        // the size of the called struct should be less than or equal to that of the assignable target struct.
        exprt curr_size = get_size_or_throw(this->obj_pointer.type(), contract.get_namespace(), log);
        exprt curr_upper_offset = pointer_offset(plus_exprt(this->main_struct_standin, curr_size));
        exprt called_size = get_size_or_throw(struct_target.obj_pointer.type(), contract.get_namespace(), log);
        exprt called_upper_offset = pointer_offset(plus_exprt(struct_target.obj_pointer, called_size));

        exprt in_range_lower = binary_predicate_exprt(pointer_offset(struct_target.obj_pointer), ID_ge, pointer_offset(this->main_struct_standin));
        exprt in_range_upper = binary_predicate_exprt(curr_upper_offset, ID_ge, called_upper_offset);

        exprt in_range = and_exprt(in_range_lower, in_range_upper);
        return and_exprt(same_obj, in_range);
    }
    else // Array
    {
        return false_exprt();
    }
}

goto_programt assigns_clause_struct_targett::havoc_code(source_locationt loc) const
{
  goto_programt assigns_havoc;

  exprt lhs = dereference_exprt(obj_pointer);
  side_effect_expr_nondett rhs(lhs.type(), loc);

  goto_programt::targett t = assigns_havoc.add(goto_programt::make_assignment(
    code_assignt(std::move(lhs), std::move(rhs)), loc));
  t->code.add_source_location()=loc;

  return assigns_havoc;
}

/*********************************************
 *  Assigns Clause Target - Array
 ********************************************/
assigns_clause_array_targett::assigns_clause_array_targett(const exprt &obj_ptr, const code_contractst &contr, messaget &log_param, const irep_idt &func_id) :
        assigns_clause_targett(Array, obj_ptr.op0(), contr, log_param),lower_offset_obj(), upper_offset_obj(), arr_standin_var(typet()), lower_offset_var(typet()), upper_offset_var(typet())
{
  const exprt &arr = obj_ptr.op0();
  const exprt &range = obj_ptr.op1();

  // If the range doesn't have operands, it is just a single value
  const exprt &lower_op = range.has_operands() ? range.op0() : range;
  const exprt &upper_op = range.has_operands() ? range.op1() : range;

  const symbolt &f_sym = contract.get_namespace().lookup(func_id);

  // Declare a new symbol to stand in for the reference
  symbolt standin_symbol = contract.new_tmp_symbol(
          obj_pointer.type(),
          f_sym.location,
          func_id,
          f_sym.mode);

  arr_standin_var = standin_symbol.symbol_expr();

  // Add array temp to variable initialization block
  init_block.add(goto_programt::make_decl(arr_standin_var, f_sym.location));
  init_block.add(goto_programt::make_assignment(
          code_assignt(arr_standin_var, obj_pointer), f_sym.location));

  if(lower_op.id() == ID_constant)
  {
    int lowerbase = std::stoi(to_constant_expr(lower_op).get(ID_C_base).c_str(), nullptr, 10);
    lower_bound = std::stoi(to_constant_expr(lower_op).get_value().c_str(), nullptr, lowerbase);

    dstringt lower_const_string(std::to_string(lower_bound));
    irep_idt lower_const_irep(lower_const_string);
    constant_exprt lower_val_const(lower_const_irep, lower_op.type());

    exprt lower_constant_size = get_size_or_throw(arr.type().subtype(), contract.get_namespace(), log);
    lower_offset_obj = typecast_exprt(mult_exprt(typecast_exprt(lower_val_const, unsigned_long_int_type()), lower_constant_size), signed_int_type());

    // Declare a new symbol to stand in for the reference
    symbolt lower_standin_symbol = contract.new_tmp_symbol(
      lower_offset_obj.type(),
      f_sym.location,
      func_id,
      f_sym.mode);

    lower_offset_var = lower_standin_symbol.symbol_expr();

    // Add array temp to variable initialization block
    init_block.add(goto_programt::make_decl(lower_offset_var, f_sym.location));
    init_block.add(goto_programt::make_assignment(
      code_assignt(lower_offset_var, lower_offset_obj), f_sym.location));
  }
  else
  {
    exprt lower_constant_size = get_size_or_throw(arr.type().subtype(), contract.get_namespace(), log);
    lower_offset_obj = typecast_exprt(mult_exprt(typecast_exprt(lower_op, unsigned_long_int_type()), lower_constant_size), signed_int_type());

    // Declare a new symbol to stand in for the reference
    symbolt lower_standin_symbol = contract.new_tmp_symbol(
      lower_offset_obj.type(),
      f_sym.location,
      func_id,
      f_sym.mode);

    lower_offset_var = lower_standin_symbol.symbol_expr();

    // Add array temp to variable initialization block
    init_block.add(goto_programt::make_decl(lower_offset_var, f_sym.location));
    init_block.add(goto_programt::make_assignment(
      code_assignt(lower_offset_var, lower_offset_obj), f_sym.location));
  }

  if(upper_op.id() == ID_constant)
  {
    int upperbase = std::stoi(to_constant_expr(upper_op).get(ID_C_base).c_str(), nullptr, 10);
    upper_bound = std::stoi(to_constant_expr(upper_op).get_value().c_str(), nullptr, upperbase);

    dstringt upper_const_string(std::to_string(upper_bound));
    irep_idt upper_const_irep(upper_const_string);
    constant_exprt upper_val_const(upper_const_irep, upper_op.type());

    exprt upper_constant_size = get_size_or_throw(arr.type().subtype(), contract.get_namespace(), log);
    upper_offset_obj = typecast_exprt(mult_exprt(typecast_exprt(upper_val_const, unsigned_long_int_type()), upper_constant_size), signed_int_type());

    // Declare a new symbol to stand in for the reference
    symbolt upper_standin_symbol = contract.new_tmp_symbol(
      upper_offset_obj.type(),
      f_sym.location,
      func_id,
      f_sym.mode);

    upper_offset_var = upper_standin_symbol.symbol_expr();

    // Add array temp to variable initialization block
    init_block.add(goto_programt::make_decl(upper_offset_var, f_sym.location));
    init_block.add(goto_programt::make_assignment(
      code_assignt(upper_offset_var, upper_offset_obj), f_sym.location));
  }
  else
  {
    exprt upper_constant_size = get_size_or_throw(arr.type().subtype(), contract.get_namespace(), log);
    upper_offset_obj = typecast_exprt(mult_exprt(typecast_exprt(upper_op, unsigned_long_int_type()), upper_constant_size), signed_int_type());

    // Declare a new symbol to stand in for the reference
    symbolt upper_standin_symbol = contract.new_tmp_symbol(
      upper_offset_obj.type(),
      f_sym.location,
      func_id,
      f_sym.mode);

    upper_offset_var = upper_standin_symbol.symbol_expr();

    // Add array temp to variable initialization block
    init_block.add(goto_programt::make_decl(upper_offset_var, f_sym.location));
    init_block.add(goto_programt::make_assignment(
      code_assignt(upper_offset_var, upper_offset_obj), f_sym.location));
  }
}

std::vector<symbol_exprt> assigns_clause_array_targett::temporary_declarations() const
{
    std::vector<symbol_exprt> result;
    result.push_back(arr_standin_var);
    result.push_back(lower_offset_var);
    result.push_back(upper_offset_var);

    return result;
}

goto_programt assigns_clause_array_targett::havoc_code(source_locationt loc) const
{
  goto_programt assigns_havoc;

  modifiest assigns_tgts;
  //code_fort()
  typet lower_type = lower_offset_var.type();
  exprt array_type_size = get_size_or_throw(obj_pointer.type().subtype(), contract.get_namespace(), log);

  for(int i = lower_bound; i<= upper_bound; ++i)
  {
    dstringt offset_string(std::to_string(i));
    irep_idt offset_irep(offset_string);
    constant_exprt val_const(offset_irep, lower_type);
    dereference_exprt array_deref(plus_exprt(obj_pointer, typecast_exprt(val_const, signed_long_int_type())));

    //exprt offset = typecast_exprt(mult_exprt(typecast_exprt(val_const, unsigned_long_int_type()), array_type_size), signed_int_type());
    assigns_tgts.insert(array_deref);


  }

  for(auto lhs : assigns_tgts)
  {
    side_effect_expr_nondett rhs(lhs.type(), loc);

    goto_programt::targett t = assigns_havoc.add(goto_programt::make_assignment(
      code_assignt(std::move(lhs), std::move(rhs)), loc));
    t->code.add_source_location()=loc;
  }

  return assigns_havoc;
}

exprt assigns_clause_array_targett::alias_expression(const exprt &ptr)
{
  exprt same_obj = same_object(ptr, arr_standin_var);
  exprt ptr_offset = pointer_offset(ptr);

  exprt in_range_lower = binary_predicate_exprt(ptr_offset, ID_ge, typecast_exprt(lower_offset_var, ptr_offset.type()));
  exprt in_range_upper = binary_predicate_exprt(typecast_exprt(upper_offset_var, ptr_offset.type()), ID_ge, ptr_offset);
  exprt in_range = and_exprt(in_range_lower, in_range_upper);

  // Troublesome
  return and_exprt(same_obj, in_range);
}

exprt assigns_clause_array_targett::compatible_expression(
        const assigns_clause_targett &called_target)
{
    if(called_target.tgt_type == Scalar)
    {
        return alias_expression(called_target.get_direct_pointer());
    }
    else if(called_target.tgt_type == Array)
    {
        const assigns_clause_array_targett &array_target
                = static_cast<const assigns_clause_array_targett &>(called_target);
        exprt same_obj = same_object(this->arr_standin_var, array_target.obj_pointer);
        exprt in_range_lower = binary_predicate_exprt(array_target.lower_offset_obj, ID_ge, this->lower_offset_var);
        exprt in_range_upper = binary_predicate_exprt(this->upper_offset_var, ID_ge, array_target.upper_offset_obj);
        exprt in_range = and_exprt(in_range_lower, in_range_upper);
        return and_exprt(same_obj, in_range);
    }
    else // Struct
    {
        return false_exprt();
    }
}

/*********************************************
 *  Assigns Clause
 ********************************************/
assigns_clauset::assigns_clauset(const exprt &assigns, code_contractst &contract,
                                 const irep_idt f_id, messaget log_param):
        assigns_expr(assigns), parent(contract), func_id(f_id), log(log_param)
{
    for(exprt curr_op : assigns_expr.operands())
    {
        add_target(curr_op);
    }
}
assigns_clauset::~assigns_clauset()
{
    for(assigns_clause_targett* tgt : targets)
    {
        delete tgt;
    }
}

assigns_clause_targett* assigns_clauset::add_target(exprt curr_op)
{
    if(curr_op.id() == ID_array_range)
    {
        assigns_clause_array_targett* array_tgt = new assigns_clause_array_targett(curr_op, parent, log, func_id);
        targets.push_back(array_tgt);
        return array_tgt;
    }
    else if(curr_op.type().id() == ID_struct_tag)
    {
      assigns_clause_struct_targett* struct_tgt = new assigns_clause_struct_targett(curr_op, parent, log, func_id);
      targets.push_back(struct_tgt);
      return struct_tgt;
    }
    else
    {
        assigns_clause_scalar_targett* scalar_tgt = new assigns_clause_scalar_targett(curr_op, parent, log, func_id);
        targets.push_back(scalar_tgt);
        return scalar_tgt;
    }
}

assigns_clause_targett* assigns_clauset::add_pointer_target(exprt curr_op)
{
  return add_target(dereference_exprt(curr_op));
}

goto_programt assigns_clauset::init_block(source_locationt loc)
{
    goto_programt result;
    for(assigns_clause_targett *target : targets)
    {
        for(goto_programt::instructiont inst : target->get_init_block().instructions)
        {
            result.add(goto_programt::instructiont(inst));
        }
    }
    return result;
}

goto_programt& assigns_clauset::temporary_declarations(source_locationt loc, dstringt func_name, dstringt lang_mode)
{
    if(standin_declarations.empty())
    {
        for(assigns_clause_targett *target : targets)
        {
            for(symbol_exprt sym : target->temporary_declarations())
            {
                standin_declarations.add(goto_programt::make_decl(sym, sym.source_location()));
            }
        }
    }
    return standin_declarations;
}

goto_programt assigns_clauset::dead_stmts(source_locationt loc, dstringt func_name, dstringt lang_mode)
{
  goto_programt dead_statements;
  for(assigns_clause_targett *target : targets)
  {
    for(symbol_exprt sym : target->temporary_declarations())
    {
      dead_statements.add(goto_programt::make_dead(sym, sym.source_location()));
    }
  }
  return dead_statements;
}

goto_programt assigns_clauset::havoc_code(source_locationt loc, dstringt func_name, dstringt lang_mode)
{
  goto_programt havoc_statements;
  for(assigns_clause_targett *target : targets)
  {
    for(goto_programt::instructiont ins : target->havoc_code(loc).instructions)
    {
      havoc_statements.add(std::move(ins));
    }
  }
  return havoc_statements;
}

exprt assigns_clauset::alias_expression(const exprt &lhs)
{
    if(targets.empty())
    {
        return false_exprt();
    }

    exprt left_ptr = assigns_clause_targett::pointer_for(lhs);

    bool first_iter = true;
    exprt result = false_exprt();
    for(assigns_clause_targett *target : targets)
    {
        if(first_iter)
        {
            result = target->alias_expression(left_ptr);
            first_iter = false;
        }
        else
        {
            result = or_exprt(result, target->alias_expression(left_ptr));
        }
    }
    return result;
}


exprt assigns_clauset::compatible_expression(const assigns_clauset &called_assigns)
{
    if(called_assigns.targets.empty())
    {
        return true_exprt();
    }

    bool first_clause = true;
    exprt result = true_exprt();
    for(assigns_clause_targett *called_target : called_assigns.targets)
    {
        bool first_iter = true;
        exprt curr_tgt_compat = false_exprt();
        for(assigns_clause_targett *target : targets)
        {
            if(first_iter)
            {
                curr_tgt_compat = target->compatible_expression(*called_target);
                first_iter = false;
            }
            else
            {
                curr_tgt_compat = or_exprt(curr_tgt_compat, target->compatible_expression(*called_target));
            }
        }
        if(first_clause)
        {
            result = curr_tgt_compat;
            first_clause = false;
        }
        else
        {
            result = and_exprt(result, curr_tgt_compat);
        }
    }

    return result;

}