/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/pointer_offset_size.h>
#include <util/byte_operators.h>
#include <util/namespace.h>

#include "flatten_byte_operators.h"

/*******************************************************************\

Function: flatten_byte_extract

  Inputs:

 Outputs:

 Purpose: rewrite byte extraction from an array to byte extraction 
          from a concatenation of array index expressions

\*******************************************************************/

exprt flatten_byte_extract(
  const byte_extract_exprt &src,
  const namespacet &ns)
{
  assert(src.operands().size()==2);

  bool little_endian;
  
  if(src.id()==ID_byte_extract_little_endian)
    little_endian=true;
  else if(src.id()==ID_byte_extract_big_endian)
    little_endian=false;
  else
    assert(false);
  
  mp_integer size_bits=pointer_offset_bits(src.type(), ns);
  if(size_bits<0)
    throw "byte_extract flatting with non-constant size: "+src.pretty();
  std::size_t width_bits=integer2unsigned(size_bits);

  std::size_t width_bytes=width_bits/8+(width_bits%8==0?0:1);
  
  const typet &t=src.op0().type();
  
  if(t.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(t);
    const typet &subtype=array_type.subtype();
    
    // byte-array?
    if((subtype.id()==ID_unsignedbv ||
        subtype.id()==ID_signedbv) &&
       to_bitvector_type(subtype).get_width()==8)
    {
      // get 'width'-many bytes, and concatenate
      exprt::operandst op;
      op.resize(width_bytes);
      
      for(std::size_t i=0; i<width_bytes; i++)
      {
        // the most significant byte comes first in the concatenation!
        std::size_t offset_i=
          little_endian?(width_bytes-i-1):i;
        
        plus_exprt offset(from_integer(offset_i, src.op1().type()), src.op1());
        index_exprt index_expr(subtype);
        index_expr.array()=src.op0();
        index_expr.index()=offset;
        op[i]=index_expr;
      }
      
      if(width_bytes==1)
        return op[0];
      else // width_bytes>=2
      {
        concatenation_exprt concatenation(src.type());
        concatenation.operands().swap(op);
        return concatenation;
      }
    }
    else // non-byte array
    {
      const exprt &root=src.op0();
      const exprt &offset=src.op1();
      const typet &array_type=ns.follow(root.type());
      const typet &offset_type=ns.follow(offset.type());
      const typet &element_type=ns.follow(array_type.subtype());
      mp_integer element_width=pointer_offset_size(element_type, ns);
      
      if(element_width==-1) // failed
        throw "failed to flatten non-byte array with unknown element width";

      mp_integer result_width=pointer_offset_size(src.type(), ns);
      mp_integer num_elements=(element_width+result_width-2)/element_width+1;

      // compute new root and offset
      concatenation_exprt concat(
        unsignedbv_typet(integer2unsigned(element_width*8*num_elements)));

      exprt first_index=
        (element_width==1)?offset 
        : div_exprt(offset, from_integer(element_width, offset_type)); // 8*offset/el_w

      for(mp_integer i=num_elements; i>0; --i)
      {
        plus_exprt index(first_index, from_integer(i-1, offset_type));
        concat.copy_to_operands(index_exprt(root, index));
      }

      // the new offset is width%offset
      exprt new_offset;
      
      if(element_width==1)
        new_offset=from_integer(0, offset_type);
      else
        new_offset=mod_exprt(offset, from_integer(element_width, offset_type));

      // build new byte-extract expression
      exprt tmp(src.id(), src.type());
      tmp.copy_to_operands(concat, new_offset);

      return tmp;
    }
  }
  else // non-array
  {
    mp_integer op0_bits=pointer_offset_bits(src.op0().type(), ns);
    if(op0_bits<0)
      throw "byte_extract flatting of non-constant source size: "+src.pretty();

    // We turn that into logical right shift and extractbits
    
    const exprt &offset=src.op1();
    const typet &offset_type=ns.follow(offset.type());
    
    // adjust for endianness
    exprt adjusted_offset;
    
    if(little_endian)
      adjusted_offset=offset;
    else
    {
      exprt width_constant=from_integer(op0_bits/8-1, offset_type);
      adjusted_offset=minus_exprt(width_constant, offset);
    }

    mult_exprt times_eight(adjusted_offset, from_integer(8, offset_type));

    // cast to generic bit-vector
    std::size_t op0_width=integer2unsigned(op0_bits);
    typecast_exprt src_op0_tc(src.op0(), bv_typet(op0_width));
    lshr_exprt left_shift(src_op0_tc, times_eight);

    extractbits_exprt extractbits;
    
    extractbits.src()=left_shift;
    extractbits.type()=src.type();
    extractbits.upper()=from_integer(width_bits-1, offset_type);
    extractbits.lower()=from_integer(0, offset_type);
      
    return extractbits;
  }
}

/*******************************************************************\

Function: flatten_byte_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt flatten_byte_update(
  const byte_update_exprt &src,
  const namespacet &ns)
{
  assert(src.operands().size()==3);

  mp_integer element_size=
    pointer_offset_size(src.op2().type(), ns);
  
  const typet &t=ns.follow(src.op0().type());
  
  if(t.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(t);
    const typet &subtype=array_type.subtype();
    
    // array of bitvectors?
    if(subtype.id()==ID_unsignedbv ||
       subtype.id()==ID_signedbv ||
       subtype.id()==ID_floatbv)
    {
      mp_integer sub_size=pointer_offset_size(subtype, ns);
      
      if(sub_size==-1)
        throw "can't flatten byte_update for sub-type without size";

      // byte array?
      if(sub_size==1)
      {
        // apply 'array-update-with' element_size times
        exprt result=src.op0();
        
        for(mp_integer i=0; i<element_size; ++i)
        {
          exprt i_expr=from_integer(i, ns.follow(src.op1().type()));

          exprt new_value;
          
          if(i==0 && element_size==1) // bytes?
          {
            new_value=src.op2();
            if(new_value.type()!=subtype)
              new_value.make_typecast(subtype);
          }
          else
          {
            byte_extract_exprt byte_extract_expr(
              src.id()==ID_byte_update_little_endian?ID_byte_extract_little_endian:
              src.id()==ID_byte_update_big_endian?ID_byte_extract_big_endian:
              throw "unexpected src.id() in flatten_byte_update",
              subtype);
            
            byte_extract_expr.copy_to_operands(src.op2(), i_expr);
            new_value=flatten_byte_extract(byte_extract_expr, ns);
          }

          exprt where=plus_exprt(src.op1(), i_expr);
            
          with_exprt with_expr;
          with_expr.type()=src.type();
          with_expr.old()=result;
          with_expr.where()=where;
          with_expr.new_value()=new_value;
          
          result.swap(with_expr);
        }
        
        return result;
      }
      else // sub_size!=1
      {
        if(element_size==1) // byte-granularity update
        {
          div_exprt div_offset(src.op1(), from_integer(sub_size, src.op1().type()));
          mod_exprt mod_offset(src.op1(), from_integer(sub_size, src.op1().type()));
        
          index_exprt index_expr(src.op0(), div_offset, array_type.subtype());
          
          byte_update_exprt byte_update_expr(src.id(), array_type.subtype());
          byte_update_expr.copy_to_operands(index_expr, mod_offset, src.op2());

          // Call recurisvely, the array is gone!            
          exprt flattened_byte_update_expr=
            flatten_byte_update(byte_update_expr, ns);
            
          with_exprt with_expr(
            src.op0(), div_offset, flattened_byte_update_expr);
            
          return with_expr;
        }
        else
          throw "flatten_byte_update can only do byte updates of non-byte arrays right now";
      }
    }
    else
    {
      throw "flatten_byte_update can only do arrays of scalars right now";
    }
  }
  else if(t.id()==ID_signedbv ||
          t.id()==ID_unsignedbv ||
          t.id()==ID_floatbv)
  {
    // do a shift, mask and OR
    std::size_t width=to_bitvector_type(t).get_width();
    
    if(element_size*8>width)
      throw "flatten_byte_update to update element that is too large";
    
    // build mask
    exprt mask=
      bitnot_exprt(
        from_integer(power(2, element_size*8)-1, unsignedbv_typet(width)));
      
    const typet &offset_type=ns.follow(src.op1().type());
    mult_exprt offset_times_eight(src.op1(), from_integer(8, offset_type));
    
    // shift the mask
    shl_exprt shl_expr(mask, offset_times_eight);

    // do the 'AND'
    bitand_exprt bitand_expr(src.op0(), mask);

    // zero-extend the value
    concatenation_exprt value_extended(
      from_integer(0, unsignedbv_typet(width-integer2unsigned(element_size)*8)), 
      src.op2(), t);
    
    // shift the value
    shl_exprt value_shifted(value_extended, offset_times_eight);
    
    // do the 'OR'
    bitor_exprt bitor_expr(bitand_expr, value_shifted);
    
    return bitor_expr;
  }
  else
  {
    throw "flatten_byte_update can only do array and scalars right now";
  }
}

/*******************************************************************\

Function: has_byte_operators

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_byte_operator(const exprt &src)
{
  if(src.id()==ID_byte_update_little_endian ||
     src.id()==ID_byte_update_big_endian ||
     src.id()==ID_byte_extract_little_endian ||
     src.id()==ID_byte_extract_big_endian)
    return true;
  
  forall_operands(it, src)
    if(has_byte_operator(*it)) return true;
  
  return false;
}

/*******************************************************************\

Function: flatten_byte_operators

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt flatten_byte_operators(const exprt &src, const namespacet &ns)
{
  exprt tmp=src;
  
  // destroys any sharing, should use hash table
  Forall_operands(it, tmp)
  {
    exprt tmp=flatten_byte_operators(*it, ns);
    it->swap(tmp);
  }

  if(src.id()==ID_byte_update_little_endian ||
     src.id()==ID_byte_update_big_endian)
    return flatten_byte_update(to_byte_update_expr(tmp), ns);
  else if(src.id()==ID_byte_extract_little_endian ||
          src.id()==ID_byte_extract_big_endian)
    return flatten_byte_extract(to_byte_extract_expr(tmp), ns);
  else
    return tmp;
}
