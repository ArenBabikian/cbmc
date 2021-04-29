int foo(int *x) __CPROVER_assigns(*x)
  __CPROVER_ensures(__CPROVER_return_value == *x + 5)
{
  int y = bar(5);
  return *x + 5;
}

// if I remove the assigns clause for "bar", it will add an "ASSERT FALSE"
// in the goto program, and will fail automatically

//POTENTIAL SOLUTION
// we implement an empty assigns clause which adds an "ASSERT TRUE"
// in the goto function instead of an "ASSERT FALSE"
int bar(int a) __CPROVER_assigns(-1)
  __CPROVER_ensures(__CPROVER_return_value == 5)
{
  return 5;
}

int main()
{
  int n;
  n = foo(&n);

  return 0;
}
