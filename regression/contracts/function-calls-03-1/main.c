int f1(int *x1)
  __CPROVER_requires(*x1 > 0 && *x1 < 20)
  __CPROVER_ensures(__CPROVER_return_value == *x1+ 2);

//Note 1: no way to check that the requires clause needs to have "*x2 >= 0" and not "*x2 > 0" due to the recursion
int f2(int *x2)
  __CPROVER_requires(*x2 >= 0 && *x2 < 20)
  __CPROVER_ensures(__CPROVER_return_value == *x2+1);

int f1(int *x1)
{
  return f2(x1) + 1;
}

//Note 2: impossible to "check" f2 by "checking" the outer function and "replacing" the internal recursive call.
int f2(int *x2)
{
  if (*x2 < 1) return -1; //Notice the change for the base case
  int loc2 = *x2-1;
  return f2(&loc2) + 1;
}

int main()
{
  int p ; 
  __CPROVER_assume(p > 0 && p < 20);
  f1(&p);

  return 0;
}