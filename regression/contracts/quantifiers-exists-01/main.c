// duplicate of
// function_check_02

int f1(int *arr)
  __CPROVER_ensures(
    __CPROVER_exists {int i; i >= 0}
  )
{
  for(int i = 0; i < 10; i++)
  {
    arr[i] = i;
  }

  return 0;
}

int main()
{
  int arr[10];
  f1(arr);
}
