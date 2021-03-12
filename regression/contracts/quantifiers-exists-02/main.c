// duplicate of
// function_check_02

int f1(int *arr)
  __CPROVER_ensures(
    __CPROVER_exists {int i; (0 <= i && i < 10) ==> arr[i] == 1}
  )
{
  for(int i = 0; i < 10; i++)
  {
    arr[i] = 0;
  }

  return 0;
}

int main()
{
  int arr[10];
  f1(arr);
}
