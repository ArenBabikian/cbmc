void assigns_single(int a[], int len) __CPROVER_assigns(a[7])
{
}

void assigns_range(int a[], int len) __CPROVER_assigns(a[2, 5])
{
}

void assigns_big_range(int a[], int len) __CPROVER_assigns(a[2, 7])
{
  assigns_single(a, len);
  assigns_range(a, len);
}

int main()
{
  int arr[10];
  assigns_big_range(arr, 10);

  return 0;
}
