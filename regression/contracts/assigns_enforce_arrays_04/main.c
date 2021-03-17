void assigns_single(int a[], int len) __CPROVER_assigns(a[8])
{
  a[8] = 20;
}

void assigns_upper_bound(int a[], int len) __CPROVER_assigns(a[2, 5])
{
  a[5] = 10;
}

void assigns_lower_bound(int a[], int len) __CPROVER_assigns(a[2, 5])
{
  a[2] = 10;
}

int main()
{
  int arr[10];
  assigns_upper_bound(arr, 10);
  assigns_lower_bound(arr, 10);
  assigns_single(arr, 10);

  return 0;
}
