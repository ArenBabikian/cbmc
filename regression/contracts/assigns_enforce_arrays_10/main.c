void assigns_in_range(int a[], int last_idx) __CPROVER_assigns(a[2, last_idx])
{
  last_idx++;
  a[last_idx] = 6;
}

int main()
{
  int arr[10];
  assigns_in_range(arr, 9);

  return 0;
}
