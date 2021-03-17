void assigns_single(int a[], int len);

void assigns_upper_bound(int a[], int len);

void assigns_lower_bound(int a[], int len);

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
