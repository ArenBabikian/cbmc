#include <assert.h>

void foo(char c[]) __CPROVER_assigns(c[2, 4])
{
}

int main()
{
  char b[10];
  b[0] = 'a';
  b[1] = 'b';
  b[2] = 'c';
  b[3] = 'd';
  b[4] = 'e';
  b[5] = 'f';
  b[6] = 'g';
  b[7] = 'h';
  b[8] = 'i';
  b[9] = 'j';
  foo(b);
  assert(b[2] == 'c' || b[3] == 'd' || b[4] == 'e');

  return 0;
}
