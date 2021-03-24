#include <assert.h>

#define N 8

void main()
{
  int a[N];
  for(int i = 0; i < N; ++i)
    // clang-format off
    __CPROVER_loop_invariant(
      (0 <= i) && (i <= N) &&
      __CPROVER_forall {
        int k;
        (0 <= k && k < i) ==> a[k] == 1
      }
    )
    // clang-format on
    {
      a[i] = 1;
    }

  // clang-format off
  assert(__CPROVER_forall {
    int k;
    (0 <= k && k < N) ==> a[k] == 1
  });
  // clang-format on
}
