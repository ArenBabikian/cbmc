#include <assert.h>

void main()
{
  int N = 64, a[64];
  for(int i = 0; i < N; ++i)
    // clang-format off
    __CPROVER_loop_invariant((0 <= i) && (i <= N) && __CPROVER_forall {
      int k;
      (0 <= k && k < N) ==> 1 == 1
    })
    // clang-format on
    {
      a[i] = 1;
    }
}