
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define size 5

void swap(int *a, int *b)
  __CPROVER_assigns(*a, *b);
  // __CPROVER_requires()
  // __CPROVER_ensures();

void swap(int *a, int *b)
{
  *a ^= *b;
  *b ^= *a;
  *a ^= *b;
}

int partition(int arr_ghost[], int arr[], int len)
  __CPROVER_assigns(arr[0, len])
  // __CPROVER_requires(arr_ghost and arr have same content,
  //)
  __CPROVER_requires(
    len >= 0
  )
  // __CPROVER_ensures(arr_ghost and arr have same content,
  //left of pivot is smaller than pivot value, 
  //right of pivot is larger than pivot value);
  __CPROVER_ensures(
    __CPROVER_return_value >= 0 && __CPROVER_return_value < len
    && __CPROVER_forall {
      int i;
      (0 <= i && i < __CPROVER_return_value) ==> 
        arr[i] <= arr[__CPROVER_return_value]
    }
    && __CPROVER_forall {
      int i;
      (__CPROVER_return_value <= i && i < len) ==> 
        arr[i] >= arr[__CPROVER_return_value]
    }
    // // GHOST 
    // && __CPROVER_forall {
    //   int i;
    //   (0 <= i && i < len) ==> __CPROVER_exists
    //   {
    //     int j;
    //     0 <= j &&j < len && arr_ghost[i] == arr[j]
    //   }
    // }
    // // GHOST
    // && __CPROVER_forall {
    //   int i;
    //   (0 <= i && i < len) ==> __CPROVER_exists
    //   {
    //     int j;
    //     0 <= j &&j < len && arr[i] == arr_ghost[j]
    //   }
    // }
  );

void quicksort(int arr_ghost[], int arr[], int len)
  __CPROVER_assigns(arr[0, len])
  // __CPROVER_requires(arr_ghpst and arr have same content
  //)
    __CPROVER_requires(
      len >= 0
      // GHOST
      // && __CPROVER_forall {
      //   int i;
      //   (0 <= i && i < len) ==> arr_ghost[i] == arr[i]
      // }
    )
  // __CPROVER_ensures(arr ghost and arr have same content,
  //any consecutive ints in arr have the right one bigger or requal to left);
    // __CPROVER_ensures(
    //   __CPROVER_forall {
    //     int i; 
    //     (0 <= i && i < len-1) ==> arr[i] <= arr[i+1]
    //   }
    //   // GHOST
    //   && __CPROVER_forall {
    //     int i;
    //     (0 <= i && i < len) ==> __CPROVER_exists
    //     {
    //       int j;
    //       0 <= j &&j < len &&arr_ghost[i] == arr[j]
    //     }
    //   } 
    //   // GHOST
    //   && __CPROVER_forall {
    //     int i;
    //     (0 <= i && i < len) ==> __CPROVER_exists
    //     {
    //       int j;
    //       0 <= j &&j < len && arr[i] == arr_ghost[j]
    //     }
    //   }
    // )
    ;

int partition(int arr_ghost[], int arr[], int len)
{
  int h = len - 1;
  int l = 0;

  int pivot_idx = len / 2;
  int pivot = arr[pivot_idx];

  while(h > l)
    // __CPROVER_loop_invariant(
    //     0 <= l && l <= pivot_idx && pivot_idx <= h && h < len
    //   // && arr[pivot_idx] == pivot
    //   && __CPROVER_forall {int i; (0 <= i && i < l) ==> arr[i] <= pivot}
    //   // && __CPROVER_forall {int i; 1 == 0}
    //   && __CPROVER_forall {int i; (h < i && i < len) ==> pivot <= arr[i]} 
    // )
  {
    if(arr[h] <= pivot && arr[l] >= pivot)
    {
      swap(arr + h, arr + l);
      if(pivot_idx == h)
      {
        pivot_idx = l;
        h--;
      }
      if(pivot_idx == l)
      {
        pivot_idx = h;
        l++;
      }
    }
    else if(arr[h] <= pivot){l++;}
    else {h--;}
  }
  return pivot_idx;
}

void quicksort(int arr_ghost[], int arr[], int len)
{
    if (len <= 1)
    {
        return;
    }
    // int *new_ghost = malloc(len * sizeof(int));
    // memcpy(new_ghost, arr, len * sizeof(int));

    int pi = partition(arr_ghost, arr, len);

    // memcpy(new_ghost, arr, len * sizeof(int));

    // quicksort(new_ghost, arr, pi);
    // quicksort(new_ghost, arr+pi+1, len-pi-1);
    quicksort(arr_ghost, arr, pi);
    quicksort(arr_ghost, arr+pi+1, len-pi-1);

    // free(new_ghost);

}

int main()
{
//   const int len = 5;
  int arr[size] = {1, 2, 3, 0, 4};
  int arr_ghost[size] = {1, 2, 3, 0, 4};
  quicksort(arr_ghost, arr, size);
  // for(int i = 0; i < size; i++){
  //     printf("%d ", arr_ghost[i]);
  // }
}