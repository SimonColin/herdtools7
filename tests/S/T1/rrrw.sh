#! /bin/bash

cat > RRRW/rrrw$1$2$3$4.litmus <<-EOF
C rrrw$1$2$3$4

{atomic_int x0 = 0;
atomic_int x1 = 0}

P0 (atomic_int* y,atomic_int* x, atomic_int* x0) {
  int r0 = atomic_compare_exchange_strong_explicit(x,x0,2,memory_order_$1, memory_order_$2);
  int r1 = atomic_load_explicit(y,memory_order_relaxed);
}

P1 (atomic_int* y,atomic_int* x, atomic_int* y0) {
  int r0 = atomic_compare_exchange_strong_explicit(y,y0,1,memory_order_$3, memory_order_$4);
  atomic_store_explicit(x,1,memory_order_relaxed);
}

exists
(x=2 /\ 0:r0=1 /\ 0:r1=0 /\ 1:r0=0)

EOF
