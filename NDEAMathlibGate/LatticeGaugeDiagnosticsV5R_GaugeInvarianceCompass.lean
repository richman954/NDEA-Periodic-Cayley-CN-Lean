import Mathlib

open Matrix
open Complex

def MatrixState := Matrix (Fin 2) (Fin 2) ℂ

def matmul2 (A B : MatrixState) : MatrixState :=
  !![ A 0 0 * B 0 0 + A 0 1 * B 1 0, A 0 0 * B 0 1 + A 0 1 * B 1 1;
      A 1 0 * B 0 0 + A 1 1 * B 1 0, A 1 0 * B 0 1 + A 1 1 * B 1 1 ]

def trace2 (A : MatrixState) : ℂ := A 0 0 + A 1 1

def G_matrix : MatrixState := !![1, 1; 0, 1]
def G_inv : MatrixState := !![1, -1; 0, 1]

-- V5R Repair: Proving Trace Invariance of Conjugation
-- Using ring_nf instead of ext because trace2 returns a complex scalar
theorem wilson_trace_conjugation_invariance (W_loop : MatrixState) :
    trace2 (matmul2 (matmul2 G_matrix W_loop) G_inv) = trace2 W_loop := by
  dsimp [trace2, matmul2, G_matrix, G_inv]
  ring_nf
