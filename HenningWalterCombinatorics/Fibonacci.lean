import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Some basic facts about odd-index Fibonacci numbers

-/

namespace Nat

/-- The sequence denoted $G$ in the paper, in OEIS it is A001519 up to index shift. -/
def odd_fib (n : ℕ) : ℕ := fib (2 * n + 1)

@[simp] lemma odd_fib_zero : odd_fib 0 = 1 := rfl
@[simp] lemma odd_fib_one : odd_fib 1 = 2 := rfl
@[simp] lemma odd_fib_two : odd_fib 2 = 5 := rfl

theorem odd_fib_add_two {n : ℕ} :
odd_fib (n + 2) + odd_fib n = 3 * odd_fib (n + 1)  := by
  grind [show fib 3 = 2 by rfl, fib_add_two, odd_fib]

open Finset

lemma antidiagonal_sum_succ (n : ℕ) :
    ∑ ij ∈ antidiagonal (n + 1), odd_fib ij.1 * 2 ^ ij.2
      =
    odd_fib (n + 1) +
      2 * ∑ ij ∈ antidiagonal n, odd_fib ij.1 * 2 ^ ij.2 := by
  rw [Nat.antidiagonal_succ']
  simp [Nat.pow_add_one, ← mul_assoc, mul_comm, Finset.mul_sum]

/-- This is Proposition 9 in the paper. -/
theorem odd_fib_pow_two {n : ℕ} :
odd_fib (n + 2) = 2 ^ (n + 1) + odd_fib (n + 1)
  + ∑ ij ∈ antidiagonal n, odd_fib ij.1 * 2 ^ ij.2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      apply Nat.add_right_cancel
      rw [odd_fib_add_two, antidiagonal_sum_succ, ih]
      ring

end Nat
