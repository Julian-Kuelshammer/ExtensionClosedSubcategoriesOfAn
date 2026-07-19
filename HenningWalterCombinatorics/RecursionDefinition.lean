import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Interval.Finset.Nat

/-! # Definition of the recursive functions.

This file corresponds to Section 1.2 in the paper. It provides the recursive definitions of
`a`, `b`, `A` and `B`.

These are as follows:
For the sequence `a` the recursive definition is:
`a 0 0 = 1`
`a 0 1 = 1`
`a 0 (k + 2) = 1` for all `k : ℕ`

`a (n + 1) 0 = ∑ i ∈ Finset.Icc 0 (n + 1), a n i`
`a (n + 1) (k + 1) = a n k + ∑ q ∈ Finset.Icc k (n + 1), b n q + ∑ m ∈ (Finset.Icc 1 n),`
  `∑ r ∈ Finset.Icc 0 (min m k), a (m - 1) r * ∑ q ∈ Finset.Icc (k - r) (n - m + 1), b (n - m) q) +`
  `b n (k + 1) + ∑ m ∈ (Finset.Icc 1 n), b (m - 1) (k + 1) * `
  `∑ i ∈ Finset.Icc 0 (n - m + 1), a (n - m) i.`

For the sequence `b` the recursive definition is:
`b 0 0 = 0`
`b 0 1 = 1`
`b 0 (k + 2) = 0` for all `k : ℕ`

`b (n + 1) 0 = 0`
`b (n + 1) (k + 1) = a n k + ∑ q ∈ Finset.Icc k (n + 1), b n q + ∑ m ∈ (Finset.Icc 1 n),`
  `∑ r ∈ Finset.Icc 0 (min m k), a (m - 1) r * `
  `∑ q ∈ Finset.Icc (k - r) (n - m + 1), b (n - m) q)`

## Implementation details

The main structure of this file with the definition of `ab`, `a` and `b` was done by Aristotle in
two steps. In Aristotle's first attempt there was an additional if-clause that was never triggered
in order to avoid having to prove the decreasing property. The purpose of the `Finset.attach` is
precisely to make proving the decreasing property possible. For a mathematician it can safely be
ignored and `m.1` can then be read as `m`.

Minor tweaks were done by the author for speed-up.
-/

namespace RecursiveArrays

/--
The "rows" of `a` and `b`, constructed simultaneously. What we define here is the function `ab  '
which is given by `r(n)=(a(n,-), b(n,-))`. The expression `Finset.Icc l m` denotes the interval
(within the natural numbers `l` and `m`.)
-/
def ab : ℕ → (ℕ → ℕ) × (ℕ → ℕ)
  | 0 =>
      (fun | 0 => 1 | 1 => 1 | _ + 2 => 0,
       fun | 0 => 0 | 1 => 1 | _ + 2 => 0)
  | n + 1 =>
      ((fun
        | 0 => ∑ i ∈ Finset.Icc 0 (n + 1), (ab   n).1 i
        | k + 1 =>
          ((ab n).1 k + ∑ q ∈ Finset.Icc k (n + 1), (ab n).2 q +
            ∑ m ∈ (Finset.Icc 1 n).attach, ∑ r ∈ Finset.Icc 0 (min m.1 k),
              (ab (m.1 - 1)).1 r * ∑ q ∈ Finset.Icc (k - r) (n - m.1 + 1), (ab (n - m.1)).2 q) +
              (ab n).2 (k + 1) + ∑ m ∈ (Finset.Icc 1 n).attach, (ab (m.1 - 1)).2 (k + 1) *
                  ∑ i ∈ Finset.Icc 0 (n - m.1 + 1), (ab (n - m.1)).1 i),
       (fun
        | 0 => 0
        | k + 1 =>
          (ab n).1 k + ∑ q ∈ Finset.Icc k (n + 1), (ab n).2 q +
            ∑ m ∈ (Finset.Icc 1 n).attach, ∑ r ∈ Finset.Icc 0 (min m.1 k),
              (ab (m.1 - 1)).1 r * ∑ q ∈ Finset.Icc (k - r) (n - m.1 + 1), (ab (n - m.1)).2 q))
termination_by n => n
decreasing_by
  all_goals simp only [Nat.succ_eq_add_one, lt_add_iff_pos_right, Order.lt_one_iff]
  all_goals (have := Finset.mem_Icc.mp m.2; omega)

/-- The sequence `a` specified by the recursion. -/
def a (n k : ℕ) : ℕ := (ab n).1 k
/-- The sequence `b` specified by the recursion. -/
def b (n k : ℕ) : ℕ := (ab n).2 k

/-- The sequence `A` so that `A n` counts the number of extension-closed subcategories of the
linearly oriented type A quiver with `n + 1` vertices. -/
def A (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 2), a n k

/-- The sequence `B` so that `B n` counts the number of extension-closed subcategories of the
linearly oriented type A quiver with `n + 1` vertices containing the unique indecomposable
projective-injective module. -/
def B (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 2), b n k

/- The following sequence of lemmas prove that the sequences `a` and `b` satisfy the claimed
recursions. These are essentially true by definition. -/

@[simp] lemma a_zero_zero : a 0 0 = 1 := by simp [a, ab]

@[simp] lemma a_zero_one : a 0 1 = 1 := by simp [a, ab]

@[simp] lemma a_zero_add_two (k : ℕ) : a 0 (k + 2) = 0 := by
  simp [a, ab]

lemma a_succ_zero (n : ℕ) :
    a (n + 1) 0 = ∑ i ∈ Finset.Icc 0 (n + 1), a n i := by
  simp [a, ab]

lemma a_succ_succ (n k : ℕ) :
    a (n + 1) (k + 1) = b (n + 1) (k + 1) + b n (k + 1) +
      ∑ m ∈ Finset.Icc 1 n, b (m - 1) (k + 1) * ∑ i ∈ Finset.Icc 0 (n - m + 1), a (n - m) i := by
  simpa [a, b, ab] using
    (Finset.sum_attach _ (f := fun m =>
        (ab (↑m - 1)).2 (k + 1) * ∑ i ∈ Finset.Icc 0 (n - ↑m + 1), (ab (n - ↑m)).1 i))

@[simp] lemma b_self_zero (n : ℕ) : b n 0 = 0 := by
  cases n <;>
  simp [b, ab]

@[simp] lemma b_zero_one : b 0 1 = 1 := by simp [b, ab]

@[simp] lemma b_zero_add_two (k : ℕ) : b 0 (k + 2) = 0 := by
  simp [b, ab]

lemma b_succ_succ (n k : ℕ) :
    b (n + 1) (k + 1) = a n k + ∑ q ∈ Finset.Icc k (n + 1), b n q +
      ∑ m ∈ Finset.Icc 1 n, ∑ r ∈ Finset.Icc 0 (min m k), a (m - 1) r *
      ∑ q ∈ Finset.Icc (k - r) (n - m + 1), b (n - m) q := by
  simpa [a, b, ab] using Finset.sum_attach _
    (fun x => ∑ r ∈ Finset.Icc 0 (min x k),
      (ab (x - 1)).1 r * ∑ q ∈ Finset.Icc (k - r) (n - x + 1), (ab (n - x)).2 q)

lemma ab_triangular_shape (n : ℕ) :
∀ k, n + 2 ≤ k → a n k = 0 ∧ b n k = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k hk
  rcases n with ( _ | n ) <;> rcases k with ( _ | k ) <;> all_goals try simp; omega
  · cases k <;> simp; omega
  · have caseb : b (n + 1) (k + 1) = 0 := by
      rw [b_succ_succ, (ih n (by omega) k (by omega)).1, zero_add, Finset.sum_eq_zero]
      · rw [zero_add, Finset.sum_eq_zero]
        intro m _
        rw [Finset.sum_eq_zero]
        intro r _
        apply mul_eq_zero_of_right
        rw [Finset.sum_eq_zero]
        intro q _
        grind
      intro m _
      grind
    refine ⟨?_, caseb⟩
    · rw [a_succ_succ, caseb, zero_add, (ih n (by omega) (k + 1) (by omega)).2, zero_add,
        Finset.sum_eq_zero]
      intro m _
      apply mul_eq_zero_of_left
      grind

lemma a_triangular_shape (n k : ℕ) (hk : n + 2 ≤ k) : a n k = 0 := by
  exact (ab_triangular_shape n k hk).1

lemma b_triangular_shape (n k : ℕ) (hk : n + 2 ≤ k) : b n k = 0 := by
  exact (ab_triangular_shape n k hk).2

/- Here are the first 7 values of A(n)=a(n+1,0). Note that eval doesn't come with the same
correctness insurances as the proofs above. More values are possible, but it is not an efficient
implementation, so it will take some time to spit out the result. -/
#eval a 0 0
#eval a 1 0
#eval a 2 0
#eval a 3 0
#eval a 4 0
#eval a 5 0
#eval a 6 0
#eval a 7 0

/- It is also possible to prove these, see below, but this takes a bit longer. -/

example : a 1 0 = 2 := by
  simp [a_succ_zero, Finset.sum_Icc_succ_top]

example : a 2 0 = 7 := by
  simp [a_succ_zero, Finset.sum_Icc_succ_top, a_succ_succ, b_succ_succ]

example : a 3 0 = 34 := by
  simp [a_succ_zero, Finset.sum_Icc_succ_top, a_succ_succ, b_succ_succ]

example : a 4 0 = 199 := by
  simp [a_succ_zero, Finset.sum_Icc_succ_top, a_succ_succ, b_succ_succ]

example : a 5 0 = 1308 := by
  simp [a_succ_zero, Finset.sum_Icc_succ_top, a_succ_succ, b_succ_succ]

end RecursiveArrays
