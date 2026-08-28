import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.SuccPred

/-!
# Bracketing functions

Bracketing functions `a : Fin n → Fin n` provide an elementary description of the Tamari lattice.
They correspond to the more classical encodings of binary trees as follows: Labelling the vertices
of the binary tree with the in-order traversal, i.e. recursively numbering first the left tree, then
the root, and finally the right tree, `a i` is the largest label occurring in the subtree rooted at
`i`. The partial order is then just given by componentwise comparison. This partial order is in fact
a lattice with meet given componentwise, but join given as the least bracketing function above the
pointwise maximum.

As an example, for `n = 3` one obtains the following Hasse diagram:

```
              ![2,2,2]
             /        \
            /          \
    ![0,2,2]         ![2,1,2]
            \           |
             \          |
              \       ![1,1,2]
               \       /
                \     /
                ![0,1,2]
```

## Main definitions

* `Function.IsBracketing`: A predicate on functions `a : Fin n → Fin n` to satisfy the property of
being a bracketing function, i.e. `i ≤ a i` and `i ≤ j ≤ a i → a j ≤ a i`.
* `bracketingSequences n`: The `Finset` of all bracketing sequences `Fin n → Fin n`.

## Main results

* `bracketingSequences_card`: The number of bracketing sequences of length `n` is given by the `n`th
Catalan numbers.

## Implementation details

In the literature, bracketing functions have been defined as functions `Icc 1 n → Icc 1 n`. As is
customary, we have shifted our sequences to instead go `Fin n → Fin n`.

## Literature

* Huang, Samuel and Tamari, Dov: Problems of Associativity: A Simple Proof for the Lattice Property
of Systems Ordered by a Semi-associative Law, Journal of Combinatorial Theory (A) 13, 7--13 (1972)

-/

/-- A function `a : Fin n → Fin n` is bracketing if `i ≤ a i` for all `i` and for all `i` and `j`
such that `i ≤ j ≤ a i` one has `a j ≤ a i`. -/
def Function.IsBracketing {n : ℕ} (a : Fin n → Fin n) : Prop :=
  (∀ i, i.val ≤ a i) ∧ (∀ i j, i ≤ j → j.val ≤ a i → a j ≤ a i)
deriving Decidable

open Function

lemma isBracketing_final {n : ℕ} {a : Fin (n + 1) → Fin (n + 1)} (hB : a.IsBracketing) :
  a ⟨n, lt_add_one n⟩ = n := by grind [hB.1 ⟨n, lt_add_one n⟩]

lemma isBracketing_exists_final {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : a.IsBracketing) :
  ∃ k : ℕ, ∃hk : k < n + 1, (a ⟨k, hk⟩) = n := ⟨n, lt_add_one n, isBracketing_final hB⟩

lemma isBracketing_id {n : ℕ} : (id : Fin n → Fin n).IsBracketing :=
  ⟨fun _ ↦ le_rfl, fun _ _ _ hji ↦ hji⟩

lemma isBracketing_const_last {n : ℕ} : (Function.const _ ⟨n, lt_add_one n⟩).IsBracketing :=
  ⟨fun i ↦ i.is_le, fun _ _ _ _ ↦ Fin.ge_of_eq rfl⟩

lemma isFixedPt_of_bracketing {n : ℕ} {a : Fin n → Fin n} (hB : a.IsBracketing) (i : Fin n) :
Function.IsFixedPt a (a i) := le_antisymm (hB.2 i (a i) (hB.1 i) (le_refl (a i))) (hB.1 (a i))

lemma idempotent_of_bracketing {n : ℕ} {a : Fin n → Fin n} (hB : a.IsBracketing) :
a ∘ a = a := by
  funext i
  simpa only [Function.comp_apply, Function.IsFixedPt] using isFixedPt_of_bracketing hB i

/-- The `Finset` of bracketing functions `Fin n → Fin n`. -/
def bracketingSequences (n : ℕ) : Finset (Fin n → Fin n) :=
Finset.univ.filter (IsBracketing)

lemma mem_bracketingSequences {n : ℕ} (a : Fin n → Fin n) :
a ∈ bracketingSequences n ↔ (∀ i, i.val ≤ a i) ∧
(∀ i j, i ≤ j → j.val ≤ a i → a j ≤ a i) := by simp [bracketingSequences, IsBracketing]

/-- Given two bracketing functions `a : Fin k → Fin k` and `b : Fin l → Fin l`, constructs a
bracketing function on `Fin (k + 1 + l)` with first `k` values given by `a`, middle value being
`k + l` and last `l` values given by `b` shifted by `k + 1`. -/
def bracketJoin {k l : ℕ} (b : Fin k → Fin k) (c : Fin l → Fin l) :
    Fin (k + 1 + l) → Fin (k + 1 + l) :=
  Fin.addCases
    (Fin.addCases
      (fun i => (b i).castLE (by omega))
      (fun _ => ⟨k + l, by omega⟩))
    (fun i => ((c i).addNat (k + 1)).cast (by omega))

/-- On the first block of indices, `bracketJoin b c` is given by `b`. -/
@[simp] lemma bracketJoin_val_of_lt {k l : ℕ} (b : Fin k → Fin k) (c : Fin l → Fin l) {v : ℕ}
(h : v < k) : (bracketJoin b c ⟨v, by omega⟩).val = (b ⟨v, h⟩).val := by
  have he : ⟨v, by omega⟩ = ((⟨v, h⟩ : Fin k).castAdd 1).castAdd l := Fin.ext (by simp)
  grind [bracketJoin]

/-- At the separating index `k`, `bracketJoin b c` takes the maximal value `k + l`. -/
@[simp] lemma bracketJoin_val_mid {k l : ℕ} (b : Fin k → Fin k) (c : Fin l → Fin l) :
    (bracketJoin b c ⟨k, by omega⟩).val = k + l := by
  have he : ⟨k, by omega⟩ = ((0 : Fin 1).natAdd k).castAdd l := Fin.ext (by simp)
  grind [bracketJoin]

/-- On the second block of indices, `bracketJoin b c` is `c` shifted by `k + 1`. -/
@[simp] lemma bracketJoin_val_of_gt {k l : ℕ} (b : Fin k → Fin k) (c : Fin l → Fin l) {t : ℕ}
(ht : t < l) : (bracketJoin b c ⟨k + 1 + t, by omega⟩).val = (c ⟨t, ht⟩).val + (k + 1) := by
  have he : ⟨k + 1 + t, by omega⟩ = (⟨t, ht⟩ : Fin l).natAdd (k + 1) := Fin.ext (by simp)
  grind [bracketJoin]

lemma bracketJoin_mem {k l : ℕ} {b : Fin k → Fin k} {c : Fin l → Fin l} (hb : IsBracketing b)
(hc : IsBracketing c) : IsBracketing (bracketJoin b c) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases lt_trichotomy i k with h | rfl | h
    · simpa [bracketJoin_val_of_lt b c h] using hb.1 ⟨i, h⟩
    · simp [bracketJoin_val_mid b c]
    · obtain ⟨t, rfl⟩ : ∃ t, i = k + 1 + t := ⟨i - (k + 1), by omega⟩
      grind [bracketJoin_val_of_gt, hc.1 ⟨t, by omega⟩]
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij hjbc
    simp only [Fin.le_def] at hij ⊢
    rcases lt_trichotomy i k with h | rfl | h
    · -- both indices lie in the first block, where `bracketJoin b c` is `b`
      rw [bracketJoin_val_of_lt b c h] at hjbc ⊢
      have h' := hb.2 ⟨i, h⟩ ⟨j, lt_of_le_of_lt hjbc (b ⟨i, h⟩).is_lt⟩ (by omega) hjbc
      grind [bracketJoin_val_of_lt]
    · -- `i` is the separating index, whose value is maximal
      grind [bracketJoin_val_mid]
    · -- both indices lie in the second block, where `bracketJoin a b` is a shift of `b`
      obtain ⟨s, rfl⟩ : ∃ s, i = k + 1 + s := ⟨i - (k + 1), by omega⟩
      have hs : s < l := by omega
      obtain ⟨t, rfl⟩ : ∃ t, j = k + 1 + t := ⟨j - (k + 1), by omega⟩
      have ht : t < l := by omega
      rw [bracketJoin_val_of_gt b c hs] at hjbc
      have := hc.2 ⟨s, hs⟩ ⟨t, ht⟩ (Fin.mk_le_mk.mpr (by omega)) (by grind)
      grind [bracketJoin_val_of_gt]

def bracketLeft {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : a.IsBracketing) :
let k := Nat.find (isBracketing_exists_final a hB); Fin k → Fin k :=
fun ⟨i, hi⟩ ↦ ⟨a ⟨i, by grind⟩, by
  set k := Nat.find (isBracketing_exists_final a hB) with hk
  by_contra hik
  have hB2 := hB.2 ⟨i, by grind⟩ ⟨k, by grind⟩ (le_of_lt hi) (Nat.le_of_not_lt hik)
  obtain ⟨_, hspeck⟩ := Nat.find_spec (isBracketing_exists_final a hB)
  have hpi : (a ⟨i, by grind⟩).val = n := by grind
  have := Nat.find_min' (isBracketing_exists_final a hB) ⟨by omega, hpi⟩
  omega⟩

lemma bracketLeftIsBracketing {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : a.IsBracketing) :
(IsBracketing (bracketLeft a hB)) := by
  constructor
  · intro ⟨i, hi⟩
    exact hB.1 ⟨i, by grind⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij hja
    exact hB.2 ⟨i, by grind⟩ ⟨j, by grind⟩ hij hja

def bracketRight {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : a.IsBracketing) :
let k := Nat.find (isBracketing_exists_final a hB); Fin (n - k) → Fin (n - k) :=
fun ⟨i, hi⟩ ↦ ⟨a ⟨i + 1 + Nat.find (isBracketing_exists_final a hB), by grind⟩
  - (Nat.find (isBracketing_exists_final a hB) + 1), by omega⟩

lemma bracketRightIsBracketing {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : a.IsBracketing) :
(IsBracketing (bracketRight a hB)) := by
  constructor
  · set k := Nat.find (isBracketing_exists_final a hB) with hk
    intro ⟨i, hi⟩
    simp [bracketRight]
    grind [hB.1 ⟨i + 1 + Nat.find (isBracketing_exists_final a hB), by omega⟩]
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij hja
    have := hB.1 ⟨i + 1 + Nat.find (isBracketing_exists_final a hB), by omega⟩
    have := hB.2 ⟨i + 1 + Nat.find (isBracketing_exists_final a hB), by omega⟩
      ⟨j + 1 + Nat.find (isBracketing_exists_final a hB), by omega⟩ (by grind)
      (by grind [bracketRight])
    grind [bracketRight]

lemma bracket_pair_heq {n K L : ℕ} (hKL : K = L)
    {b' : Fin K → Fin K} {c' : Fin (n - K) → Fin (n - K)}
    {b : Fin L → Fin L} {c : Fin (n - L) → Fin (n - L)}
    {h1 : (b', c') ∈ bracketingSequences K ×ˢ bracketingSequences (n - K)}
    {h2 : (b, c) ∈ bracketingSequences L ×ˢ bracketingSequences (n - L)}
    (hbb : ∀ (i : Fin K) (j : Fin L), i.val = j.val → (b' i).val = (b j).val)
    (hcc : ∀ (i : Fin (n - K)) (j : Fin (n - L)), i.val = j.val → (c' i).val = (c j).val) :
    HEq (⟨(b', c'), h1⟩ : ↥(bracketingSequences K ×ˢ bracketingSequences (n - K)))
      (⟨(b, c), h2⟩ : ↥(bracketingSequences L ×ˢ bracketingSequences (n - L))) := by
  subst hKL
  apply heq_of_eq
  apply Subtype.ext
  have hbe : b' = b := funext fun i => Fin.ext (hbb i i rfl)
  have hce : c' = c := funext fun i => Fin.ext (hcc i i rfl)
  simp [hbe, hce]

def bracketingSequences_succ (n : ℕ) :
bracketingSequences (n + 1) ≃ Σ k : Fin (n + 1),
bracketingSequences k ×ˢ bracketingSequences (n - k) :=
{ toFun := fun ⟨a, ha⟩ ↦ ⟨⟨Nat.find (isBracketing_exists_final a ((Finset.mem_filter.mp ha).2)),
    by grind⟩,
    ⟨(bracketLeft a ((Finset.mem_filter.mp ha).2), bracketRight a ((Finset.mem_filter.mp ha).2)),
    Finset.mem_product.mpr
    ⟨by simp only [mem_bracketingSequences];
        exact bracketLeftIsBracketing a ((Finset.mem_filter.mp ha).2),
     by simp only [mem_bracketingSequences];
        exact bracketRightIsBracketing a ((Finset.mem_filter.mp ha).2)⟩⟩⟩
  invFun := fun ⟨k, ⟨⟨b, c⟩, hbc⟩⟩ ↦
    have h : (k + 1 + (n - k)) = n + 1 := by omega
    have hb : b ∈ bracketingSequences k := by
      simpa [bracketingSequences] using (Finset.mem_product.mp hbc).1
    have hc : c ∈ bracketingSequences _ := by
      simpa [bracketingSequences] using (Finset.mem_product.mp hbc).2
    have hj : bracketJoin b c ∈ bracketingSequences (k.val + 1 + (n - k.val)) := by
      simp only [mem_bracketingSequences]
      exact bracketJoin_mem ((Finset.mem_filter.mp hb).2) ((Finset.mem_filter.mp hc).2)
    ⟨fun i => Fin.cast h (bracketJoin b c (Fin.cast h.symm i)), by
      simp only [mem_bracketingSequences]
      have hjB : IsBracketing (bracketJoin b c) := (Finset.mem_filter.mp hj).2
      constructor
      · intro i
        have hle := hjB.1 (Fin.cast h.symm i)
        simpa using hle
      · intro i j hij hja
        have hij' : Fin.cast h.symm i ≤ Fin.cast h.symm j := by
          rw [Fin.le_def] at hij ⊢
          exact hij
        have hja' :
          (Fin.cast h.symm j : Fin (k + 1 + (n - k))).val
          ≤ (bracketJoin b c (Fin.cast h.symm i)).val := by
            exact hja
        rw [Fin.le_def]
        exact hjB.2 (Fin.cast h.symm i) (Fin.cast h.symm j) hij' hja'⟩
  left_inv := by
    intro ⟨a, ha⟩
    have hB := (Finset.mem_filter.mp ha).2
    ext ⟨i, hi⟩
    set k := (Nat.find (isBracketing_exists_final a hB))
    rcases Nat.lt_trichotomy i k with h | rfl | h
    · grind [bracketJoin_val_of_lt _ _ h, bracketLeft, Fin.cast_mk]
    · simp only [Fin.cast_mk, Fin.val_cast]
      rw [bracketJoin_val_mid]
      grind
    · have hi' : (⟨i, hi⟩ : Fin (n + 1)) = Fin.cast (by omega) (⟨k + 1 + (i - (k + 1)), by omega⟩ :
                Fin (k + 1 + (n - k))) := by grind
      simp only [hi', Fin.cast_mk, Fin.val_cast]
      rw [bracketJoin_val_of_gt _ _ (by omega)]
      grind [bracketRight, hB.1 ⟨i - (k + 1) + 1 + k, by omega⟩]
  right_inv := by
    intro ⟨k,⟨b,c⟩,hbc⟩
    simp only [Sigma.mk.injEq, Order.lt_add_one_iff]
    constructor
    · apply le_antisymm
      · apply Nat.find_min'
        constructor
        · change bracketJoin b c ⟨k, by omega⟩ = n
          rw [bracketJoin_val_mid]
          omega
        · exact Fin.is_le k
      · refine (Nat.le_find_iff _ _).mpr ?_
        intro m hmk ⟨hmn, hval⟩
        change (bracketJoin b c ⟨m, by omega⟩) = n at hval
        rw [bracketJoin_val_of_lt b c hmk] at hval
        omega
    · apply bracket_pair_heq
      · apply le_antisymm
        · apply Nat.find_min'
          constructor
          · change bracketJoin b c ⟨k, by omega⟩ = n
            rw [bracketJoin_val_mid]
            omega
        · refine (Nat.le_find_iff _ _).mpr ?_
          intro m hmk ⟨hmn, hval⟩
          change (bracketJoin b c ⟨m, by omega⟩) = n at hval
          rw [bracketJoin_val_of_lt b c hmk] at hval
          omega
      · intro i j hij
        simp only [Fin.cast_mk, Fin.val_cast, bracketLeft]
        simp_rw [hij]
        rw [bracketJoin_val_of_lt b c _]
      · intro i j hij
        simp only [Fin.cast_mk, Fin.val_cast, bracketRight, Order.lt_add_one_iff]
        simp_rw [hij]
        generalize_proofs _ pf2 _
        have hK : Nat.find pf2 = (k : ℕ) := by
          apply le_antisymm
          · exact Nat.find_min' pf2 ⟨Nat.lt_succ_iff.mp k.isLt, by rw [bracketJoin_val_mid]; omega⟩
          · refine (Nat.le_find_iff _ _).mpr ?_
            rintro m hmk ⟨hmn, hval⟩
            rw [bracketJoin_val_of_lt b c hmk] at hval
            have := (b ⟨m, hmk⟩).isLt
            omega
        grind [bracketJoin_val_of_gt b c j.isLt]
      }

/-- The number of Bracketing sequences of size `n` is given by the `n`th Catalan number. -/
theorem bracketingSequences_card (n : ℕ) : (bracketingSequences n).card = catalan n := by
  induction n using Nat.case_strong_induction_on with
  | hz => rw [catalan_zero]; decide
  | hi n ih =>
    grind [Fintype.card_congr (bracketingSequences_succ n), Fintype.card_sigma, Finset.card_product,
    Fintype.card_coe, catalan_succ]

instance {n : ℕ} : SemilatticeInf (bracketingSequences n) where
  inf := fun a b ↦ ⟨fun i ↦ min (a.1 i) (b.1 i), by grind [mem_bracketingSequences]⟩
  inf_le_left := by intro a b i; exact Std.min_le_left --could be solved by grind
  inf_le_right := by intro a b i; exact Std.min_le_right --could be solved by grind
  le_inf := by intro a b c hab hac i; exact le_min (hab i) (hac i) --could be solved by grind

instance {n : ℕ} : OrderTop (bracketingSequences n) where
  top := ⟨fun i => ⟨n - 1, by have := i.isLt; omega⟩, by grind [mem_bracketingSequences]⟩
  le_top := by intro a i; grind

instance {n : ℕ} : OrderBot (bracketingSequences n) where
  bot := ⟨id, by rw [mem_bracketingSequences]; exact isBracketing_id⟩
  bot_le := by intro ⟨a, ha⟩ i; grind [mem_bracketingSequences]

instance instDecidableLEFinPi {n : ℕ} : DecidableLE (Fin n → Fin n) :=
  fun a b => decidable_of_iff (∀ i, a i ≤ b i) Pi.le_def.symm

/-- The least bracketing sequence above `a`. -/
def bracketingClosure {n : ℕ} (a : Fin n → Fin n) : bracketingSequences n :=
  (Finset.univ.filter fun b : bracketingSequences n ↦ a ≤ b).inf (fun b => b)

lemma bracketingClosure_le {n : ℕ} {a : Fin n → Fin n} {b : bracketingSequences n} (h : a ≤ b) :
  bracketingClosure a ≤ b := Finset.inf_le <| (Finset.mem_filter_univ b).mpr h

lemma le_bracketingClosure {n : ℕ} (a : Fin n → Fin n) :
    a ≤ (bracketingClosure a : Fin n → Fin n) := by
  refine Finset.inf_induction (p := fun c : bracketingSequences n => a ≤ c) ?_ ?_ ?_
  · intro i
    change (a i : ℕ) ≤ (n - 1 : ℕ)
    omega
  · intro x hx y hy i
    exact le_min (hx i) (hy i)
  · intro b hb
    exact (Finset.mem_filter_univ b).mp hb

instance {n : ℕ} : Lattice (bracketingSequences n) :=
  { sup := fun a b ↦ bracketingClosure (a ⊔ b)
    le_sup_left := fun _ _ ↦ le_sup_left.trans (le_bracketingClosure _)
    le_sup_right := fun _ _ ↦ le_sup_right.trans (le_bracketingClosure _)
    sup_le := fun _ _ _ hac hbc ↦ bracketingClosure_le (sup_le hac hbc) }

example : ¬ ∀ x y z : bracketingSequences 3, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  intro h
  have := h ⟨![2,1,2], by decide⟩ ⟨![0,2,2], by decide⟩ ⟨![1,1,2], by decide⟩
  revert this
  decide
