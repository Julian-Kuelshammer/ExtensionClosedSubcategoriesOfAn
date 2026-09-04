/-
Copyright (c) 2026 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/

import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Bracketing functions

Bracketing functions `a : Fin n → Fin n` provide an elementary description of the Tamari lattice.
They correspond to the more classical encoding of binary trees as follows: Labelling the vertices
of the binary tree with the in-order traversal, i.e. recursively numbering first the left tree, then
the root, and finally the right tree, `a i` is the largest label occurring in the subtree rooted at
`i`. The partial order is then just given by componentwise comparison. This partial order is in fact
a lattice with meet given componentwise, but join given as the least bracketing function above the
pointwise maximum.

As an example, for `n = 3` one obtains the following Hasse diagram:

```
              ![2,2,2]
               /      \
              /        \
             /      ![2,1,2]
        ![0,2,2]        |
             \          |
              \     ![1,1,2]
               \       /
                \     /
                ![0,1,2]
```

## Main definitions

* `Function.IsBracketing`: A predicate on functions `a : Fin n → Fin n` to satisfy the property of
  being a bracketing function, i.e. `i ≤ a i` and `i ≤ j ≤ a i → a j ≤ a i`.
* `BracketingFunctions n`: The `Type` of all bracketing functions `Fin n → Fin n`.

## Main results

* `bracketingFunctions_card`: The number of bracketing functions of length `n` is given by the `n`th
  Catalan number.
* `instLatticeBracketingFunctions`: The lattice instance on bracketing functions, i.e. the Tamari
  lattice.

## Implementation details

In the literature, bracketing functions have been defined as functions `Icc 1 n → Icc 1 n`. As is
customary, we have shifted our functions to instead go `Fin n → Fin n`.

## References

* Huang, Samuel and Tamari, Dov: Problems of Associativity: A Simple Proof for the Lattice Property
  of Systems Ordered by a Semi-associative Law, Journal of Combinatorial Theory (A) 13, 7--13 (1972)

## TODO

* Combinatorially describe the covering relation for the Tamari lattice
* Give a bijection between bracketing functions and binary trees.
* Show that the Tamari lattice is semidistributive.
* Show that the Tamari lattice is trim.

-/
variable {n : ℕ}

namespace Function

/-- A function `a : Fin n → Fin n` is bracketing if `i ≤ a i` for all `i` and for all `i` and `j`
such that `i ≤ j ≤ a i` one has `a j ≤ a i`. -/
def IsBracketing (a : Fin n → Fin n) : Prop :=
  (∀ i, i ≤ a i) ∧ (∀ i j, i ≤ j → j ≤ a i → a j ≤ a i)
deriving Decidable

lemma IsBracketing.self_le {a : Fin n → Fin n} (ha : a.IsBracketing) (i : Fin n) : i ≤ a i :=
  ha.1 i
lemma IsBracketing.apply_le {a : Fin n → Fin n} (ha : a.IsBracketing) (i j) (hij : i ≤ j)
    (hj : j ≤ a i) : a j ≤ a i := ha.2 i j hij hj

lemma IsBracketing.apply_last {a : Fin (n + 1) → Fin (n + 1)} (ha : a.IsBracketing) :
    a (Fin.last n) = Fin.last n := le_antisymm (Fin.le_last _) (ha.self_le _)

lemma isBracketing_id : (id : Fin n → Fin n).IsBracketing := ⟨fun _ ↦ le_rfl, fun _ _ _ hji ↦ hji⟩

lemma isBracketing_const_last : (const _ (Fin.last n)).IsBracketing :=
  ⟨fun i ↦ i.le_last, fun _ _ _ _ ↦ le_rfl⟩

lemma IsBracketing.isFixedPt {a : Fin n → Fin n} (ha : a.IsBracketing) (i : Fin n) :
    IsFixedPt a (a i) :=
  le_antisymm (ha.apply_le _ _ (ha.self_le _) (le_refl _)) (ha.self_le _)

lemma IsBracketing.comp_self {a : Fin n → Fin n} (ha : a.IsBracketing) : a ∘ a = a := by
  funext i
  simpa only [comp_apply, IsFixedPt] using ha.isFixedPt i

end Function

/-- The `Type` of bracketing functions `Fin n → Fin n`. -/
abbrev BracketingFunctions (n : ℕ) : Type := {a : Fin n → Fin n // a.IsBracketing}

def Function.IsBracketing.toBracketingFunctions {a : Fin n → Fin n} (ha : a.IsBracketing) :
    BracketingFunctions n := ⟨a, ha⟩

lemma BracketingFunctions.isBracketing (a : BracketingFunctions n) :
    (a : Fin n → Fin n).IsBracketing := a.2

section rootIndex

namespace Function.IsBracketing

variable {a : Fin (n + 1) → Fin (n + 1)} (ha : a.IsBracketing)

include ha in
lemma filter_apply_eq_last_nonempty : (Finset.univ.filter fun k ↦ a k = Fin.last n).Nonempty :=
  ⟨Fin.last n, (Finset.mem_filter_univ _).mpr ha.apply_last⟩

/-- The index of the first element mapped to the last index, i.e. the position of the root
in the in-order labelling. -/
def rootIndex : Fin (n + 1) :=
  (Finset.univ.filter _).min' ha.filter_apply_eq_last_nonempty

lemma apply_rootIndex : a ha.rootIndex = Fin.last n := by
  simpa [rootIndex] using Finset.min'_mem _ ha.filter_apply_eq_last_nonempty

lemma rootIndex_le {k : Fin (n + 1)} (hk : a k = Fin.last n) : ha.rootIndex ≤ k :=
  Finset.min'_le _ _ ((Finset.mem_filter_univ k).mpr hk)

lemma le_rootIndex {k : Fin (n + 1)} (h : ∀ m < k, a m ≠ Fin.last n) : k ≤ ha.rootIndex :=
  not_lt.mp fun hlt ↦ h _ hlt ha.apply_rootIndex

lemma le_rootIndex_val {k : ℕ} (h : ∀ m : Fin (n + 1), (m : ℕ) < k → a m ≠ Fin.last n) :
    k ≤ (ha.rootIndex : ℕ) := not_lt.mp fun hlt ↦ h ha.rootIndex hlt ha.apply_rootIndex

lemma lt_rootIndex {k : Fin (n + 1)} (hk : k < ha.rootIndex) :
    a k ≠ Fin.last n := fun h ↦ absurd (ha.rootIndex_le h) (not_le.mpr hk)

lemma rootIndex_cast {m : ℕ} (h : n = m)
    (ha' : (fun (i : Fin (m + 1)) ↦ Fin.cast (by omega) (a (Fin.cast (by omega) i))).IsBracketing) :
    (ha'.rootIndex : ℕ) = (ha.rootIndex : ℕ) := by subst h; congr 1

end Function.IsBracketing

end rootIndex

section node

variable {k l : ℕ} (b : Fin k → Fin k) (c : Fin l → Fin l)

/-- Given two bracketing functions `b : Fin k → Fin k` and `c : Fin l → Fin l`, constructs a
bracketing function on `Fin (k + l + 1)` with first `k` values given by `b`, middle value being
`k + l` and last `l` values given by `c` shifted by `k + 1`. -/
def bracketingNode : Fin (k + l + 1) → Fin (k + l + 1) :=
  fun i ↦
    if h : i < k then ⟨b ⟨i, h⟩, by omega⟩
    else if h' : i = k then ⟨k + l, by omega⟩
    else ⟨c ⟨i - (k + 1), by omega⟩ + (k + 1), by omega⟩

lemma bracketingNode_castLE (i : Fin k) :
    bracketingNode b c (i.castLE (by omega)) = (b i).castLE (by omega) := by grind [bracketingNode]

/-- On the first `k` indices, `bracketingNode b c` is given by `b`. -/
@[simp] lemma bracketingNode_val_of_lt {i : ℕ} (h : i < k) :
    (bracketingNode b c ⟨i, by omega⟩ : ℕ) = (b ⟨i, h⟩ : ℕ) :=
  congrArg Fin.val (bracketingNode_castLE b c ⟨i, h⟩)

/-- At the separating index `k`, `bracketingNode b c` takes the maximal value `k + l`. -/
lemma bracketingNode_mid : (bracketingNode b c ⟨k, by omega⟩) = Fin.last (k + l) := by
  grind [bracketingNode]

lemma bracketingNode_mid_val : (bracketingNode b c ⟨k, by omega⟩ : ℕ) = k + l :=
  congrArg Fin.val (bracketingNode_mid b c)

lemma bracketingNode_natAdd (i : Fin l) :
    bracketingNode b c (Fin.cast (by omega) (i.natAdd (k + 1)))
      = Fin.cast (by omega) ((c i).natAdd (k + 1)) := by
  grind [bracketingNode]

/-- On the last `l` indices, `bracketingNode b c` is `c` shifted by `k + 1`. -/
lemma bracketingNode_val_of_gt {t : ℕ} (ht : t < l) :
    (bracketingNode b c ⟨k + 1 + t, by omega⟩ : ℕ) = (c ⟨t, ht⟩ + (k + 1) : ℕ) := by
  grind [bracketingNode]

lemma isBracketing_bracketingNode {b : Fin k → Fin k} {c : Fin l → Fin l}
    (hb : b.IsBracketing) (hc : c.IsBracketing) : (bracketingNode b c).IsBracketing := by
  constructor
  · rintro ⟨i, hi⟩
    rcases lt_trichotomy i k with h | rfl | h
    · grind [bracketingNode_val_of_lt b c h, hb.self_le ⟨i,h⟩]
    · grind [bracketingNode_mid b c]
    · obtain ⟨t, rfl⟩ : ∃ t, i = k + 1 + t := ⟨i - (k + 1), by omega⟩
      grind [bracketingNode_val_of_gt, hc.self_le ⟨t, by omega⟩]
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij hjbc
    simp only [Fin.le_def] at hij hjbc ⊢
    rcases lt_trichotomy i k with h | rfl | h
    · -- the case `i < k` so that `bracketingNode b c i` is `b i`
      simp_rw [bracketingNode_val_of_lt b c h] at hjbc ⊢
      have h' := hb.apply_le ⟨i, h⟩ ⟨j, lt_of_le_of_lt hjbc (b ⟨i, h⟩).isLt⟩ hij hjbc
      grind [bracketingNode_val_of_lt]
    · -- the case `i = k` so that `bracketingNode b c i` is `k + l`
      grind [bracketingNode_mid]
    · -- the case `i > k` so that `bracketingNode b c i` is `c (i - (k + 1)) + k + 1`
      obtain ⟨s, rfl⟩ : ∃ s, i = k + 1 + s := ⟨i - (k + 1), by omega⟩
      obtain ⟨t, rfl⟩ : ∃ t, j = k + 1 + t := ⟨j - (k + 1), by omega⟩
      rw [bracketingNode_val_of_gt b c (by omega)] at hjbc
      have := hc.apply_le ⟨s, (by omega)⟩ ⟨t, (by omega)⟩ (Fin.mk_le_mk.mpr (by omega)) (by grind)
      grind [bracketingNode_val_of_gt]

lemma Function.IsBracketing.rootIndex_bracketingNode {b : Fin k → Fin k} {c : Fin l → Fin l}
    (hb : b.IsBracketing) (hc : c.IsBracketing) :
    ((isBracketing_bracketingNode hb hc).rootIndex : ℕ) = k := by
  apply le_antisymm
  · exact Function.IsBracketing.rootIndex_le _ (bracketingNode_mid b c)
  · refine Function.IsBracketing.le_rootIndex_val _ fun ⟨m, hm⟩ hmk ↦ ?_
    grind [bracketingNode_val_of_lt b c hmk]

lemma Function.IsBracketing.cast {m : ℕ} (h : m = n) {a : Fin m → Fin m} (ha : a.IsBracketing) :
    (fun i ↦ Fin.cast h (a (Fin.cast h.symm i))).IsBracketing :=
  ⟨fun i ↦ by grind [ha.self_le (Fin.cast h.symm i)],
   fun i j hij hja ↦ by simpa using ha.apply_le _ _ hij (Fin.le_def.mpr hja)⟩

lemma isBracketing_cast {k : Fin (n + 1)} {b : Fin k → Fin k} {c : Fin (n - k) → Fin (n - k)}
    (hb : b.IsBracketing) (hc : c.IsBracketing) :
    (fun i ↦ Fin.cast (show k + (n - k) + 1 = n + 1 by omega)
      (bracketingNode b c (Fin.cast (show n + 1 = k + (n - k) + 1 by omega) i))).IsBracketing :=
  (isBracketing_bracketingNode hb hc).cast (by omega)

end node

section leftright

variable {a : Fin (n + 1) → Fin (n + 1)} (ha : a.IsBracketing)

/-- Given a bracketing function `a`, this constructs the function corresponding to the left tree of
`a`. -/
def bracketingLeft : Fin ha.rootIndex → Fin ha.rootIndex :=
  fun i ↦ ⟨a (i.castLE ha.rootIndex.isLt.le), by
    by_contra hik
    have hpi : a (i.castLE ha.rootIndex.isLt.le) = Fin.last n := by
      grind [ha.apply_le _ _ i.isLt.le (Nat.le_of_not_lt hik), ha.apply_rootIndex]
    exact absurd (ha.rootIndex_le hpi) (Fin.not_le.mpr i.isLt)⟩

lemma isBracketing_bracketingLeft : (bracketingLeft ha).IsBracketing :=
  have h : ha.rootIndex ≤ n + 1 := ha.rootIndex.isLt.le
  ⟨fun i ↦ ha.self_le (i.castLE h), fun _ _ hij hja ↦ ha.apply_le _ _ hij hja⟩

@[simp] lemma val_bracketingLeft (i : Fin ha.rootIndex) :
    (bracketingLeft ha i : ℕ) = (a (i.castLE ha.rootIndex.isLt.le) : ℕ) := rfl

/-- Given a bracketing function `a`, this constructs the function corresponding to the right tree
of `a`. -/
def bracketingRight : Fin (n - ha.rootIndex) → Fin (n - ha.rootIndex) :=
  fun i ↦ ⟨(a ((i.natAdd (ha.rootIndex + 1)).cast (by omega)) : ℕ) - (ha.rootIndex + 1), by
    grind [ha.self_le ((i.natAdd (ha.rootIndex + 1)).cast (by omega))]⟩

lemma isBracketing_bracketingRight : (bracketingRight ha).IsBracketing := by
  constructor
  · intro i
    grind [Fin.val_le_of_ge, bracketingRight,
      ha.self_le ((i.natAdd (ha.rootIndex + 1)).cast (by omega))]
  · intro i j hij hja
    have hja : (j : ℕ)
        ≤ a ((i.natAdd (ha.rootIndex + 1)).cast (by omega)) - (ha.rootIndex + 1) := hja
    grind [Fin.val_le_of_ge, bracketingRight, ha.apply_le
      (i := ((i.natAdd (ha.rootIndex + 1)).cast (by omega)))
      (j := ((j.natAdd (ha.rootIndex + 1)).cast (by omega))) (by grind)
      (by grind [ha.self_le ((i.natAdd (ha.rootIndex + 1)).cast (by omega))])]

@[simp] lemma val_bracketingRight (i : Fin (n - ha.rootIndex)) : (bracketingRight ha i : ℕ)
    = (a ((i.natAdd (ha.rootIndex + 1)).cast (by omega)) : ℕ) - (ha.rootIndex + 1) := rfl

end leftright

section catalan

private lemma bracket_pair_heq {k l : ℕ} (hkl : k = l)
    {b' : BracketingFunctions k} {c' : BracketingFunctions (n - k)}
    {b : BracketingFunctions l} {c : BracketingFunctions (n - l)}
    (hbb : ∀ (i : Fin k) (j : Fin l), (i : ℕ) = j → (b'.1 i : ℕ) = b.1 j)
    (hcc : ∀ (i : Fin (n - k)) (j : Fin (n - l)), (i : ℕ) = j → (c'.1 i : ℕ) = c.1 j) :
    HEq (b', c') (b, c) := by
  subst hkl
  have hbe : b' = b := Subtype.ext (funext fun i ↦ Fin.ext (hbb i i rfl))
  have hce : c' = c := Subtype.ext (funext fun i ↦ Fin.ext (hcc i i rfl))
  rw [hbe, hce]

variable (n : ℕ)

/-- The Catalan recursion bijection between bracketing functions on `Fin (n + 1)` and the disjoint
union of all possible splits of bracketing functions on `Fin k` times bracketing functions on
`Fin (n - k)`. -/
def bracketingFunctionsSuccEquiv : BracketingFunctions (n + 1) ≃ Σ k : Fin (n + 1),
    BracketingFunctions k × BracketingFunctions (n - k) where
  toFun := fun ⟨a, ha⟩ ↦
    ⟨ha.rootIndex,
     ⟨bracketingLeft ha, isBracketing_bracketingLeft ha⟩,
     ⟨bracketingRight ha, isBracketing_bracketingRight ha⟩⟩
  invFun := fun ⟨k, ⟨b, hb⟩, ⟨c, hc⟩⟩ ↦
    ⟨fun i ↦ Fin.cast (by omega) (bracketingNode b c (Fin.cast (by omega) i)),
     isBracketing_cast hb hc⟩
  left_inv := by
    rintro ⟨a, ha⟩
    ext ⟨i, hi⟩
    rcases Nat.lt_trichotomy i ha.rootIndex with h | rfl | h
    · simp [bracketingNode_val_of_lt _ _ h]
    · grind [Fin.cast_mk, bracketingNode_mid_val, ha.apply_rootIndex]
    · obtain ⟨t, rfl⟩ : ∃ t, i = ha.rootIndex + 1 + t := ⟨i - (ha.rootIndex + 1), by omega⟩
      simp [bracketingNode_val_of_gt _ _ (show t < n - ha.rootIndex by omega)]
      grind [ha.self_le ⟨ha.rootIndex + 1 + t, hi⟩]
  right_inv := by
    rintro ⟨k, ⟨b, hb⟩, ⟨c, hc⟩⟩
    have hk : ((isBracketing_cast hb hc).rootIndex : ℕ) = k :=
      ((isBracketing_bracketingNode hb hc).rootIndex_cast (by omega) _).trans
        (Function.IsBracketing.rootIndex_bracketingNode hb hc)
    simp only [Sigma.mk.injEq]
    refine ⟨Fin.ext hk, ?_⟩
    refine bracket_pair_heq hk ?_ ?_
    · intro i j hij
      simp [bracketingLeft, bracketingNode, hij]
    · grind [bracketingRight, bracketingNode]

/-- The number of bracketing functions of size `n` is given by the `n`th Catalan number. -/
theorem card_bracketingFunctions : Fintype.card (BracketingFunctions n) = catalan n := by
  induction n using Nat.case_strong_induction_on with
  | hz => rw [catalan_zero]; decide
  | hi n _ =>
    grind [Fintype.card_congr (bracketingFunctionsSuccEquiv n), Fintype.card_sigma,
      Fintype.card_prod, catalan_succ]

end catalan

section lattice

instance : SemilatticeInf (BracketingFunctions n) where
  inf := fun a b ↦ ⟨fun i ↦ a.1 i ⊓ b.1 i, by grind [Function.IsBracketing]⟩
  inf_le_left := fun a b i ↦ inf_le_left
  inf_le_right := fun a b i ↦ inf_le_right
  le_inf := fun a b c hab hac i ↦ le_inf (hab i) (hac i)

instance : OrderTop (BracketingFunctions n) where
  top := ⟨fun i ↦ ⟨n - 1, by have := i.isLt; omega⟩, by
    grind [Function.IsBracketing]⟩
  le_top := by intro a i; grind

instance : OrderBot (BracketingFunctions n) where
  bot := ⟨id, Function.isBracketing_id⟩
  bot_le := by intro ⟨a, ha⟩ i; grind [Function.IsBracketing]

-- TODO: move to where?
instance Pi.instDecidableLE {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, LE (α i)]
    [∀ i, DecidableLE (α i)] : DecidableLE (∀ i, α i) :=
  fun a b ↦ decidable_of_iff (∀ i, a i ≤ b i) Pi.le_def.symm

/-- The least bracketing function above `a`. -/
def bracketingClosure (a : Fin n → Fin n) : BracketingFunctions n :=
  (Finset.univ.filter fun b : BracketingFunctions n ↦ a ≤ b).inf (id)

lemma bracketingClosure_le {a : Fin n → Fin n} {b : BracketingFunctions n} (h : a ≤ b) :
    bracketingClosure a ≤ b := Finset.inf_le <| (Finset.mem_filter_univ b).mpr h

lemma le_bracketingClosure (a : Fin n → Fin n) :
    a ≤ (bracketingClosure a : Fin n → Fin n) := by
  refine Finset.inf_induction (p := fun c : BracketingFunctions n ↦ a ≤ c) ?_ ?_ ?_
  · intro i
    change (a i : ℕ) ≤ (n - 1 : ℕ)
    omega
  · intro x hx y hy i
    exact le_inf (hx i) (hy i)
  · intro b hb
    exact (Finset.mem_filter_univ b).mp hb

/-- `bracketingClosure` is left adjoint to the inclusion of bracketing functions into all functions
`Fin n → Fin n`, exhibiting the bracketing functions as the closed elements of a closure operator.
-/
def bracketingGI : GaloisInsertion bracketingClosure ((↑·) : BracketingFunctions n → _) where
  choice a h := ⟨a, by rw [le_antisymm (le_bracketingClosure a) h]; exact (bracketingClosure a).2⟩
  gc a b := ⟨fun h ↦ (le_bracketingClosure a).trans h, fun h ↦ bracketingClosure_le h⟩
  le_l_u b := le_bracketingClosure _
  choice_eq a h := Subtype.ext (le_antisymm h (le_bracketingClosure a)).symm

instance instLatticeBracketingFunctions : Lattice (BracketingFunctions n) where
  sup := fun a b ↦ bracketingClosure (a ⊔ b)
  le_sup_left := fun _ _ ↦ le_sup_left.trans (le_bracketingClosure _)
  le_sup_right := fun _ _ ↦ le_sup_right.trans (le_bracketingClosure _)
  sup_le := fun _ _ _ hac hbc ↦ bracketingClosure_le (sup_le hac hbc)

-- TODO: Move to counterexamples?
-- The Tamari lattice is not distributive.
example : ¬ ∀ x y z : BracketingFunctions 3, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  intro h
  have := h ⟨![2,1,2], by decide⟩ ⟨![0,2,2], by decide⟩ ⟨![1,1,2], by decide⟩
  revert this
  decide

end lattice
