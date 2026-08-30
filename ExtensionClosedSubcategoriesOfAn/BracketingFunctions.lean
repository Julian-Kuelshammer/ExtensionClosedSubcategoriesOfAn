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
* `bracketingFunctions n`: The `Finset` of all bracketing functions `Fin n → Fin n`.

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

/-- A function `a : Fin n → Fin n` is bracketing if `i ≤ a i` for all `i` and for all `i` and `j`
such that `i ≤ j ≤ a i` one has `a j ≤ a i`. -/
def Function.IsBracketing (a : Fin n → Fin n) : Prop :=
  (∀ i, i.val ≤ a i) ∧ (∀ i j, i ≤ j → j.val ≤ a i → a j ≤ a i)
deriving Decidable

open Function

lemma Function.IsBracketing.apply_last {a : Fin (n + 1) → Fin (n + 1)} (ha : a.IsBracketing) :
    a ⟨n, lt_add_one n⟩ = n := by grind [ha.1 ⟨n, lt_add_one n⟩]

lemma Function.IsBracketing.exists_apply_eq_last {a : Fin (n + 1) → Fin (n + 1)}
    (ha : a.IsBracketing) : ∃ k : ℕ, ∃ hk : k < n + 1, (a ⟨k, hk⟩) = n :=
  ⟨n, lt_add_one n, ha.apply_last⟩

lemma isBracketing_id : (id : Fin n → Fin n).IsBracketing := ⟨fun _ ↦ le_rfl, fun _ _ _ hji ↦ hji⟩

lemma isBracketing_const_last : (Function.const _ ⟨n, lt_add_one n⟩).IsBracketing :=
  ⟨fun i ↦ i.le_last, fun _ _ _ _ ↦ Fin.ge_of_eq rfl⟩

lemma Function.IsBracketing.isFixedPt {a : Fin n → Fin n} (ha : a.IsBracketing) (i : Fin n) :
    Function.IsFixedPt a (a i) :=
  le_antisymm (ha.2 i (a i) (ha.1 i) (le_refl (a i))) (ha.1 (a i))

lemma Function.IsBracketing.comp_self {a : Fin n → Fin n} (ha : a.IsBracketing) : a ∘ a = a := by
  funext i
  simpa only [Function.comp_apply, Function.IsFixedPt] using ha.isFixedPt i

/-- The `Finset` of bracketing functions `Fin n → Fin n`. -/
def bracketingFunctions (n : ℕ) : Finset (Fin n → Fin n) := Finset.univ.filter (IsBracketing)

@[simp] lemma mem_bracketingFunctions {a : Fin n → Fin n} :
    a ∈ bracketingFunctions n ↔ a.IsBracketing := by simp [bracketingFunctions]

section rootIndex

variable {a : Fin (n + 1) → Fin (n + 1)} (ha : a.IsBracketing)

/-- The index of the first element mapped to the last index, i.e. the position of the root
in the in-order labelling. -/
def Function.IsBracketing.rootIndex : Fin (n + 1) :=
  ⟨Nat.find (ha.exists_apply_eq_last), (Nat.find_spec (ha.exists_apply_eq_last)).1⟩

lemma apply_rootIndex : a (ha.rootIndex) = n := (Nat.find_spec (ha.exists_apply_eq_last)).2

lemma rootIndex_le {k : Fin (n + 1)} (h : a k = n) : ha.rootIndex ≤ k := Nat.find_min' _ ⟨k.2, h⟩

lemma le_rootIndex {k : ℕ} (h : ∀ m : Fin (n + 1), (m : ℕ) < k → (a m : ℕ) ≠ n) :
    k ≤ (ha.rootIndex : ℕ) :=
  (Nat.le_find_iff _ _).mpr fun m hmk ⟨hmn, hval⟩ => h ⟨m, hmn⟩ hmk hval

lemma lt_rootIndex {k : Fin (n + 1)} (hk : k < ha.rootIndex) : a k ≠ n :=
  fun h ↦ Nat.find_min (ha.exists_apply_eq_last) hk ⟨k.isLt, h⟩

lemma rootIndex_cast {m : ℕ} (h : n = m)
    (ha' : (fun (i : Fin (m + 1)) ↦ Fin.cast (by omega) (a (Fin.cast (by omega) i))).IsBracketing) :
    (ha'.rootIndex : ℕ) = (ha.rootIndex : ℕ) := by subst h; congr 1

end rootIndex

section node

variable {k l : ℕ} (b : Fin k → Fin k) (c : Fin l → Fin l)

/-- Given two bracketing functions `b : Fin k → Fin k` and `c : Fin l → Fin l`, constructs a
bracketing function on `Fin (k + l + 1)` with first `k` values given by `b`, middle value being
`k + l` and last `l` values given by `c` shifted by `k + 1`. -/
def bracketingNode : Fin (k + l + 1) → Fin (k + l + 1) :=
  fun i ↦
    if h : (i : ℕ) < k then ⟨b ⟨i, h⟩, by have := (b ⟨i, h⟩).isLt; omega⟩
    else if h' : (i : ℕ) = k then ⟨k + l, by omega⟩
    else ⟨(c ⟨i - (k + 1), by have := i.isLt; omega⟩ : ℕ) + (k + 1), by
      have := (c ⟨(i : ℕ) - (k + 1), by have := i.isLt; omega⟩).isLt; omega⟩

/-- On the first `k` indices, `bracketingNode b c` is given by `b`. -/
lemma bracketingNode_val_of_lt {v : ℕ} (h : v < k) :
    (bracketingNode b c ⟨v, by omega⟩).val = (b ⟨v, h⟩).val := by simp [bracketingNode, h]

/-- At the separating index `k`, `bracketingNode b c` takes the maximal value `k + l`. -/
lemma bracketingNode_val_mid : (bracketingNode b c ⟨k, by omega⟩).val = k + l := by
  simp [bracketingNode]

/-- On the last `l` indices, `bracketingNode b c` is `c` shifted by `k + 1`. -/
lemma bracketingNode_val_of_gt {t : ℕ} (ht : t < l) :
    (bracketingNode b c ⟨k + 1 + t, by omega⟩ : ℕ) = c ⟨t, ht⟩ + (k + 1) := by
  grind [bracketingNode]

lemma isBracketing_bracketingNode {b : Fin k → Fin k} {c : Fin l → Fin l}
    (hb : b.IsBracketing) (hc : c.IsBracketing) : (bracketingNode b c).IsBracketing := by
  constructor
  · rintro ⟨i, hi⟩
    rcases lt_trichotomy i k with h | rfl | h
    · simpa [bracketingNode_val_of_lt b c h] using hb.1 ⟨i, h⟩
    · simp [bracketingNode_val_mid b c]
    · obtain ⟨t, rfl⟩ : ∃ t, i = k + 1 + t := ⟨i - (k + 1), by omega⟩
      grind [bracketingNode_val_of_gt, hc.1 ⟨t, by omega⟩]
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij hjbc
    simp only [Fin.le_def] at hij ⊢
    rcases lt_trichotomy i k with h | rfl | h
    · -- the case `i < k` so that `bracketingNode b c i` is `b i`
      rw [bracketingNode_val_of_lt b c h] at hjbc ⊢
      have h' := hb.2 ⟨i, h⟩ ⟨j, lt_of_le_of_lt hjbc (b ⟨i, h⟩).isLt⟩ (by omega) hjbc
      grind [bracketingNode_val_of_lt]
    · -- the case `i = k` so that `bracketingNode b c i` is `k + l`
      grind [bracketingNode_val_mid]
    · -- the case `i > k` so that `bracketingNode b c i` is `c (i - (k + 1)) + k + 1`
      obtain ⟨s, rfl⟩ : ∃ s, i = k + 1 + s := ⟨i - (k + 1), by omega⟩
      obtain ⟨t, rfl⟩ : ∃ t, j = k + 1 + t := ⟨j - (k + 1), by omega⟩
      rw [bracketingNode_val_of_gt b c (by omega)] at hjbc
      have := hc.2 ⟨s, (by omega)⟩ ⟨t, (by omega)⟩ (Fin.mk_le_mk.mpr (by omega)) (by grind)
      grind [bracketingNode_val_of_gt]

lemma rootIndex_bracketingNode {b : Fin k → Fin k} {c : Fin l → Fin l}
    (hb : b.IsBracketing) (hc : c.IsBracketing) :
    ((isBracketing_bracketingNode hb hc).rootIndex : ℕ) = k := by
  apply le_antisymm
  · exact rootIndex_le _ (bracketingNode_val_mid b c)
  · refine le_rootIndex _ fun _ hmk _ ↦ ?_
    grind [bracketingNode_val_of_lt b c hmk]

lemma Function.IsBracketing.cast {m : ℕ} (h : m = n) {a : Fin m → Fin m} (ha : a.IsBracketing) :
    (fun i ↦ Fin.cast h (a (Fin.cast h.symm i))).IsBracketing :=
  ⟨fun i ↦ by simpa using ha.1 (Fin.cast h.symm i),
   fun i j hij hja ↦ by
     simpa using ha.2 (Fin.cast h.symm i) (Fin.cast h.symm j) (by simpa) (by simpa)⟩

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
    have hpi : a (i.castLE ha.rootIndex.isLt.le) = n := by
      grind [ha.2 (i.castLE ha.rootIndex.isLt.le) ha.rootIndex i.isLt.le (Nat.le_of_not_lt hik),
        apply_rootIndex ha]
    exact absurd (rootIndex_le ha hpi) (Fin.not_le.mpr i.isLt)⟩

lemma isBracketing_bracketingLeft : (bracketingLeft ha).IsBracketing :=
  have h : ha.rootIndex ≤ n + 1 := ha.rootIndex.isLt.le
  ⟨fun i ↦ ha.1 (i.castLE h), fun i j hij hja ↦ ha.2 (i.castLE h) (j.castLE h) hij hja⟩

@[simp] lemma val_bracketingLeft (i : Fin ha.rootIndex) :
    (bracketingLeft ha i : ℕ) = (a (i.castLE ha.rootIndex.isLt.le) : ℕ) := rfl

/-- Given a bracketing function `a`, this constructs the function corresponding to the right tree
of `a`. -/
def bracketingRight : Fin (n - ha.rootIndex) → Fin (n - ha.rootIndex) :=
  fun i ↦ ⟨(a ((i.natAdd (ha.rootIndex + 1)).cast (by omega)) : ℕ) - (ha.rootIndex + 1), by
    grind [ha.1 ((i.natAdd (ha.rootIndex + 1)).cast (by omega))]⟩

lemma isBracketing_bracketingRight : (bracketingRight ha).IsBracketing := by
  constructor
  · intro i
    change (i : ℕ) ≤ a ((i.natAdd (ha.rootIndex + 1)).cast (by omega)) - (ha.rootIndex + 1)
    grind [ha.1 ((i.natAdd (ha.rootIndex + 1)).cast (by omega))]
  · intro i j hij hja
    replace hja : (j : ℕ)
        ≤ a ((i.natAdd (ha.rootIndex + 1)).cast (by omega)) - (ha.rootIndex + 1) := hja
    have h2 := ha.2 ((i.natAdd (ha.rootIndex + 1)).cast (by omega))
      ((j.natAdd (ha.rootIndex + 1)).cast (by omega)) (by grind)
      (by grind [ha.1 ((i.natAdd (ha.rootIndex + 1)).cast (by omega))])
    change (a ((j.natAdd (ha.rootIndex + 1)).cast (by omega)) : ℕ) - (ha.rootIndex + 1)
       ≤ (a ((i.natAdd (ha.rootIndex + 1)).cast (by omega)) : ℕ) - (ha.rootIndex + 1)
    omega

@[simp] lemma val_bracketingRight (i : Fin (n - ha.rootIndex)) : (bracketingRight ha i : ℕ)
    = (a ((i.natAdd (ha.rootIndex + 1)).cast (by omega)) : ℕ) - (ha.rootIndex + 1) := rfl

end leftright

section catalan

lemma bracket_pair_heq {k l : ℕ} (hkl : k = l) {b' : Fin k → Fin k}
    {c' : Fin (n - k) → Fin (n - k)} {b : Fin l → Fin l} {c : Fin (n - l) → Fin (n - l)}
    (h1 : (b', c') ∈ bracketingFunctions k ×ˢ bracketingFunctions (n - k))
    (h2 : (b, c) ∈ bracketingFunctions l ×ˢ bracketingFunctions (n - l))
    (hbb : ∀ (i : Fin k) (j : Fin l), i.val = j.val → (b' i).val = (b j).val)
    (hcc : ∀ (i : Fin (n - k)) (j : Fin (n - l)), i.val = j.val → (c' i).val = (c j).val) :
    HEq (⟨(b', c'), h1⟩ : ↥(bracketingFunctions k ×ˢ bracketingFunctions (n - k)))
      (⟨(b, c), h2⟩ : ↥(bracketingFunctions l ×ˢ bracketingFunctions (n - l))) := by
  subst hkl
  have hbe := funext fun i => Fin.ext (hbb i i rfl)
  have hce := funext fun i => Fin.ext (hcc i i rfl)
  simp [hbe, hce]

variable (n : ℕ)

/-- The Catalan recursion bijection between bracketing functions on `Fin (n + 1)` and the disjoint
union of all possible splits of bracketing functions on `Fin k` times bracketing functions on
`Fin (n - k)`. -/
def bracketingFunctionsSuccEquiv : bracketingFunctions (n + 1) ≃ Σ k : Fin (n + 1),
    bracketingFunctions k ×ˢ bracketingFunctions (n - k) where
  toFun := fun ⟨a, hmem⟩ ↦
    let ha := mem_bracketingFunctions.mp hmem
    ⟨ha.rootIndex,
     ⟨(bracketingLeft ha, bracketingRight ha),
      Finset.mem_product.mpr
        ⟨mem_bracketingFunctions.mpr (isBracketing_bracketingLeft ha),
         mem_bracketingFunctions.mpr (isBracketing_bracketingRight ha)⟩⟩⟩
  invFun := fun ⟨k, ⟨b, c⟩, hmem⟩ ↦
    ⟨fun i ↦ Fin.cast (by omega) (bracketingNode b c (Fin.cast (by omega) i)),
     mem_bracketingFunctions.mpr (isBracketing_cast
       (mem_bracketingFunctions.mp (Finset.mem_product.mp hmem).1)
       (mem_bracketingFunctions.mp (Finset.mem_product.mp hmem).2))⟩
  left_inv := by
    rintro ⟨a, hmem⟩
    have ha : a.IsBracketing := mem_bracketingFunctions.mp hmem
    ext ⟨i, hi⟩
    rcases Nat.lt_trichotomy i ha.rootIndex with h | rfl | h
    · -- left subtree
      simp [bracketingNode_val_of_lt _ _ h]
    · -- the root
      grind [Fin.cast_mk, bracketingNode_val_mid, apply_rootIndex ha]
    · -- right subtree
      obtain ⟨t, rfl⟩ : ∃ t, i = ha.rootIndex + 1 + t := ⟨i - (ha.rootIndex + 1), by omega⟩
      simp [bracketingNode_val_of_gt _ _ (show t < n - ha.rootIndex by omega)]
      grind [ha.1 ⟨ha.rootIndex + 1 + t, hi⟩]
  right_inv := by
    rintro ⟨k, ⟨b, c⟩, hbc⟩
    have hb : b.IsBracketing := mem_bracketingFunctions.mp (Finset.mem_product.mp hbc).1
    have hc : c.IsBracketing := mem_bracketingFunctions.mp (Finset.mem_product.mp hbc).2
    have hkn := k.isLt
    have hk : ((isBracketing_cast hb hc).rootIndex : ℕ) = k :=
      (rootIndex_cast (isBracketing_bracketingNode hb hc)
        (by omega) _).trans (rootIndex_bracketingNode hb hc)
    simp only [Sigma.mk.injEq]
    refine ⟨Fin.ext hk , ?_⟩
    refine bracket_pair_heq hk _ _ ?_ ?_
    · intro i j hij
      simp [bracketingLeft, bracketingNode, hij]
    · grind [bracketingRight, bracketingNode]

/-- The number of bracketing functions of size `n` is given by the `n`th Catalan number. -/
theorem bracketingFunctions_card : (bracketingFunctions n).card = catalan n := by
  induction n using Nat.case_strong_induction_on with
  | hz => rw [catalan_zero]; decide
  | hi n _ =>
    grind [Fintype.card_congr (bracketingFunctionsSuccEquiv n), Fintype.card_sigma,
      Finset.card_product, Fintype.card_coe, catalan_succ]

end catalan

section lattice

instance : SemilatticeInf (bracketingFunctions n) where
  inf := fun a b ↦ ⟨fun i ↦ a.1 i ⊓ b.1 i, by grind [mem_bracketingFunctions, IsBracketing]⟩
  inf_le_left := fun a b i ↦ inf_le_left
  inf_le_right := fun a b i ↦ inf_le_right
  le_inf := fun a b c hab hac i ↦ le_inf (hab i) (hac i)

instance : OrderTop (bracketingFunctions n) where
  top := ⟨fun i => ⟨n - 1, by have := i.isLt; omega⟩, by
    grind [mem_bracketingFunctions, IsBracketing]⟩
  le_top := by intro a i; grind

instance : OrderBot (bracketingFunctions n) where
  bot := ⟨id, by rw [mem_bracketingFunctions]; exact isBracketing_id⟩
  bot_le := by intro ⟨a, ha⟩ i; grind [mem_bracketingFunctions, IsBracketing]

-- TODO: move to Mathlib/Order/Pi.lean?
instance Pi.instDecidableLE {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, LE (α i)]
    [∀ i, DecidableLE (α i)] : DecidableLE (∀ i, α i) :=
  fun a b => decidable_of_iff (∀ i, a i ≤ b i) Pi.le_def.symm

/-- The least bracketing function above `a`. -/
def bracketingClosure (a : Fin n → Fin n) : bracketingFunctions n :=
  (Finset.univ.filter fun b : bracketingFunctions n ↦ a ≤ b).inf (fun b => b)

lemma bracketingClosure_le {a : Fin n → Fin n} {b : bracketingFunctions n} (h : a ≤ b) :
    bracketingClosure a ≤ b := Finset.inf_le <| (Finset.mem_filter_univ b).mpr h

lemma le_bracketingClosure (a : Fin n → Fin n) :
    a ≤ (bracketingClosure a : Fin n → Fin n) := by
  refine Finset.inf_induction (p := fun c : bracketingFunctions n => a ≤ c) ?_ ?_ ?_
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
def bracketingGI : GaloisInsertion bracketingClosure ((↑·) : bracketingFunctions n → _) where
  choice a h := ⟨a, mem_bracketingFunctions.mpr (by
    rw [le_antisymm (le_bracketingClosure a) h]
    exact mem_bracketingFunctions.mp (bracketingClosure a).2)⟩
  gc a b := ⟨fun h ↦ (le_bracketingClosure a).trans h, fun h ↦ bracketingClosure_le h⟩
  le_l_u b := le_bracketingClosure _
  choice_eq a h := Subtype.ext (le_antisymm h (le_bracketingClosure a)).symm

instance instLatticeBracketingFunctions : Lattice (bracketingFunctions n) where
  sup := fun a b ↦ bracketingClosure (a ⊔ b)
  le_sup_left := fun _ _ ↦ le_sup_left.trans (le_bracketingClosure _)
  le_sup_right := fun _ _ ↦ le_sup_right.trans (le_bracketingClosure _)
  sup_le := fun _ _ _ hac hbc ↦ bracketingClosure_le (sup_le hac hbc)

-- TODO: Move to counterexamples?
-- The Tamari lattice is not distributive.
example : ¬ ∀ x y z : bracketingFunctions 3, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  intro h
  have := h ⟨![2,1,2], by decide⟩ ⟨![0,2,2], by decide⟩ ⟨![1,1,2], by decide⟩
  revert this
  decide

end lattice
