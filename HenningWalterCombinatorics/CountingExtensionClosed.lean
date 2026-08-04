import HenningWalterCombinatorics.ExtensionClosed
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

instance {n : ℕ} (p q : higher_nakayama_convention n) : Decidable (ext_interlace p q) := by
  unfold ext_interlace
  infer_instance

instance {n : ℕ} : DecidablePred (@strong_ext_closed n) := by
  intro Y
  dsimp [strong_ext_closed]
  infer_instance

instance {n : ℕ} : Fintype (higher_nakayama_convention n) := FinsetCoe.fintype _

open Finset

/-- The set of all extension-closed, additive, idempotent split subcategories of the category of
finite-dimensional representations of the uniformly oriented `A_n`-quiver. In the paper, it is
denoted by $\mathcal{R}(n)$. -/
def ext_closed_sets (n : ℕ) : Finset (Finset (higher_nakayama_convention n)) :=
  univ.powerset.filter strong_ext_closed

lemma mem_ext_closed_sets {n : ℕ} (Y : Finset (higher_nakayama_convention n)) :
Y ∈ ext_closed_sets n ↔ strong_ext_closed Y := by
  grind [ext_closed_sets]

/-- The number of all extension-closed, additive, idempotent split subcategories of the category of
finite-dimensional representations of the uniformly oriented `A_n` quiver. In the paper, it is
denoted by $R(n)$. -/
def card_ext_closed_sets (n : ℕ) : ℕ := (ext_closed_sets n).card

/-- The index of the unique indecomposable projective-injective module for the uniformly oriented
`A_n`-quiver. -/
def ind_proj_inj (n : ℕ) : higher_nakayama_convention n :=
⟨(0, n), by rw [mem_higher_nakayama_convention_iff]; omega⟩

/-- The set of all extension-closed, additive, idempotent split subcategories of the category of
finite-dimensional representations of the uniformly oriented `A_n`-quiver containing the
unique indecomposable projective-injective module. In the paper, it is denoted by $\mathcal{P}(n)$.
-/
def ext_closed_sets_containing_proj_inj (n : ℕ) : Finset (Finset (higher_nakayama_convention n)) :=
  (ext_closed_sets n).filter (fun Y => ind_proj_inj n ∈ Y)

/-- The number of all extension-closed, additive, idempotent split subcategories of the category of
finite-dimensional representations of the uniformly oriented `A_n` quiver. In the paper, it is
denoted by $P(n)$. -/
def card_ext_closed_containing_proj_inj (n : ℕ) : ℕ := (ext_closed_sets_containing_proj_inj n).card

/-- The set of all extension-closed, additive, idempotent split subcategories of the category of
finite-dimensional representations of the uniformly oriented `A_n`-quiver containing precisely `k`
indecomposable projective representations. In the paper, it is denoted by $\mathcal{R}(n)_k$. -/
def ext_closed_sets_with_specified_number_projectives (n k : ℕ) :
  Finset (Finset (higher_nakayama_convention n)) :=
  (ext_closed_sets n).filter (fun Y ↦ (Y.filter (fun p ↦ p.1.1 = 0)).card = k)

lemma mem_ext_closed_sets_with_specified_number_projectives {n k : ℕ}
(Y : Finset (higher_nakayama_convention n)) :
Y ∈ ext_closed_sets_with_specified_number_projectives n k ↔
strong_ext_closed Y ∧ (Y.filter (fun p => p.1.1 = 0)).card = k := by
  grind [ext_closed_sets_with_specified_number_projectives, strong_ext_closed, ext_closed_sets]

/-- The number of all extension-closed, additive, idempotent split subcategories of the category of
finite-dimensional representations of the uniformly oriented `A_n`-quiver containing precisely `k`
indecomposable projective representations. In the paper, it is denoted by $R(n)_k$. -/
def card_ext_closed_sets_with_specified_number_projectives (n k : ℕ) : ℕ :=
  (ext_closed_sets_with_specified_number_projectives n k).card

/-- The set of all extension-closed, additive, idempotent split subcategories of the category of
finite-dimensional representations of the uniformly oriented `A_n`-quiver containing the unique
indecomposable projective-injective and containing precisely `k` indecomposable projective
representations. In the paper, it is denoted by $\mathcal{P}(n)_k$. -/
def ext_closed_sets_containing_proj_inj_with_specified_number_projectives (n k : ℕ) :
  Finset (Finset (higher_nakayama_convention n)) :=
  (ext_closed_sets_containing_proj_inj n).filter (fun Y => (Y.filter (fun p => p.1.1 = 0)).card = k)

/-- The number of all extension-closed, additive, idempotent split subcategories of the category of
finite-dimensional representations of the uniformly oriented `A_n`-quiver containing precisely `k`
indecomposable projective representations. In the paper, it is denoted by $P(n)_k$. -/
def card_ext_closed_sets_containing_proj_inj_with_specified_number_projectives (n k : ℕ) : ℕ :=
  (ext_closed_sets_containing_proj_inj_with_specified_number_projectives n k).card

/-- R(0)_0 = 1. -/
lemma card_ext_closed_sets_with_specified_number_projectives_zero_zero :
  card_ext_closed_sets_with_specified_number_projectives 0 0 = 1 := by
  decide

/-- R(0)_1 = 1. -/
lemma card_ext_closed_sets_with_specified_number_projectives_zero_one :
  card_ext_closed_sets_with_specified_number_projectives 0 1 = 1 := by
  decide

def projectives_in_univ (n : ℕ) :
  Fin (n + 1) ≃
    ((Finset.univ : Finset (higher_nakayama_convention n)).filter (fun p => p.1.1 = 0)) :=
  { toFun := fun i ↦ ⟨⟨(0,i), by grind [mem_higher_nakayama_convention_iff]⟩, by simp⟩
    invFun := fun p ↦ ⟨p.1.1.2, by grind [mem_higher_nakayama_convention_iff]⟩
    left_inv := by grind
    right_inv := by grind
  }

lemma cardinality_projectives_in_univ (n : ℕ) :
  ((Finset.univ : Finset (higher_nakayama_convention n)).filter (fun p => p.1.1 = 0)).card
    = n + 1 := by
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    (Fintype.card_congr (projectives_in_univ n)).symm

/-- $\mathcal{R}(n)_k$ and $\mathcal{R}(n)_l$ are disjoint. -/
lemma disjoint_with_specified_projectives_of_number_projectives_differs {n k l : ℕ} (h : k ≠ l) :
  Disjoint (ext_closed_sets_with_specified_number_projectives n k)
    (ext_closed_sets_with_specified_number_projectives n l) := by
  rw [disjoint_left]
  intro Y hk hl
  simp only [ext_closed_sets_with_specified_number_projectives, mem_filter] at hk hl
  omega

/-- $\mathcal{R}(n)=\bigcup_{k=0}^{n+1} \mathcal{R}(n)_k$. -/
lemma ext_closed_sets_eq_biUnion (n : ℕ) :
  ext_closed_sets n =
    (Finset.range (n + 2)).biUnion (ext_closed_sets_with_specified_number_projectives n) := by
  ext Y
  simp only [Finset.mem_biUnion, Finset.mem_range,
    ext_closed_sets_with_specified_number_projectives, Finset.mem_filter]
  refine ⟨fun hY => ⟨_, ?_, hY, rfl⟩, fun ⟨_, _, hY, _⟩ => hY⟩
  have h := Finset.card_le_card
    (Finset.filter_subset_filter (fun p => p.1.1 = 0) (Finset.subset_univ Y))
  rw [cardinality_projectives_in_univ] at h
  omega

/-- $R(n)=\sum_{k=0}^{n+1} R(n)_k$. -/
lemma card_ext_closed_sets_eq_sum (n : ℕ) :
    (ext_closed_sets n).card =
    ∑ k ∈ Finset.range (n + 2), (ext_closed_sets_with_specified_number_projectives n k).card := by
  rw [ext_closed_sets_eq_biUnion n]
  apply Finset.card_biUnion
  intro k _ l _ hkl
  exact disjoint_with_specified_projectives_of_number_projectives_differs hkl

def nonProjectives (n : ℕ) : Finset (higher_nakayama_convention n) :=
  Finset.univ.filter (fun p ↦ 0 < p.1.1)

lemma mem_nonProjectives {n : ℕ} (p : higher_nakayama_convention n) :
p ∈ nonProjectives n ↔ 0 < p.1.1 := by
  grind [nonProjectives]

def nonInjectives (n : ℕ) : Finset (higher_nakayama_convention n) :=
  Finset.univ.filter (fun p ↦ p.1.2 < n)

/-- The (combinatorial) AR-translate which defines a bijection between non-projective and
non-injective modules. -/
def AR_translate (n : ℕ) : nonProjectives n ≃ nonInjectives n :=
  { toFun := fun p ↦ ⟨⟨(p.1.1.1-1, p.1.1.2-1), by grind [mem_higher_nakayama_convention_iff]⟩, by
                          grind [mem_higher_nakayama_convention_iff, nonProjectives, nonInjectives]⟩
    invFun := fun p ↦ ⟨⟨(p.1.1.1+1, p.1.1.2+1), by
                          grind [mem_higher_nakayama_convention_iff, nonInjectives]⟩, by
                          grind [mem_higher_nakayama_convention_iff, nonProjectives, nonInjectives]⟩
    left_inv := by grind [mem_higher_nakayama_convention_iff, nonProjectives]
    right_inv := by grind
  }

/-- A combinatorial shadow of the fact that the injectively stable module category of a linearly
oriented `A (n + 1)`-quiver is the module category of a linearly oriented `A n`-quiver. -/
def NonInjective_equiv_convention (n : ℕ) : nonInjectives (n + 1) ≃ higher_nakayama_convention n :=
  { toFun := fun p ↦ ⟨p, by grind [mem_higher_nakayama_convention_iff, nonInjectives]⟩
    invFun := fun p ↦ ⟨⟨p, by grind [mem_higher_nakayama_convention_iff]⟩,
                           by grind [mem_higher_nakayama_convention_iff, nonInjectives]⟩
    left_inv := by grind
    right_inv := by grind
  }

/-- A combinatorial shadow of the fact that the projectively stable module category of a linearly
oriented `A (n + 1)`-quiver is the module category of a linearly oriented `A n`-quiver. -/
def NonProjective_equiv_convention (n : ℕ) : nonProjectives (n + 1) ≃
higher_nakayama_convention n :=
  { toFun := fun p ↦ ⟨(p.1.1.1 - 1, p.1.1.2 - 1), by grind [mem_higher_nakayama_convention_iff]⟩
    invFun := fun p ↦ ⟨⟨(p.1.1 + 1, p.1.2 + 1), by grind [mem_higher_nakayama_convention_iff]⟩,
                                                by grind [nonProjectives]⟩
    left_inv := by grind [mem_higher_nakayama_convention_iff, nonProjectives]
    right_inv := by grind
  }

lemma ext_interlace_NP_iff {n : ℕ} (p q : nonProjectives (n + 1)) :
    ext_interlace (NonProjective_equiv_convention n p) (NonProjective_equiv_convention n q) ↔
      ext_interlace p.1 q.1 := by
  grind [NonProjective_equiv_convention, mem_higher_nakayama_convention_iff, ext_interlace]

lemma hshort_NP_iff {n : ℕ} (p q : nonProjectives (n + 1)) :
  (NonProjective_equiv_convention n p).1.1 ≤ (NonProjective_equiv_convention n q).1.2 ↔
    p.1.1.1 ≤ q.1.1.2 := by
  grind [NonProjective_equiv_convention]

lemma long_extension_equiv {n : ℕ} {p q : nonProjectives (n + 1)} (hpq : ext_interlace p.1 q.1) :
  NonProjective_equiv_convention n ⟨long_extension hpq, by grind [nonProjectives, long_extension]⟩ =
    long_extension ((ext_interlace_NP_iff p q).mpr hpq) := by
  simp [NonProjective_equiv_convention, long_extension]

lemma short_extension_equiv {n : ℕ} {p q : nonProjectives (n + 1)} (hshort : p.1.1.1 ≤ q.1.1.2) :
  NonProjective_equiv_convention n ⟨short_extension hshort, by
    grind [nonProjectives, short_extension]⟩ =
    short_extension ((hshort_NP_iff p q).mpr hshort) := by
  grind [NonProjective_equiv_convention, short_extension]

def toNonProjectives {n : ℕ}
    (Y : ext_closed_sets_with_specified_number_projectives (n + 1) 0) :
    Finset (nonProjectives (n + 1)) :=
  Y.1.subtype (fun p ↦ p ∈ nonProjectives (n + 1))

def fromNonProjectives {n : ℕ} (S : Finset (nonProjectives (n + 1))) :
    Finset (higher_nakayama_convention (n + 1)) :=
  S.map (Function.Embedding.subtype (fun p ↦ p ∈ nonProjectives (n + 1)))

lemma mem_Y_pos {n : ℕ} (Y : ext_closed_sets_with_specified_number_projectives (n + 1) 0)
    {p : higher_nakayama_convention (n + 1)} (hp : p ∈ Y.1) : p.1.1 > 0 := by
  grind [Finset.filter_eq_empty_iff, mem_ext_closed_sets_with_specified_number_projectives]

lemma fromNonProjectives_toNonProjectives {n : ℕ}
    (Y : ext_closed_sets_with_specified_number_projectives (n + 1) 0) :
    fromNonProjectives (toNonProjectives Y) = Y.1 := by
  ext p
  simp only [fromNonProjectives, toNonProjectives, subtype_map, mem_nonProjectives, mem_filter,
    and_iff_left_iff_imp]
  intro hp
  exact mem_Y_pos Y hp

lemma toNonProjectives_fromNonProjectives {n : ℕ} (S : Finset (nonProjectives (n + 1))) :
    (fromNonProjectives S).subtype (fun p ↦ p ∈ nonProjectives (n + 1)) = S := by
  ext p
  simp [fromNonProjectives]

lemma map_equiv_symm {α β} (e : α ≃ β) (S : Finset α) :
  (S.map e.toEmbedding).map e.symm.toEmbedding = S := by
  ext x; simp

lemma map_symm_equiv {α β} (e : α ≃ β) (S : Finset β) :
    (S.map e.symm.toEmbedding).map e.toEmbedding = S := by
  ext x; simp

def ext_closed_succ_without_projectives_equiv_ext_closed (n : ℕ) :
  ↥ (ext_closed_sets_with_specified_number_projectives (n + 1) 0) ≃ ↥ (ext_closed_sets n) :=
  { toFun := fun Y ↦ ⟨(toNonProjectives Y).map (NonProjective_equiv_convention n).toEmbedding, by
      rw [mem_ext_closed_sets]
      intro p' hp' q' hq' hpq'
      simp only [Finset.mem_map, Equiv.coe_toEmbedding] at hp' hq'
      obtain ⟨p, hpY, rfl⟩ := hp'
      obtain ⟨q, hqY, rfl⟩ := hq'
      have hp1Y := Finset.mem_subtype.mp hpY
      have hq1Y := Finset.mem_subtype.mp hqY
      have hpq := (ext_interlace_NP_iff p q).mp hpq'
      obtain ⟨hYclosed, -⟩ := (mem_ext_closed_sets_with_specified_number_projectives Y.1).mp Y.2
      obtain ⟨hlongY, hshortY⟩ := hYclosed p.1 hp1Y q.1 hq1Y hpq
      constructor
      · rw [← long_extension_equiv hpq]
        exact Finset.mem_map_of_mem _ (Finset.mem_subtype.mpr hlongY)
      · intro hshort'
        have hshort := (hshort_NP_iff p q).mp hshort'
        rw [← short_extension_equiv hshort]
        exact Finset.mem_map_of_mem _ (Finset.mem_subtype.mpr (hshortY hshort))⟩
    invFun := fun Y ↦
        ⟨fromNonProjectives (Y.1.map (NonProjective_equiv_convention n).symm.toEmbedding), by
        rw [mem_ext_closed_sets_with_specified_number_projectives]
        constructor
        · intro p' hp' q' hq' hpq'
          simp only [fromNonProjectives, Finset.mem_map, Equiv.coe_toEmbedding] at hp' hq'
          obtain ⟨p, hpY, rfl⟩ := hp'
          obtain ⟨q, hqY, rfl⟩ := hq'
          have hpY' : NonProjective_equiv_convention n p ∈ Y.1 := by
            obtain ⟨a, ha, hpa⟩ := hpY
            rw [← hpa, Equiv.apply_symm_apply]
            exact ha
          have hqY' : NonProjective_equiv_convention n q ∈ Y.1 := by
            obtain ⟨a, ha, hqa⟩ := hqY
            rw [← hqa, Equiv.apply_symm_apply]
            exact ha
          have hpq := (ext_interlace_NP_iff p q).mpr hpq'
          obtain ⟨hlongY, hshortY⟩ :=
            (mem_ext_closed_sets Y.1).mp Y.2 _ hpY' _ hqY' hpq
          constructor
          · simp only [fromNonProjectives, Finset.mem_map, Equiv.coe_toEmbedding]
            let r : nonProjectives (n + 1) := ⟨long_extension hpq', by
            simp only [nonProjectives, mem_filter, mem_univ, true_and, long_extension]
            exact (Finset.mem_filter.mp q.2).2⟩
            refine ⟨r, ⟨long_extension hpq, hlongY, ?_⟩, rfl⟩
            symm
            simpa [r] using congrArg (NonProjective_equiv_convention n).symm
              (long_extension_equiv hpq')
          · intro hshort
            have hshort' := (hshort_NP_iff p q).mpr hshort
            simp only [fromNonProjectives, Finset.mem_map, Equiv.coe_toEmbedding]
            let r : nonProjectives (n + 1) := ⟨short_extension hshort, by
            simp only [nonProjectives, mem_filter, mem_univ, true_and, short_extension]
            exact (Finset.mem_filter.mp p.2).2⟩
            refine ⟨r, ⟨short_extension hshort', hshortY hshort', ?_⟩, rfl⟩
            symm
            simpa [r] using congrArg (NonProjective_equiv_convention n).symm
              (short_extension_equiv hshort)
        · rw [card_eq_zero, filter_eq_empty_iff]
          rintro ⟨⟨a,b⟩,hab⟩ hp hzero
          simp only at hzero
          simp [hzero, fromNonProjectives, nonProjectives] at hp⟩
    left_inv := by
      intro Y
      apply Subtype.ext
      simp [map_equiv_symm, fromNonProjectives_toNonProjectives]
    right_inv := by
      intro Y
      apply Subtype.ext
      simp [toNonProjectives, toNonProjectives_fromNonProjectives, map_symm_equiv]
  }

/-- Proposition 1 (6) -/
theorem card_ext_closed_with_specified_number_of_projectives_zero (n : ℕ) :
card_ext_closed_sets_with_specified_number_projectives (n + 1) 0
= ∑ i ∈ Finset.Icc 0 (n + 1), card_ext_closed_sets_with_specified_number_projectives n i := by
  simp_rw [card_ext_closed_sets_with_specified_number_projectives,
    ← Nat.range_succ_eq_Icc_zero (n + 1), ← card_ext_closed_sets_eq_sum, ← Fintype.card_coe]
  exact Fintype.card_congr (ext_closed_succ_without_projectives_equiv_ext_closed n)

/-- $P(n)_0 = 0$. -/
theorem card_ext_closed_sets_containing_proj_inj_with_specified_number_projectives_zero (n : ℕ) :
  card_ext_closed_sets_containing_proj_inj_with_specified_number_projectives n 0 = 0 := by
  rw [card_ext_closed_sets_containing_proj_inj_with_specified_number_projectives, card_eq_zero,
    eq_empty_iff_forall_notMem]
  intro Y hY
  simp only [ext_closed_sets_containing_proj_inj_with_specified_number_projectives, mem_filter]
    at hY
  rcases hY with ⟨hY, hcard⟩
  simp only [ext_closed_sets_containing_proj_inj, mem_filter] at hY
  have hmem : ind_proj_inj n ∈ Y.filter (fun p => p.1.1 = 0) := by
    simp only [mem_filter]
    exact ⟨hY.2, rfl⟩
  rw [card_eq_zero] at hcard
  rw [hcard] at hmem
  contradiction

/-- P(0)_1 = 1. -/
lemma card_ext_closed_sets_containing_proj_inj_with_specified_number_projectives_zero_one :
  card_ext_closed_sets_containing_proj_inj_with_specified_number_projectives 0 1 = 1 := by
  decide

/-- $\mathcal{P}(n)_k$ and $\mathcal{P}(n)_l$ are disjoint. -/
lemma disjoint_containing_proj_inj_with_specified_projectives_of_number_projectives_differs
{n k l : ℕ} (h : k ≠ l) : Disjoint
    (ext_closed_sets_containing_proj_inj_with_specified_number_projectives n k)
    (ext_closed_sets_containing_proj_inj_with_specified_number_projectives n l) := by
  rw [Finset.disjoint_left]
  intro Y hk hl
  simp only [ext_closed_sets_containing_proj_inj_with_specified_number_projectives, mem_filter]
    at hk hl
  omega

/-- $\mathcal{P}(n)=\bigcup_{k=0}^{n+1} \mathcal{P}(n)_k$. -/
lemma ext_closed_sets_containing_proj_inj_eq_biUnion (n : ℕ) :
    ext_closed_sets_containing_proj_inj n =
      (Finset.range (n + 2)).biUnion
        (ext_closed_sets_containing_proj_inj_with_specified_number_projectives n) := by
  ext Y
  simp only [Finset.mem_biUnion, Finset.mem_range,
    ext_closed_sets_containing_proj_inj_with_specified_number_projectives, Finset.mem_filter]
  refine ⟨fun hY => ⟨_, ?_, hY, rfl⟩, fun ⟨_, _, hY, _⟩ => hY⟩
  have h := Finset.card_le_card
    (Finset.filter_subset_filter (fun p => p.1.1 = 0) (Finset.subset_univ Y))
  rw [cardinality_projectives_in_univ] at h
  omega

/-- $P(n)=\sum_{k=0}^{n+1} P(n)_k$. -/
lemma card_ext_closed_sets_containing_proj_inj_eq_sum (n : ℕ) :
    (ext_closed_sets_containing_proj_inj n).card =
    ∑ k ∈ Finset.range (n + 2),
      (ext_closed_sets_containing_proj_inj_with_specified_number_projectives n k).card := by
  rw [ext_closed_sets_containing_proj_inj_eq_biUnion n]
  apply Finset.card_biUnion
  intro k _ l _ hkl
  exact disjoint_containing_proj_inj_with_specified_projectives_of_number_projectives_differs hkl
