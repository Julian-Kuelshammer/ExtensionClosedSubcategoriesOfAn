import HenningWalterCombinatorics.ExtensionClosed
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic

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
  (ext_closed_sets n).filter (fun Y => (Y.filter (fun p => p.1.1 = 0)).card = k)

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

/-- $\mathcal{R}(n)_k$ and $\mathcal{R}(n)_l$ are disjoint. -/
lemma disjoint_with_specified_projectives_of_number_projectives_differs {n k l : ℕ} (h : k ≠ l) : Disjoint
    (ext_closed_sets_with_specified_number_projectives n k)
    (ext_closed_sets_with_specified_number_projectives n l) := by
  rw [Finset.disjoint_left]
  intro Y hk hl
  simp only [ext_closed_sets_with_specified_number_projectives, mem_filter] at hk hl
  omega

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
