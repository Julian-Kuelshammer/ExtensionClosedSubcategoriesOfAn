import ExtensionClosedSubcategoriesOfAn.BracketingFunctions

def Function.IsThreshold {n : ℕ} (h : Fin n → Fin n) : Prop :=
(∀i, h i ≤ n - (i.val + 1)) ∧
(∀i j, i ≤ j → h i ≤ n - (j.val + 1) → h i ≤ h j)

open Function

instance (n : ℕ) (h : Fin n → Fin n) :
    Decidable (IsThreshold h) := by
  unfold IsThreshold
  infer_instance

def ThresholdFunctions (n : ℕ) : Finset (Fin n → Fin n) :=
Finset.univ.filter (IsThreshold)

lemma mem_ThresholdFunctions {n : ℕ} (h : Fin n → Fin n) :
h ∈ ThresholdFunctions n ↔ (∀i, h i ≤ n - (i.val + 1)) ∧
(∀i j, i ≤ j → h i ≤ n - (j.val + 1) → h i ≤ h j) := by
  simp [ThresholdFunctions, IsThreshold]

def Threshold_equiv_Bracketing (n : ℕ) : ThresholdFunctions n ≃ bracketingFunctions n :=
{ toFun := fun h =>
    ⟨fun i => ⟨n - (h.1 i + 1), by omega⟩, by
      rcases h with ⟨h, hh⟩
      simp only [mem_ThresholdFunctions] at hh
      grind [Function.IsBracketing, bracketingFunctions]⟩,
  invFun := fun a =>
    ⟨fun i => ⟨n - (a.1 i + 1), by omega⟩, by
      grind [mem_bracketingFunctions, IsBracketing, mem_ThresholdFunctions, Fin.mk_eq_zero]⟩,
  left_inv := by
    intro h
    ext i
    grind,
  right_inv := by
    intro a
    ext i
    grind }

theorem ThresholdFunctions_card (n : ℕ) : (ThresholdFunctions n).card = catalan n :=
  (Finset.card_eq_of_equiv (Threshold_equiv_Bracketing n)).trans (bracketingFunctions_card n)
