import ExtensionClosedSubcategoriesOfAn.BracketingFunctions
import ExtensionClosedSubcategoriesOfAn.CountingExtensionClosed

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

def Threshold_equiv_Bracketing (n : ℕ) : ThresholdFunctions n ≃ BracketingFunctions n :=
{ toFun := fun h =>
    ⟨fun i => ⟨n - (h.1 i + 1), by lia⟩, by grind [Function.IsBracketing, mem_ThresholdFunctions]⟩,
  invFun := fun a =>
    ⟨fun i => ⟨n - (a.1 i + 1), by lia⟩, by grind [Function.IsBracketing, mem_ThresholdFunctions]⟩,
  left_inv := by
    intro
    ext
    grind,
  right_inv := by
    intro
    ext
    grind }

theorem ThresholdFunctions_card (n : ℕ) : (ThresholdFunctions n).card = catalan n :=
  (Fintype.card_coe _).symm.trans ((Fintype.card_congr (Threshold_equiv_Bracketing n)).trans
  (card_bracketingFunctions n))

def Threshold_equiv_Extension_with_all_simples (n : ℕ) :
ThresholdFunctions n ≃ ext_closed_sets_with_specified_number_projectives n (n + 1) :=
{ toFun := by sorry
  invFun := by sorry
  left_inv := by sorry
  right_inv := by sorry}
