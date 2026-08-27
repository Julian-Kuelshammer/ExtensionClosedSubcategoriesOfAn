import HenningWalterCombinatorics.BracketingSequences

def IsThreshold {n : ℕ} (h : Fin n → Fin n) : Prop :=
(∀i, h i ≤ n - (i.val + 1)) ∧
(∀i j, i ≤ j → h i ≤ n - (j.val + 1) → h i ≤ h j)

instance (n : ℕ) (h : Fin n → Fin n) :
    Decidable (IsThreshold h) := by
  unfold IsThreshold
  infer_instance

def ThresholdSequences (n : ℕ) : Finset (Fin n → Fin n) :=
Finset.univ.filter (IsThreshold)

lemma mem_ThresholdSequences {n : ℕ} (h : Fin n → Fin n) :
h ∈ ThresholdSequences n ↔ (∀i, h i ≤ n - (i.val + 1)) ∧
(∀i j, i ≤ j → h i ≤ n - (j.val + 1) → h i ≤ h j) := by
  simp [ThresholdSequences, IsThreshold]

#eval (ThresholdSequences 0).card
#eval (ThresholdSequences 1).card
#eval (ThresholdSequences 2).card
#eval (ThresholdSequences 3).card
#eval (ThresholdSequences 4).card

def Threshold_equiv_Bracketing (n : ℕ) : ThresholdSequences n ≃ BracketingSequences n :=
{ toFun := fun h =>
    ⟨fun i => ⟨n - (h.1 i + 1), by omega⟩, by
      rcases h with ⟨h, hh⟩
      simp only [mem_ThresholdSequences] at hh
      grind [IsBracketing, BracketingSequences]⟩,
  invFun := fun a =>
    ⟨fun i => ⟨n - (a.1 i + 1), by omega⟩, by
      grind [mem_BracketingSequences, mem_ThresholdSequences, Fin.mk_eq_zero]⟩,
  left_inv := by
    intro h
    ext i
    grind,
  right_inv := by
    intro a
    ext i
    grind }

theorem ThresholdSequences_card (n : ℕ) : (ThresholdSequences n).card = catalan n :=
  (Finset.card_eq_of_equiv (Threshold_equiv_Bracketing n)).trans (bracketingSequences_card n)
