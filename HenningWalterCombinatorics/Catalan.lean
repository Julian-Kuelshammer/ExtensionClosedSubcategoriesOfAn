import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder

def IsThreshold (n : ℕ) (h : Fin n → Fin n) : Prop :=
(∀i, h i ≤ n - (i.val + 1)) ∧
(∀i j, i ≤ j → h i ≤ n - (j.val + 1) → h i ≤ h j)

instance (n : ℕ) (h : Fin n → Fin n) :
    Decidable (IsThreshold n h) := by
  unfold IsThreshold
  infer_instance

def IsBracketing (n : ℕ) (a : Fin n → Fin n) : Prop :=
(∀i, i.val ≤ a i) ∧
(∀i j, i ≤ j → j.val ≤ a i → a j ≤ a i)

instance (n : ℕ) (h : Fin n → Fin n) :
    Decidable (IsBracketing n h) := by
  unfold IsBracketing
  infer_instance

def ThresholdSequences (n : ℕ) : Finset (Fin n → Fin n) :=
Finset.univ.filter (IsThreshold n)

lemma mem_ThresholdSequences {n : ℕ} (h : Fin n → Fin n) :
h ∈ ThresholdSequences n ↔ (∀i, h i ≤ n - (i.val + 1)) ∧
(∀i j, i ≤ j → h i ≤ n - (j.val + 1) → h i ≤ h j) := by
  simp [ThresholdSequences, IsThreshold]

#eval (ThresholdSequences 0).card
#eval (ThresholdSequences 1).card
#eval (ThresholdSequences 2).card
#eval (ThresholdSequences 3).card
#eval (ThresholdSequences 4).card

def BracketingSequences (n : ℕ) : Finset (Fin n → Fin n) :=
Finset.univ.filter (IsBracketing n)

lemma mem_BracketingSequences {n : ℕ} (a : Fin n → Fin n) :
a ∈ BracketingSequences n ↔ (∀i, i.val ≤ a i) ∧
(∀i j, i ≤ j → j.val ≤ a i → a j ≤ a i) := by
  simp [BracketingSequences, IsBracketing]

#eval (BracketingSequences 0).card
#eval (BracketingSequences 1).card
#eval (BracketingSequences 2).card
#eval (BracketingSequences 3).card
#eval (BracketingSequences 4).card

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

theorem bracketingSequences_card (n : ℕ) : (BracketingSequences n).card = catalan n := by
  induction n using Nat.case_strong_induction_on with
  | hz => simp [BracketingSequences, IsBracketing]
  | hi n ih =>
    sorry
