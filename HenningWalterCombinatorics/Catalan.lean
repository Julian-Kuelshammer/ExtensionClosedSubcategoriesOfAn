import Mathlib

def IsThreshold (n : ℕ) (h : Fin (n + 1) → Fin (n + 2)) : Prop :=
(h 0 = 0) ∧
(∀i, h i ≤ n + 1 - i.val) ∧
(∀i j, i ≤ j → h i ≤ n + 1 - j.val → h i ≤ h j)

instance (n : ℕ) (h : Fin (n + 1) → Fin (n + 2)) :
    Decidable (IsThreshold n h) := by
  unfold IsThreshold
  infer_instance

def IsYSequence (n : ℕ) (a : Fin (n + 1) → Fin (n + 2)) : Prop :=
(a 0 = n + 1) ∧
(∀i, i.val ≤ a i) ∧
(∀i j, i ≤ j → j.val ≤ a i → a j ≤ a i)

instance (n : ℕ) (h : Fin (n + 1) → Fin (n + 2)) :
    Decidable (IsYSequence n h) := by
  unfold IsYSequence
  infer_instance

def ThresholdSequences (n : ℕ) : Finset (Fin (n + 1) → Fin (n + 2)) :=
Finset.univ.filter (IsThreshold n)

lemma mem_ThresholdSequences {n : ℕ} (h : Fin (n + 1) → Fin (n + 2)):
h ∈ ThresholdSequences n ↔ (h 0 = 0) ∧ (∀i, h i ≤ n + 1 - i.val) ∧
(∀i j, i ≤ j → h i ≤ n + 1 - j.val → h i ≤ h j) := by
  simp [ThresholdSequences, IsThreshold]

#eval (ThresholdSequences 4).card

def YSequences (n : ℕ) : Finset (Fin (n + 1) → Fin (n + 2)) :=
Finset.univ.filter (IsYSequence n)

lemma mem_YSequences {n : ℕ} (a : Fin (n + 1) → Fin (n + 2)) :
a ∈ YSequences n ↔ (a 0 = n + 1) ∧ (∀i, i.val ≤ a i) ∧
(∀i j, i ≤ j → j.val ≤ a i → a j ≤ a i) := by
  simp [YSequences, IsYSequence]

#eval (YSequences 4).card

def Threshold_equiv_Y (n : ℕ) : ThresholdSequences n ≃ YSequences n :=
{ toFun := fun h =>
    ⟨fun i => ⟨n + 1 - h.1 i, by omega⟩, by
      rcases h with ⟨h, hh⟩
      simp only [mem_ThresholdSequences] at hh
      rcases hh with ⟨hh1, hh2, hh3⟩
      simp only [YSequences, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · simp [hh1]
      · grind⟩,
  invFun := fun a =>
    ⟨fun i => ⟨n + 1 - a.1 i, by omega⟩, by
      grind [mem_YSequences, mem_ThresholdSequences, Fin.mk_eq_zero]⟩,
  left_inv := by
    intro h
    ext i
    grind,
  right_inv := by
    intro a
    ext i
    grind }
