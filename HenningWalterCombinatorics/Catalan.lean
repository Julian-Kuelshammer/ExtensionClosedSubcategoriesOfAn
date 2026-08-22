import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic

def IsBracketing {n : ℕ} (a : Fin n → Fin n) : Prop :=
(∀i, i.val ≤ a i) ∧
(∀i j, i ≤ j → j.val ≤ a i → a j ≤ a i)

instance {n : ℕ} (a : Fin n → Fin n) :
    Decidable (IsBracketing a) := by
  unfold IsBracketing
  infer_instance

lemma isBracketing_final {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : IsBracketing a) :
a ⟨n, by omega⟩ = n := by
  have := hB.1 ⟨n, by omega⟩
  grind

lemma isBracketing_id {n : ℕ} : IsBracketing (id : Fin n → Fin n) := by grind [IsBracketing]

lemma isBracketing_const_last {n : ℕ} : IsBracketing (Function.const (Fin (n + 1)) ⟨n, by omega⟩)
:= by grind [IsBracketing]

def BracketingSequences (n : ℕ) : Finset (Fin n → Fin n) :=
Finset.univ.filter (IsBracketing)

lemma mem_BracketingSequences {n : ℕ} (a : Fin n → Fin n) :
a ∈ BracketingSequences n ↔ (∀i, i.val ≤ a i) ∧
(∀i j, i ≤ j → j.val ≤ a i → a j ≤ a i) := by
  simp [BracketingSequences, IsBracketing]

#eval (BracketingSequences 0).card
#eval (BracketingSequences 1).card
#eval (BracketingSequences 2).card
#eval (BracketingSequences 3).card
#eval (BracketingSequences 4).card

/-- Given two sequences `a` and `b`, constructs the sequence a (k+l) (k+1+b). -/
def bracketJoin {k l : ℕ} (a : Fin k → Fin k) (b : Fin l → Fin l) :
    Fin (k + 1 + l) → Fin (k + 1 + l) :=
  Fin.addCases
    (Fin.addCases
      (fun i => (a i).castLE (by omega))
      (fun _ => ⟨k + l, by omega⟩))
    (fun i => ((b i).addNat (k + 1)).cast (by omega))

/-- On the first block of indices, `bracketJoin a b` is given by `a`. -/
lemma bracketJoin_val_of_lt {k l : ℕ} {a : Fin k → Fin k} {b : Fin l → Fin l} (v : ℕ) (h : v < k)
    (hv : v < k + 1 + l) :
    (bracketJoin a b ⟨v, hv⟩).val = (a ⟨v, h⟩).val := by
  have he : (⟨v, hv⟩ : Fin (k + 1 + l)) = ((⟨v, h⟩ : Fin k).castAdd 1).castAdd l :=
    Fin.ext (by simp)
  grind [bracketJoin]

/-- At the separating index `k`, `bracketJoin a b` takes the maximal value `k + l`. -/
lemma bracketJoin_val_mid {k l : ℕ} {a : Fin k → Fin k} {b : Fin l → Fin l}
    (hv : k < k + 1 + l) :
    (bracketJoin a b ⟨k, hv⟩).val = k + l := by
  have he : (⟨k, hv⟩ : Fin (k + 1 + l)) = ((0 : Fin 1).natAdd k).castAdd l := Fin.ext (by simp)
  grind [bracketJoin]

/-- On the second block of indices, `bracketJoin a b` is `b` shifted by `k + 1`. -/
lemma bracketJoin_val_of_gt {k l : ℕ} {a : Fin k → Fin k} {b : Fin l → Fin l} (t : ℕ) (ht : t < l)
    (hv : k + 1 + t < k + 1 + l) :
    (bracketJoin a b ⟨k + 1 + t, hv⟩).val = (b ⟨t, ht⟩).val + (k + 1) := by
  have he : (⟨k + 1 + t, hv⟩ : Fin (k + 1 + l)) = (⟨t, ht⟩ : Fin l).natAdd (k + 1) :=
    Fin.ext (by simp)
  grind [bracketJoin]

lemma bracketJoin_mem {k l : ℕ} {a : Fin k → Fin k} {b : Fin l → Fin l} (ha : IsBracketing a)
(hb : IsBracketing b) : IsBracketing (bracketJoin a b) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases lt_trichotomy i k with h | rfl | h
    · simpa [bracketJoin_val_of_lt i h hi] using ha.1 ⟨i, h⟩
    · simp [bracketJoin_val_mid hi]
    · obtain ⟨t, rfl⟩ : ∃ t, i = k + 1 + t := ⟨i - (k + 1), by omega⟩
      have ht : t < l := by omega
      have : t ≤ (b ⟨t, ht⟩).val := hb.1 ⟨t, ht⟩
      simp only [bracketJoin_val_of_gt t ht hi]
      omega
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij hja
    simp only [Fin.le_def] at hij ⊢
    rcases lt_trichotomy i k with h | rfl | h
    · -- both indices lie in the first block, where `bracketJoin a b` is `a`
      rw [bracketJoin_val_of_lt i h hi] at hja ⊢
      have h' := ha.2 ⟨i, h⟩ ⟨j, lt_of_le_of_lt hja (a ⟨i, h⟩).is_lt⟩ (by omega) hja
      grind [bracketJoin_val_of_lt]
    · -- `i` is the separating index, whose value is maximal
      grind [bracketJoin_val_mid]
    · -- both indices lie in the second block, where `bracketJoin a b` is a shift of `b`
      obtain ⟨s, rfl⟩ : ∃ s, i = k + 1 + s := ⟨i - (k + 1), by omega⟩
      have hs : s < l := by omega
      obtain ⟨t, rfl⟩ : ∃ t, j = k + 1 + t := ⟨j - (k + 1), by omega⟩
      have ht : t < l := by omega
      rw [bracketJoin_val_of_gt s hs hi] at hja
      have := hb.2 ⟨s, hs⟩ ⟨t, ht⟩ (Fin.mk_le_mk.mpr (by omega)) (by grind)
      grind [bracketJoin_val_of_gt]

def construct {k l : ℕ}  :
BracketingSequences k → BracketingSequences l → BracketingSequences (k + l + 1) :=
sorry

theorem bracketingSequences_card (n : ℕ) : (BracketingSequences n).card = catalan n := by
  induction n using Nat.case_strong_induction_on with
  | hz => simp [BracketingSequences, IsBracketing]
  | hi n ih =>
    sorry

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
