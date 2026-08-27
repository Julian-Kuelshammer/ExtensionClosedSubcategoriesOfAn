import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.SuccPred

def IsBracketing {n : ℕ} (a : Fin n → Fin n) : Prop :=
(∀i, i.val ≤ a i) ∧ (∀i j, i ≤ j → j.val ≤ a i → a j ≤ a i)

instance {n : ℕ} (a : Fin n → Fin n) : Decidable (IsBracketing a) := by
  unfold IsBracketing; infer_instance

@[simp] lemma isBracketing_final {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : IsBracketing a) :
a ⟨n, by omega⟩ = n := by grind [hB.1 ⟨n, by omega⟩]

lemma isBracketing_exists_final {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : IsBracketing a) :
  ∃ k : ℕ, ∃hk : k < n + 1, (a ⟨k, hk⟩) = n := ⟨n, lt_add_one n, isBracketing_final a hB⟩

lemma isBracketing_id {n : ℕ} : IsBracketing (id : Fin n → Fin n) := by grind [IsBracketing]

lemma isBracketing_const_last {n : ℕ} : IsBracketing (Function.const (Fin (n + 1)) ⟨n, by omega⟩)
:= by grind [IsBracketing]

def BracketingSequences (n : ℕ) : Finset (Fin n → Fin n) :=
Finset.univ.filter (IsBracketing)

lemma mem_BracketingSequences {n : ℕ} (a : Fin n → Fin n) :
a ∈ BracketingSequences n ↔ (∀i, i.val ≤ a i) ∧
(∀i j, i ≤ j → j.val ≤ a i → a j ≤ a i) := by simp [BracketingSequences, IsBracketing]

#eval (BracketingSequences 0).card
#eval (BracketingSequences 1).card
#eval (BracketingSequences 2).card
#eval (BracketingSequences 3).card
#eval (BracketingSequences 4).card

/-- Given two sequences `a` and `b`, constructs the sequence a (k+l) (k+1+b). -/
def bracketJoin {k l : ℕ} (b : Fin k → Fin k) (c : Fin l → Fin l) :
    Fin (k + 1 + l) → Fin (k + 1 + l) :=
  Fin.addCases
    (Fin.addCases
      (fun i => (b i).castLE (by omega))
      (fun _ => ⟨k + l, by omega⟩))
    (fun i => ((c i).addNat (k + 1)).cast (by omega))

/-- On the first block of indices, `bracketJoin b c` is given by `b`. -/
@[simp] lemma bracketJoin_val_of_lt {k l : ℕ} (b : Fin k → Fin k) (c : Fin l → Fin l) {v : ℕ}
(h : v < k) : (bracketJoin b c ⟨v, by omega⟩).val = (b ⟨v, h⟩).val := by
  have he : ⟨v, by omega⟩ = ((⟨v, h⟩ : Fin k).castAdd 1).castAdd l := Fin.ext (by simp)
  grind [bracketJoin]

/-- At the separating index `k`, `bracketJoin b c` takes the maximal value `k + l`. -/
@[simp] lemma bracketJoin_val_mid {k l : ℕ} (b : Fin k → Fin k) (c : Fin l → Fin l) :
    (bracketJoin b c ⟨k, by omega⟩).val = k + l := by
  have he : ⟨k, by omega⟩ = ((0 : Fin 1).natAdd k).castAdd l := Fin.ext (by simp)
  grind [bracketJoin]

/-- On the second block of indices, `bracketJoin b c` is `c` shifted by `k + 1`. -/
@[simp] lemma bracketJoin_val_of_gt {k l : ℕ} (b : Fin k → Fin k) (c : Fin l → Fin l) {t : ℕ}
(ht : t < l) : (bracketJoin b c ⟨k + 1 + t, by omega⟩).val = (c ⟨t, ht⟩).val + (k + 1) := by
  have he : ⟨k + 1 + t, by omega⟩ = (⟨t, ht⟩ : Fin l).natAdd (k + 1) := Fin.ext (by simp)
  grind [bracketJoin]

lemma bracketJoin_mem {k l : ℕ} {b : Fin k → Fin k} {c : Fin l → Fin l} (hb : IsBracketing b)
(hc : IsBracketing c) : IsBracketing (bracketJoin b c) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases lt_trichotomy i k with h | rfl | h
    · simpa [bracketJoin_val_of_lt b c h] using hb.1 ⟨i, h⟩
    · simp [bracketJoin_val_mid b c]
    · obtain ⟨t, rfl⟩ : ∃ t, i = k + 1 + t := ⟨i - (k + 1), by omega⟩
      have ht : t < l := by omega
      have : t ≤ (c ⟨t, ht⟩).val := hc.1 ⟨t, ht⟩
      simp only [bracketJoin_val_of_gt b c ht]
      omega
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij hjbc
    simp only [Fin.le_def] at hij ⊢
    rcases lt_trichotomy i k with h | rfl | h
    · -- both indices lie in the first block, where `bracketJoin b c` is `b`
      rw [bracketJoin_val_of_lt b c h] at hjbc ⊢
      have h' := hb.2 ⟨i, h⟩ ⟨j, lt_of_le_of_lt hjbc (b ⟨i, h⟩).is_lt⟩ (by omega) hjbc
      grind [bracketJoin_val_of_lt]
    · -- `i` is the separating index, whose value is maximal
      grind [bracketJoin_val_mid]
    · -- both indices lie in the second block, where `bracketJoin a b` is a shift of `b`
      obtain ⟨s, rfl⟩ : ∃ s, i = k + 1 + s := ⟨i - (k + 1), by omega⟩
      have hs : s < l := by omega
      obtain ⟨t, rfl⟩ : ∃ t, j = k + 1 + t := ⟨j - (k + 1), by omega⟩
      have ht : t < l := by omega
      rw [bracketJoin_val_of_gt b c hs] at hjbc
      have := hc.2 ⟨s, hs⟩ ⟨t, ht⟩ (Fin.mk_le_mk.mpr (by omega)) (by grind)
      grind [bracketJoin_val_of_gt]

def bracketLeft {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : IsBracketing a) :
let k := Nat.find (isBracketing_exists_final a hB); Fin k → Fin k :=
fun ⟨i, hi⟩ ↦ ⟨a ⟨i, by grind⟩, by
  set k := Nat.find (isBracketing_exists_final a hB) with hk
  by_contra hik
  have hB2 := hB.2 ⟨i, by grind⟩ ⟨k, by grind⟩ (le_of_lt hi) (Nat.le_of_not_lt hik)
  obtain ⟨_, hspeck⟩ := Nat.find_spec (isBracketing_exists_final a hB)
  have hpi : (a ⟨i, by grind⟩).val = n := by grind
  have := Nat.find_min' (isBracketing_exists_final a hB) ⟨by omega, hpi⟩
  omega⟩

lemma bracketLeftIsBracketing {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : IsBracketing a) :
(IsBracketing (bracketLeft a hB)) := by
  constructor
  · intro ⟨i, hi⟩
    exact hB.1 ⟨i, by grind⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij hja
    exact hB.2 ⟨i, by grind⟩ ⟨j, by grind⟩ hij hja

def bracketRight {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : IsBracketing a) :
let k := Nat.find (isBracketing_exists_final a hB); Fin (n - k) → Fin (n - k) :=
fun ⟨i, hi⟩ ↦ ⟨a ⟨i + 1 + Nat.find (isBracketing_exists_final a hB), by grind⟩
  - (Nat.find (isBracketing_exists_final a hB) + 1), by omega⟩

lemma bracketRightIsBracketing {n : ℕ} (a : Fin (n + 1) → Fin (n + 1)) (hB : IsBracketing a) :
(IsBracketing (bracketRight a hB)) := by
  constructor
  · set k := Nat.find (isBracketing_exists_final a hB) with hk
    intro ⟨i, hi⟩
    simp [bracketRight]
    grind [hB.1 ⟨i + 1 + Nat.find (isBracketing_exists_final a hB), by omega⟩]
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij hja
    have := hB.1 ⟨i + 1 + Nat.find (isBracketing_exists_final a hB), by omega⟩
    have := hB.2 ⟨i + 1 + Nat.find (isBracketing_exists_final a hB), by omega⟩
      ⟨j + 1 + Nat.find (isBracketing_exists_final a hB), by omega⟩ (by grind)
      (by grind [bracketRight])
    grind [bracketRight]

lemma bracket_pair_heq {n K L : ℕ} (hKL : K = L)
    {b' : Fin K → Fin K} {c' : Fin (n - K) → Fin (n - K)}
    {b : Fin L → Fin L} {c : Fin (n - L) → Fin (n - L)}
    {h1 : (b', c') ∈ BracketingSequences K ×ˢ BracketingSequences (n - K)}
    {h2 : (b, c) ∈ BracketingSequences L ×ˢ BracketingSequences (n - L)}
    (hbb : ∀ (i : Fin K) (j : Fin L), i.val = j.val → (b' i).val = (b j).val)
    (hcc : ∀ (i : Fin (n - K)) (j : Fin (n - L)), i.val = j.val → (c' i).val = (c j).val) :
    HEq (⟨(b', c'), h1⟩ : ↥(BracketingSequences K ×ˢ BracketingSequences (n - K)))
      (⟨(b, c), h2⟩ : ↥(BracketingSequences L ×ˢ BracketingSequences (n - L))) := by
  subst hKL
  apply heq_of_eq
  apply Subtype.ext
  have hbe : b' = b := funext fun i => Fin.ext (hbb i i rfl)
  have hce : c' = c := funext fun i => Fin.ext (hcc i i rfl)
  simp [hbe, hce]

def bracketingSequences_succ (n : ℕ) :
BracketingSequences (n + 1) ≃ Σ k : Fin (n + 1),
BracketingSequences k ×ˢ BracketingSequences (n - k) :=
{ toFun := fun ⟨a, ha⟩ ↦ ⟨⟨Nat.find (isBracketing_exists_final a ((Finset.mem_filter.mp ha).2)),
    by grind⟩,
    ⟨(bracketLeft a ((Finset.mem_filter.mp ha).2), bracketRight a ((Finset.mem_filter.mp ha).2)),
    Finset.mem_product.mpr
    ⟨by simp only [mem_BracketingSequences];
        exact bracketLeftIsBracketing a ((Finset.mem_filter.mp ha).2),
     by simp only [mem_BracketingSequences];
        exact bracketRightIsBracketing a ((Finset.mem_filter.mp ha).2)⟩⟩⟩
  invFun := fun ⟨k, ⟨⟨b, c⟩, hbc⟩⟩ ↦
    have h : (k + 1 + (n - k)) = n + 1 := by omega
    have hb : b ∈ BracketingSequences k := by
      simpa [BracketingSequences] using (Finset.mem_product.mp hbc).1
    have hc : c ∈ BracketingSequences _ := by
      simpa [BracketingSequences] using (Finset.mem_product.mp hbc).2
    have hj : bracketJoin b c ∈ BracketingSequences (k.val + 1 + (n - k.val)) := by
      simp only [mem_BracketingSequences]
      exact bracketJoin_mem ((Finset.mem_filter.mp hb).2) ((Finset.mem_filter.mp hc).2)
    ⟨fun i => Fin.cast h (bracketJoin b c (Fin.cast h.symm i)), by
      simp only [mem_BracketingSequences]
      have hjB : IsBracketing (bracketJoin b c) := (Finset.mem_filter.mp hj).2
      constructor
      · intro i
        have hle := hjB.1 (Fin.cast h.symm i)
        simpa using hle
      · intro i j hij hja
        have hij' : Fin.cast h.symm i ≤ Fin.cast h.symm j := by
          rw [Fin.le_def] at hij ⊢
          exact hij
        have hja' :
          (Fin.cast h.symm j : Fin (k + 1 + (n - k))).val
          ≤ (bracketJoin b c (Fin.cast h.symm i)).val := by
            exact hja
        rw [Fin.le_def]
        exact hjB.2 (Fin.cast h.symm i) (Fin.cast h.symm j) hij' hja'⟩
  left_inv := by
    intro ⟨a, ha⟩
    have hB := (Finset.mem_filter.mp ha).2
    ext ⟨i, hi⟩
    set k := (Nat.find (isBracketing_exists_final a hB))
    rcases Nat.lt_trichotomy i k with h | rfl | h
    · grind [bracketJoin_val_of_lt _ _ h, bracketLeft, Fin.cast_mk]
    · simp only [Fin.cast_mk, Fin.val_cast]
      rw [bracketJoin_val_mid]
      grind
    · have hi' : (⟨i, hi⟩ : Fin (n + 1)) = Fin.cast (by omega) (⟨k + 1 + (i - (k + 1)), by omega⟩ :
                Fin (k + 1 + (n - k))) := by grind
      rw [hi']
      simp only [Fin.cast_mk, Fin.val_cast]
      rw [bracketJoin_val_of_gt _ _ (by omega)]
      grind [bracketRight, hB.1 ⟨i - (k + 1) + 1 + k, by omega⟩]
  right_inv := by
    intro ⟨k,⟨b,c⟩,hbc⟩
    simp only [Sigma.mk.injEq, Order.lt_add_one_iff]
    constructor
    · apply le_antisymm
      · apply Nat.find_min'
        constructor
        · change bracketJoin b c ⟨k, by omega⟩ = n
          rw [bracketJoin_val_mid]
          omega
        · exact Fin.is_le k
      · refine (Nat.le_find_iff _ _).mpr ?_
        intro m hmk ⟨hmn, hval⟩
        change (bracketJoin b c ⟨m, by omega⟩) = n at hval
        rw [bracketJoin_val_of_lt b c hmk] at hval
        omega
    · apply bracket_pair_heq
      · apply le_antisymm
        · apply Nat.find_min'
          constructor
          · change bracketJoin b c ⟨k, by omega⟩ = n
            rw [bracketJoin_val_mid]
            omega
        · refine (Nat.le_find_iff _ _).mpr ?_
          intro m hmk ⟨hmn, hval⟩
          change (bracketJoin b c ⟨m, by omega⟩) = n at hval
          rw [bracketJoin_val_of_lt b c hmk] at hval
          omega
      · intro i j hij
        simp only [Fin.cast_mk, Fin.val_cast, bracketLeft]
        simp_rw [hij]
        rw [bracketJoin_val_of_lt b c _]
      · intro i j hij
        simp only [Fin.cast_mk, Fin.val_cast, bracketRight, Order.lt_add_one_iff]
        simp_rw [hij]
        generalize_proofs _ pf2 _
        have hK : Nat.find pf2 = (k : ℕ) := by
          apply le_antisymm
          · exact Nat.find_min' pf2 ⟨Nat.lt_succ_iff.mp k.isLt, by rw [bracketJoin_val_mid]; omega⟩
          · refine (Nat.le_find_iff _ _).mpr ?_
            rintro m hmk ⟨hmn, hval⟩
            rw [bracketJoin_val_of_lt b c hmk] at hval
            have := (b ⟨m, hmk⟩).isLt
            omega
        grind [bracketJoin_val_of_gt b c j.isLt]
      }

theorem bracketingSequences_card (n : ℕ) : (BracketingSequences n).card = catalan n := by
  induction n using Nat.case_strong_induction_on with
  | hz => rw [catalan_zero]; decide
  | hi n ih =>
    grind [Fintype.card_congr (bracketingSequences_succ n), Fintype.card_sigma, Finset.card_product,
    Fintype.card_coe, catalan_succ]
