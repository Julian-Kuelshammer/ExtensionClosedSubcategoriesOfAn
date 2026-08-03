import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod

open Finset

def higher_nakayama_convention (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.product (range (n+1)) (range (n+1))).filter
    (fun p => p.1 ≤ p.2 ∧ p.2 ≤ n)

lemma mem_higher_nakayama_convention_iff (n : ℕ) (p : ℕ × ℕ) :
  p ∈ higher_nakayama_convention n ↔
    p.1 ≤ p.2 ∧ p.2 ≤ n := by
  simp only [higher_nakayama_convention, product_eq_sprod, mem_filter, mem_product, mem_range]
  omega

/-- A combinatorial condition for two interval modules `p` and `q` to have non-zero `Ext^1(p,q)`. -/
def ext_interlace {n : ℕ} (p q : higher_nakayama_convention n) : Prop :=
q.1.1 + 1 ≤ p.1.1 ∧ p.1.1 ≤ q.1.2 + 1 ∧ q.1.2 + 1 ≤ p.1.2

/-- The objects of the form (0,i) are projective. -/
lemma proj_of_fst_eq_zero {n : ℕ} (p q : higher_nakayama_convention n) (hproj : p.1.1 = 0) :
¬ ext_interlace p q := by
  grind [ext_interlace]

/-- The objects of the form (i,n) are injective. -/
lemma inj_of_snd_eq_top {n : ℕ} (p q : higher_nakayama_convention n) (hinj : q.1.2 = n) :
¬ ext_interlace p q := by
  grind [ext_interlace, higher_nakayama_convention]

/-- Let `p=(a,b)` and `q=(c,d)` be such that `Ext^1(p,q)≠0`. Then, there is a short exact sequence
`0 → (c,d) → (c,b) ⊕ (a,d) → (a,b) → 0`, where `(c,b)` is a longer intervall, which we call
`long_extension`. -/
def long_extension {n : ℕ} {p q : higher_nakayama_convention n} (hpq : ext_interlace p q) :
higher_nakayama_convention n := by
  refine ⟨(q.1.1, p.1.2), ?_⟩
  rcases p with ⟨⟨a,b⟩,hp⟩
  rw [mem_higher_nakayama_convention_iff] at hp ⊢
  rw [ext_interlace] at hpq
  grind

/-- Let `p=(a,b)` and `q=(c,d)` be such that `Ext^1(p,q)≠0`. Then, there is a short exact sequence
`0 → (c,d) → (c,b) ⊕ (a,d) → (a,b) → 0`, where `(a,d)` is a shorter intervall, which only exists if
`a ≤ d` (otherwise in the literature it is treated as `0`). -/
def short_extension {n : ℕ} {p q : higher_nakayama_convention n} (hshort : p.1.1 ≤ q.1.2) :
higher_nakayama_convention n := by
  refine ⟨⟨p.1.1, q.1.2⟩, ?_⟩
  rcases q with ⟨⟨c,d⟩,hq⟩
  rw [mem_higher_nakayama_convention_iff] at hq ⊢
  grind

/-- A symmetrised version of `ext_interlace`, which includes both `Ext^1(p,q)≠0` and
`Ext^1(q,p) ≠ 0` as well as the cases where `p` and `q` are contained in each other, see
`weak_interlace_cases`. -/
def weak_ext_interlace {n : ℕ} (p q : higher_nakayama_convention n) : Prop :=
max p.1.1 q.1.1 ≤ 1 + min p.1.2 q.1.2

def contains {n : ℕ} (p q : higher_nakayama_convention n) : Prop :=
  (p.1.1 ≤ q.1.1 ∧ q.1.2 ≤ p.1.2)

lemma weak_ext_interlace_comm {n : ℕ} (p q : higher_nakayama_convention n) :
    weak_ext_interlace p q ↔ weak_ext_interlace q p := by
  simp [weak_ext_interlace, max_comm, min_comm]

lemma weak_interlace_cases {n : ℕ} {p q : higher_nakayama_convention n}
(hpq : weak_ext_interlace p q) :
  ext_interlace p q ∨ ext_interlace q p ∨ contains p q ∨ contains q p := by
  rw [weak_ext_interlace] at hpq
  simp only [ext_interlace, contains]
  omega

lemma weak_interlace_of_interlace {n : ℕ}
{p q : higher_nakayama_convention n} (hpq : ext_interlace p q) : weak_ext_interlace p q := by
  rw [weak_ext_interlace]
  rw [ext_interlace] at hpq
  omega

lemma weak_interlace_of_interlace_rev {n : ℕ} {p q : higher_nakayama_convention n}
(hqp : ext_interlace q p) : weak_ext_interlace p q := by
  rw [weak_ext_interlace]
  rw [ext_interlace] at hqp
  omega

lemma weak_short_of_short {n : ℕ} {p q : higher_nakayama_convention n} (hpq : ext_interlace p q)
(hshort : p.1.1 ≤ q.1.2) : max p.1.1 q.1.1 ≤ min p.1.2 q.1.2 := by
  rw [ext_interlace] at hpq
  omega

lemma weak_short_of_short_rev {n : ℕ} {p q : higher_nakayama_convention n} (hqp : ext_interlace q p)
(hshort : q.1.1 ≤ p.1.2) : max p.1.1 q.1.1 ≤ min p.1.2 q.1.2 := by
  rw [ext_interlace] at hqp
  omega

lemma short_of_weak_short {n : ℕ} {p q : higher_nakayama_convention n}
(h : max p.1.1 q.1.1 ≤ min p.1.2 q.1.2) : p.1.1 ≤ q.1.2 := by omega

lemma short_of_weak_short_rev {n : ℕ} {p q : higher_nakayama_convention n}
(h : max p.1.1 q.1.1 ≤ min p.1.2 q.1.2) : q.1.1 ≤ p.1.2 := by omega

def weak_long_extension {n : ℕ} {p q : higher_nakayama_convention n}
(hpq : weak_ext_interlace p q) : higher_nakayama_convention n := by
  refine ⟨(min p.1.1 q.1.1, max p.1.2 q.1.2), ?_⟩
  rcases p with ⟨⟨a,b⟩,hp⟩
  rcases q with ⟨⟨c,d⟩,hq⟩
  rw [mem_higher_nakayama_convention_iff] at hp hq ⊢
  rw [weak_ext_interlace] at hpq
  grind

def weak_short_extension {n : ℕ} {p q : higher_nakayama_convention n}
(hshort : max p.1.1 q.1.1 ≤ min p.1.2 q.1.2) : higher_nakayama_convention n := by
  refine ⟨⟨max p.1.1 q.1.1, min p.1.2 q.1.2⟩, ?_⟩
  rcases q with ⟨⟨c,d⟩,hq⟩
  rw [mem_higher_nakayama_convention_iff] at hq ⊢
  grind

lemma weak_long_extension_of_contains {n : ℕ} {p q : higher_nakayama_convention n}
(hpq : weak_ext_interlace p q) (h : contains p q) : weak_long_extension hpq = p := by
  simp only [weak_long_extension, contains] at h ⊢
  grind

lemma weak_long_extension_of_contains_rev {n : ℕ} {p q : higher_nakayama_convention n}
  (hpq : weak_ext_interlace p q) (h : contains q p) : weak_long_extension hpq = q := by
  simpa [weak_long_extension, max_comm, min_comm] using
  (weak_long_extension_of_contains ((weak_ext_interlace_comm p q).mp hpq) h)

lemma weak_short_extension_of_contains {n : ℕ} {p q : higher_nakayama_convention n}
  (hshort : max p.1.1 q.1.1 ≤ min p.1.2 q.1.2) (h : contains p q) :
  weak_short_extension hshort = q := by
  simp only [contains] at h
  grind [weak_short_extension]

lemma weak_short_extension_of_contains_rev {n : ℕ}
  {p q : higher_nakayama_convention n} (hshort : max p.1.1 q.1.1 ≤ min p.1.2 q.1.2)
  (h : contains q p) : weak_short_extension hshort = p := by
  simp only [contains] at h
  grind [weak_short_extension]

lemma long_extension_eq_weak_long_extension {n : ℕ} {p q : higher_nakayama_convention n}
  (hpq : ext_interlace p q) :
  long_extension hpq = weak_long_extension (weak_interlace_of_interlace hpq) := by
  rw [ext_interlace] at hpq
  grind [long_extension, weak_long_extension]

lemma long_extension_eq_weak_long_extension_rev {n : ℕ} {p q : higher_nakayama_convention n}
  (hqp : ext_interlace q p) :
  long_extension hqp = weak_long_extension (weak_interlace_of_interlace_rev hqp) := by
  rw [ext_interlace] at hqp
  grind [long_extension, weak_long_extension]

lemma short_extension_eq_weak_short_extension {n : ℕ} {p q : higher_nakayama_convention n}
  (hpq : ext_interlace p q) (hshort : p.1.1 ≤ q.1.2) :
  short_extension hshort = weak_short_extension (weak_short_of_short hpq hshort) := by
  rw [ext_interlace] at hpq
  grind [short_extension, weak_short_extension]

lemma short_extension_eq_weak_short_extension_rev {n : ℕ} {p q : higher_nakayama_convention n}
  (hqp : ext_interlace q p) (hshort : q.1.1 ≤ p.1.2) :
  short_extension hshort = weak_short_extension (weak_short_of_short_rev hqp hshort) := by
  rw [ext_interlace] at hqp
  grind [short_extension, weak_short_extension]

def strong_ext_closed {n : ℕ} (Y : Finset (higher_nakayama_convention n)) : Prop :=
  ∀ p ∈ Y, ∀ q ∈ Y, ∀ hpq : ext_interlace p q,
      long_extension hpq ∈ Y ∧ (∀ hshort : p.1.1 ≤ q.1.2, short_extension hshort ∈ Y)

def weak_ext_closed {n : ℕ} (Y : Finset (higher_nakayama_convention n)) : Prop :=
  ∀ p ∈ Y, ∀ q ∈ Y, ∀ hpq : weak_ext_interlace p q, weak_long_extension hpq ∈ Y ∧
      (∀ hshort : max p.1.1 q.1.1 ≤ min p.1.2 q.1.2, weak_short_extension hshort ∈ Y)

lemma strong_ext_closed_iff_weak_ext_closed {n : ℕ} (Y : Finset (higher_nakayama_convention n)) :
  strong_ext_closed Y ↔ weak_ext_closed Y := by
  rw [strong_ext_closed, weak_ext_closed]
  constructor
  · intro hstrong p hp q hq hpq
    rcases weak_interlace_cases hpq with hpq' | hpq' | hpq' | hpq'
    · -- The case `ext_interlace p q`
      constructor
      · rw [← long_extension_eq_weak_long_extension hpq']
        exact (hstrong p hp q hq hpq').1
      · intro hshort
        rw [← short_extension_eq_weak_short_extension hpq' (short_of_weak_short hshort)]
        exact (hstrong p hp q hq hpq').2 (short_of_weak_short hshort)
    · -- The case `ext_interlace q p`
      constructor
      · rw [← long_extension_eq_weak_long_extension_rev hpq']
        exact (hstrong q hq p hp hpq').1
      · intro hshort
        rw [← short_extension_eq_weak_short_extension_rev hpq' (short_of_weak_short_rev hshort)]
        exact (hstrong q hq p hp hpq').2 (short_of_weak_short_rev hshort)
    · -- The case `contains p q`
      constructor
      · rw [weak_long_extension_of_contains hpq hpq']
        exact hp
      · intro hshort
        rw [weak_short_extension_of_contains hshort hpq']
        exact hq
    · -- The case `contains q p`
      constructor
      · rw [weak_long_extension_of_contains_rev hpq hpq']
        exact hq
      · intro hshort
        rw [weak_short_extension_of_contains_rev hshort hpq']
        exact hp
  · intro hweak p hp q hq hpq
    constructor
    · rw [long_extension_eq_weak_long_extension hpq]
      exact (hweak p hp q hq (weak_interlace_of_interlace hpq)).1
    · intro hshort
      rw [short_extension_eq_weak_short_extension hpq hshort]
      exact (hweak p hp q hq (weak_interlace_of_interlace hpq)).2 (weak_short_of_short hpq hshort)
