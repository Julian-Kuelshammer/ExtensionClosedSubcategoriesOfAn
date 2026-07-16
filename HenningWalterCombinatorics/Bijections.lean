import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod

/-! # Bijections between different conventions for the indexing set of intervall modules.

-/

open Finset

def intervall_modules_convention (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.product (range (n+2)) (range (n+2))).filter
    (fun p => 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ n+1)

def higher_nakayama_convention (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.product (range (n+1)) (range (n+1))).filter
    (fun p => p.1 ≤ p.2 ∧ p.2 ≤ n)

def mazorchuk_convention (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.product (range (n+1)) (range (n+1))).filter
    (fun p => p.1 + p.2 ≤ n)

lemma mem_intervall_modules_convention_iff (n : ℕ) (p : ℕ × ℕ) :
  p ∈ intervall_modules_convention n ↔
    1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ n + 1 := by
  simp only [intervall_modules_convention, product_eq_sprod, mem_filter, mem_product, mem_range]
  omega

lemma mem_higher_nakayama_convention_iff (n : ℕ) (p : ℕ × ℕ) :
  p ∈ higher_nakayama_convention n ↔
    p.1 ≤ p.2 ∧ p.2 ≤ n := by
  simp only [higher_nakayama_convention, product_eq_sprod, mem_filter, mem_product, mem_range]
  omega

lemma mem_mazorchuk_convention_iff (n : ℕ) (p : ℕ × ℕ) :
  p ∈ mazorchuk_convention n ↔
    p.1 + p.2 ≤ n := by
  simp only [mazorchuk_convention, product_eq_sprod, mem_filter, mem_product, mem_range]
  omega

def intervall_equiv_nakayama (n : ℕ) :
  ↥ (intervall_modules_convention n) ≃ ↥ (higher_nakayama_convention n) :=
    { toFun := fun p ↦ ⟨(n + 1 - p.1.2, n + 1 - p.1.1), by
        rcases p with ⟨p,hp⟩
        rw [mem_intervall_modules_convention_iff] at hp
        simp only [higher_nakayama_convention, product_eq_sprod, mem_filter, mem_product,
          mem_range]
        omega⟩
      invFun := fun p ↦ ⟨(n + 1 - p.1.2, n + 1 - p.1.1), by
        rcases p with ⟨p,hp⟩
        rw [mem_higher_nakayama_convention_iff] at hp
        simp only [intervall_modules_convention, product_eq_sprod, mem_filter, mem_product,
          mem_range]
        omega⟩
      left_inv := by
        rintro ⟨p, hp⟩
        rw [mem_intervall_modules_convention_iff] at hp
        simp only [Subtype.mk.injEq]
        ext <;>
        omega
      right_inv := by
        rintro ⟨p, hp⟩
        rw [mem_higher_nakayama_convention_iff] at hp
        simp only [Subtype.mk.injEq]
        ext <;>
        omega
    }

def nakayama_equiv_mazorchuk (n : ℕ) :
  ↥ (higher_nakayama_convention n) ≃ ↥ (mazorchuk_convention n) :=
  { toFun := fun p ↦ ⟨(p.1.1, n - p.1.2), by
      rcases p with ⟨p,hp⟩
      rw [mem_higher_nakayama_convention_iff] at hp
      simp only [mazorchuk_convention, product_eq_sprod, mem_filter, mem_product, mem_range]
      omega⟩
    invFun := fun p ↦ ⟨(p.1.1, n - p.1.2), by
      rcases p with ⟨p,hp⟩
      rw [mem_mazorchuk_convention_iff] at hp
      simp [higher_nakayama_convention]
      omega⟩
    left_inv := by
      rintro ⟨p, hp⟩
      rw [mem_higher_nakayama_convention_iff] at hp
      simp only [Subtype.mk.injEq]
      ext <;>
      omega
    right_inv := by
      rintro ⟨p, hp⟩
      rw [mem_mazorchuk_convention_iff] at hp
      simp only [Subtype.mk.injEq]
      ext <;>
      omega
  }
