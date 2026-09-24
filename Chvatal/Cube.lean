import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

open scoped BigOperators symmDiff
open Finset Matrix

noncomputable section

namespace Chvatal

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Real Walsh character of the finite Boolean cube. -/
def chi (S T : Finset α) : ℝ :=
  ∏ i : α, if i ∈ S ∧ i ∈ T then -1 else 1

lemma chi_comm (S T : Finset α) : chi S T = chi T S := by
  simp only [chi, and_comm]

@[simp] lemma chi_empty (T : Finset α) : chi (∅ : Finset α) T = 1 := by simp [chi]
@[simp] lemma chi_empty_right (S : Finset α) : chi S ∅ = 1 := by rw [chi_comm]; simp

lemma chi_mul (S T X : Finset α) : chi S X * chi T X = chi (S ∆ T) X := by
  rw [chi, chi, ← Finset.prod_mul_distrib, chi]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> by_cases hX : i ∈ X <;>
    simp [hS, hT, hX, Finset.mem_symmDiff]

lemma chi_mul_right (S X Y : Finset α) : chi S X * chi S Y = chi S (X ∆ Y) := by
  simpa only [chi_comm] using chi_mul X Y S

@[simp] lemma chi_sq (S T : Finset α) : chi S T ^ 2 = 1 := by
  rw [pow_two, chi_mul]; simp

lemma chi_singleton (S : Finset α) (i : α) :
    chi S {i} = if i ∈ S then -1 else 1 := by
  unfold chi
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

noncomputable def toggle (T : Finset α) : Finset α ≃ Finset α :=
  { toFun := fun X => X ∆ T
    invFun := fun X => X ∆ T
    left_inv := fun X => symmDiff_symmDiff_cancel_right T X
    right_inv := fun X => symmDiff_symmDiff_cancel_right T X }

lemma sum_toggle (T : Finset α) (f : Finset α → ℝ) :
    (∑ X : Finset α, f (X ∆ T)) = ∑ X, f X := (toggle T).sum_comp f

lemma sum_chi (S : Finset α) :
    (∑ X : Finset α, chi S X) = if S = ∅ then (Fintype.card (Finset α) : ℝ) else 0 := by
  classical
  by_cases hS : S = ∅
  · simp [hS]
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  have h := sum_toggle {i} (chi S)
  simp_rw [← chi_mul_right, chi_singleton, if_pos hi, mul_neg_one, Finset.sum_neg_distrib] at h
  simp only [if_neg hS]
  linarith

lemma chi_orthogonal (X Y : Finset α) :
    (∑ S : Finset α, chi S X * chi S Y) =
      if X = Y then (Fintype.card (Finset α) : ℝ) else 0 := by
  simp_rw [chi_mul_right, chi_comm _ (X ∆ Y)]
  rw [sum_chi]
  simp

/-- Unnormalized Walsh transform. -/
def walsh (f : Finset α → ℝ) (S : Finset α) : ℝ := ∑ X, chi S X * f X

lemma walsh_twice (f : Finset α → ℝ) (X : Finset α) :
    walsh (walsh f) X = (Fintype.card (Finset α) : ℝ) * f X := by
  classical
  simp only [walsh, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  have hh (Y : Finset α) :
      (∑ S : Finset α, chi X S * chi S Y) =
        if X = Y then (Fintype.card (Finset α) : ℝ) else 0 := by
    simpa only [chi_comm X] using chi_orthogonal X Y
  simp_rw [hh]
  simp

lemma walsh_adjoint (f g : Finset α → ℝ) :
    (∑ X, walsh f X * g X) = ∑ X, f X * walsh g X := by
  simp only [walsh, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro X hX
  apply Finset.sum_congr rfl
  intro Y hY
  rw [chi_comm]
  ring

lemma walsh_parseval (f : Finset α → ℝ) :
    (∑ X, walsh f X ^ 2) = (Fintype.card (Finset α) : ℝ) * ∑ X, f X ^ 2 := by
  simp_rw [pow_two]
  rw [walsh_adjoint]
  simp_rw [walsh_twice]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X hX
  ring

/-- Normalized Fourier coefficient. -/
def fourier (f : Finset α → ℝ) (S : Finset α) : ℝ :=
  walsh f S / Fintype.card (Finset α)

omit [DecidableEq α] in
lemma cube_card_pos : (0 : ℝ) < Fintype.card (Finset α) := by
  exact_mod_cast Fintype.card_pos

lemma fourier_parseval (f : Finset α → ℝ) :
    (∑ X, fourier f X ^ 2) = (∑ X, f X ^ 2) / Fintype.card (Finset α) := by
  simp only [fourier, div_pow, ← Finset.sum_div]
  rw [walsh_parseval]
  have hn := cube_card_pos (α := α)
  field_simp

/-- The convolution matrix of a scalar Fourier multiplier. -/
def kernel (h : Finset α → ℝ) : Matrix (Finset α) (Finset α) ℝ :=
  fun A B => fourier h (A ∆ B)

lemma kernel_action (h f : Finset α → ℝ) (A : Finset α) :
    (kernel h *ᵥ f) A = walsh (fun T => h T * walsh f T) A /
      Fintype.card (Finset α) := by
  simp only [kernel, Matrix.mulVec, dotProduct, fourier, walsh]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro B hB
  rw [← chi_mul, chi_comm B T, chi_comm A T]
  ring

lemma kernel_eigen (h f : Finset α → ℝ) (t : ℝ)
    (he : ∀ T, h T * walsh f T = t * walsh f T) :
    kernel h *ᵥ f = t • f := by
  ext A
  rw [kernel_action]
  rw [show (fun T => h T * walsh f T) = (fun T => t * walsh f T) from funext he]
  rw [walsh]
  simp only [mul_left_comm (chi A _) t, ← Finset.mul_sum]
  change t * walsh (walsh f) A / _ = t * f A
  rw [walsh_twice]
  have hn := cube_card_pos (α := α)
  field_simp

/-- Indicator of the principal downset generated by A. -/
def downIndicator (A X : Finset α) : ℝ := if X ⊆ A then 1 else 0

def signedIndicator (A X : Finset α) : ℝ := chi Finset.univ X * downIndicator A X

omit [Fintype α] in
lemma downIndicator_toggle {A : Finset α} {i : α} (hi : i ∈ A) (X : Finset α) :
    downIndicator A (X ∆ {i}) = downIndicator A X := by
  have hh : X ∆ {i} ⊆ A ↔ X ⊆ A := by
    constructor
    · intro h x hx
      by_cases hxi : x = i
      · simpa [hxi] using hi
      · exact h (by simp [Finset.mem_symmDiff, hx, hxi])
    · intro h x hx
      simp only [Finset.mem_symmDiff, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · exact h hx.1
      · simpa [hx.1] using hi
  simp [downIndicator, hh]

lemma walsh_downIndicator_zero (A T : Finset α) (h : ¬ Disjoint A T) :
    walsh (downIndicator A) T = 0 := by
  obtain ⟨i, hiA, hiT⟩ := Finset.not_disjoint_iff.mp h
  have hh := sum_toggle {i} (fun X => chi T X * downIndicator A X)
  simp_rw [downIndicator_toggle hiA, ← chi_mul_right, chi_singleton,
    if_pos hiT, mul_neg_one, neg_mul, Finset.sum_neg_distrib] at hh
  unfold walsh
  linarith

lemma walsh_signedIndicator (A T : Finset α) :
    walsh (signedIndicator A) T = walsh (downIndicator A) (T ∆ Finset.univ) := by
  simp only [walsh, signedIndicator, ← mul_assoc, chi_mul]

end Chvatal
