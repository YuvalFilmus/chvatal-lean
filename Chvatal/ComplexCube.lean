import Chvatal.Cube
import Mathlib.Data.Complex.BigOperators

/-! Complex Fourier transforms and flattened block Fourier multipliers on the Boolean cube. -/

open scoped BigOperators symmDiff
open Finset Matrix
noncomputable section
namespace Chvatal
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

def complexWalsh (f : Finset α → ℂ) (S : Finset α) : ℂ :=
  ∑ X, (chi S X : ℂ) * f X

def complexFourier (f : Finset α → ℂ) (S : Finset α) : ℂ :=
  complexWalsh f S / Fintype.card (Finset α)

lemma complexWalsh_twice (f : Finset α → ℂ) (X : Finset α) :
    complexWalsh (complexWalsh f) X = (Fintype.card (Finset α) : ℂ) * f X := by
  classical
  simp only [complexWalsh, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  have hh (Y : Finset α) :
      (∑ S : Finset α, chi X S * chi S Y) =
        if X = Y then (Fintype.card (Finset α) : ℝ) else 0 := by
    simpa only [chi_comm X] using chi_orthogonal X Y
  simp_rw [hh]
  simp only [apply_ite Complex.ofReal, Complex.ofReal_natCast, Complex.ofReal_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma complexFourier_re (f : Finset α → ℂ) (S : Finset α) :
    (complexFourier f S).re = fourier (fun X => (f X).re) S := by
  unfold complexFourier fourier
  rw [show (Fintype.card (Finset α) : ℂ) = ((Fintype.card (Finset α) : ℝ) : ℂ) by simp,
    Complex.div_ofReal_re]
  simp [complexWalsh, walsh]

lemma complexFourier_im (f : Finset α → ℂ) (S : Finset α) :
    (complexFourier f S).im = fourier (fun X => (f X).im) S := by
  unfold complexFourier fourier
  rw [show (Fintype.card (Finset α) : ℂ) = ((Fintype.card (Finset α) : ℝ) : ℂ) by simp,
    Complex.div_ofReal_im]
  simp [complexWalsh, walsh]

lemma complexFourier_parseval (f : Finset α → ℂ) :
    (∑ T, Complex.normSq (complexFourier f T)) =
      (∑ T, Complex.normSq (f T)) / Fintype.card (Finset α) := by
  simp only [Complex.normSq_apply, complexFourier_re, complexFourier_im, ← pow_two,
    Finset.sum_add_distrib]
  rw [fourier_parseval, fourier_parseval, add_div]

lemma complexWalsh_real_mul (f : Finset α → ℝ) (z : ℂ) (T : Finset α) :
    complexWalsh (fun X => (f X : ℂ) * z) T = (walsh f T : ℂ) * z := by
  simp only [complexWalsh, walsh, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul, mul_assoc]

lemma complex_kernel_action (h f : Finset α → ℂ) (A : Finset α) :
    (∑ B, complexFourier h (A ∆ B) * f B) =
      complexWalsh (fun T => h T * complexWalsh f T) A / Fintype.card (Finset α) := by
  simp only [complexFourier, complexWalsh]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro B hB
  rw [← chi_mul, chi_comm B T, chi_comm A T, Complex.ofReal_mul]
  ring

def blockFourier (h : Finset α → Matrix β β ℂ) (T : Finset α) : Matrix β β ℂ :=
  fun i j => complexFourier (fun X => h X i j) T

def blockKernel (h : Finset α → Matrix β β ℂ) :
    Matrix (Finset α × β) (Finset α × β) ℂ :=
  fun A B => blockFourier h (A.1 ∆ B.1) A.2 B.2

lemma blockKernel_action (h : Finset α → Matrix β β ℂ)
    (f : Finset α × β → ℂ) (A : Finset α) (i : β) :
    (blockKernel h *ᵥ f) (A, i) =
      complexWalsh (fun T => ∑ j, h T i j * complexWalsh (fun B => f (B,j)) T) A /
        Fintype.card (Finset α) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockKernel, blockFourier]
  rw [Finset.sum_comm]
  simp_rw [complex_kernel_action]
  simp only [complexWalsh, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]

lemma blockKernel_eigen (h : Finset α → Matrix β β ℂ)
    (f : Finset α × β → ℂ) (t : ℂ)
    (he : ∀ T i, (∑ j, h T i j * complexWalsh (fun B => f (B,j)) T) =
      t * complexWalsh (fun B => f (B,i)) T) :
    blockKernel h *ᵥ f = t • f := by
  ext ⟨A,i⟩
  rw [blockKernel_action]
  simp_rw [he]
  simp only [complexWalsh, mul_left_comm (chi A _ : ℂ) t, ← Finset.mul_sum]
  change t * complexWalsh (complexWalsh (fun B => f (B,i))) A / _ = t * f (A,i)
  rw [complexWalsh_twice]
  have hn : (Fintype.card (Finset α) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
end Chvatal
