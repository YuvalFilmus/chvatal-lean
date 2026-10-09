import Chvatal.Spectral
import Mathlib.Data.Complex.Basic

/-! Hermitian complex matrices: eigenvalue multiplicities and squared Frobenius energy. -/

open scoped BigOperators
open Matrix
noncomputable section
namespace Chvatal
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

lemma complex_eigenvector_card_le (M : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (v : κ → ι → ℂ) (hv : LinearIndependent ℂ v) (t : ℝ)
    (he : ∀ k, M *ᵥ v k = (t : ℂ) • v k) :
    Fintype.card κ ≤ (Finset.univ.filter fun i => hM.eigenvalues i = t).card := by
  classical
  let w : κ → Module.End.eigenspace (Matrix.toLin' M) (t : ℂ) :=
    fun k => ⟨v k, by simpa [Module.End.mem_eigenspace_iff] using he k⟩
  have hw : LinearIndependent ℂ w := hv.of_comp (Submodule.subtype _)
  have h := hw.fintype_card_le_finrank.trans
    (LinearMap.finrank_eigenspace_le (Matrix.toLin' M) (t : ℂ))
  rw [Matrix.charpoly_toLin', ← Polynomial.count_roots,
    hM.roots_charpoly_eq_eigenvalues, Multiset.count_map] at h
  simpa [Function.comp_def, eq_comm] using h

lemma complex_trace_square (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    (M * M).trace.re = ∑ i, hM.eigenvalues i ^ 2 := by
  have ht : (M * M).trace = ∑ i, (hM.eigenvalues i : ℂ) ^ 2 := by
    conv_lhs => rw [hM.spectral_theorem]
    rw [← map_mul, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
    simp [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]
  rw [ht, Complex.re_sum]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

omit [DecidableEq ι] in
lemma hermitian_frobenius (M : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    (M * M).trace.re = ∑ i, ∑ j, Complex.normSq (M i j) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hsym : M j i = star (M i j) := by
    have hh := congrArg (fun A : Matrix ι ι ℂ => A j i) hM
    simpa using hh.symm
  rw [hsym]
  simp [Complex.mul_conj]

lemma complex_spectral_lower (M : Matrix ι ι ℂ) (hM : M.IsHermitian)
    (p q : κ → ι → ℂ) (hp : LinearIndependent ℂ p) (hq : LinearIndependent ℂ q)
    (hep : ∀ k, M *ᵥ p k = (-1 : ℂ) • p k)
    (heq : ∀ k, M *ᵥ q k = q k) :
    2 * (Fintype.card κ : ℝ) ≤ ∑ i, ∑ j, Complex.normSq (M i j) := by
  classical
  have hminus := complex_eigenvector_card_le M hM p hp (-1) (by simpa using hep)
  have hplus := complex_eigenvector_card_le M hM q hq 1 (by simpa using heq)
  have hcount : ((Finset.univ.filter fun i => hM.eigenvalues i = -1).card : ℝ) +
      ((Finset.univ.filter fun i => hM.eigenvalues i = 1).card : ℝ) ≤
      ∑ i, hM.eigenvalues i ^ 2 := by
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    by_cases h1 : hM.eigenvalues i = -1
    · norm_num [h1]
    by_cases h2 : hM.eigenvalues i = 1
    · norm_num [h2]
    simpa [h1, h2] using sq_nonneg (hM.eigenvalues i)
  rw [← hermitian_frobenius M hM, complex_trace_square M hM]
  exact le_trans (by exact_mod_cast (by omega :
    2 * Fintype.card κ ≤
      (Finset.univ.filter fun i => hM.eigenvalues i = -1).card +
      (Finset.univ.filter fun i => hM.eigenvalues i = 1).card)) hcount
end Chvatal
