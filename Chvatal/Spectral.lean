import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Tactic

open scoped BigOperators
open Matrix

namespace Chvatal

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Independent eigenvectors bound the multiplicity of an eigenvalue. -/
lemma eigenvector_card_le (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (v : κ → ι → ℝ) (hv : LinearIndependent ℝ v) (t : ℝ)
    (he : ∀ k, M *ᵥ v k = t • v k) :
    Fintype.card κ ≤ (Finset.univ.filter fun i => hM.eigenvalues i = t).card := by
  classical
  let w : κ → Module.End.eigenspace (Matrix.toLin' M) t :=
    fun k => ⟨v k, by simpa [Module.End.mem_eigenspace_iff] using he k⟩
  have hw : LinearIndependent ℝ w := hv.of_comp (Submodule.subtype _)
  have h := hw.fintype_card_le_finrank.trans
    (LinearMap.finrank_eigenspace_le (Matrix.toLin' M) t)
  rw [Matrix.charpoly_toLin', ← Polynomial.count_roots,
    hM.roots_charpoly_eq_eigenvalues, Multiset.count_map] at h
  simpa [Function.comp_def, eq_comm] using h

lemma trace_square (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    (M * M).trace = ∑ i, hM.eigenvalues i ^ 2 := by
  conv_lhs => rw [hM.spectral_theorem]
  rw [← map_mul, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]

/-- The squared Frobenius norm counts independent +1 and -1 eigenvectors. -/
lemma spectral_lower (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (p q : κ → ι → ℝ) (hp : LinearIndependent ℝ p) (hq : LinearIndependent ℝ q)
    (hep : ∀ k, M *ᵥ p k = (-1 : ℝ) • p k)
    (heq : ∀ k, M *ᵥ q k = q k) :
    2 * (Fintype.card κ : ℝ) ≤ ∑ i, ∑ j, M i j ^ 2 := by
  classical
  have hminus := eigenvector_card_le M hM p hp (-1) hep
  have hplus := eigenvector_card_le M hM q hq 1 (by simpa using heq)
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
  have hfrob : (M * M).trace = ∑ i, ∑ j, M i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hsym : M j i = M i j := by
      simpa using congrArg (fun A : Matrix ι ι ℝ => A i j) hM
    rw [hsym, pow_two]
  rw [← hfrob, trace_square M hM]
  exact le_trans (by exact_mod_cast (by omega :
    2 * Fintype.card κ ≤
      (Finset.univ.filter fun i => hM.eigenvalues i = -1).card +
      (Finset.univ.filter fun i => hM.eigenvalues i = 1).card)) hcount

end Chvatal
