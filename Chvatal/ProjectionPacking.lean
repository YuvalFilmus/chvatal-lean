import Chvatal.ComplexCube
import Chvatal.ComplexSpectral
import Chvatal.Main
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace

/-! # Projection packings of downset Kneser graphs

Theorem 3 of Ellis, Filmus, and Friedgut, arXiv:2609.28404v2, Section 4.
The public theorem `projection_packing` gives both the bound for arbitrary complex
subspace assignments and its attainment by a largest star in every positive dimension.
-/

open scoped BigOperators symmDiff
open Finset Matrix Module
noncomputable section
namespace Chvatal
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Orthogonality on disjoint sets, including the loop at the empty set. -/
def IsProjectionPacking (D : Finset (Finset α))
    (U : Finset α → Submodule ℂ (EuclideanSpace ℂ β)) : Prop :=
  ∀ A ∈ D, ∀ B ∈ D, Disjoint A B → U A ≤ (U B)ᗮ

/-- The sum of dimensions divided by the ambient dimension. -/
def projectionPackingValue (D : Finset (Finset α))
    (U : Finset α → Submodule ℂ (EuclideanSpace ℂ β)) : ℝ :=
  (∑ A ∈ D, (finrank ℂ (U A) : ℝ)) / Fintype.card β

/-- The monotone closure of a packing, defined on the whole Boolean cube. -/
def packingUp (D : Finset (Finset α))
    (U : Finset α → Submodule ℂ (EuclideanSpace ℂ β)) (A : Finset α) :
    Submodule ℂ (EuclideanSpace ℂ β) :=
  ⨆ B : {B : Finset α // B ∈ D ∧ B ⊆ A}, U B.val

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
lemma packingUp_mono (D : Finset (Finset α))
    (U : Finset α → Submodule ℂ (EuclideanSpace ℂ β)) {A B : Finset α} (hAB : A ⊆ B) :
    packingUp D U A ≤ packingUp D U B := by
  apply iSup_le
  intro C
  exact le_iSup_of_le ⟨C.val, C.property.1, C.property.2.trans hAB⟩ le_rfl

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
lemma le_packingUp (D : Finset (Finset α))
    (U : Finset α → Submodule ℂ (EuclideanSpace ℂ β)) {A : Finset α} (hA : A ∈ D) :
    U A ≤ packingUp D U A :=
  le_iSup_of_le ⟨A, hA, Finset.Subset.refl _⟩ le_rfl

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
lemma packingUp_orthogonal (D : Finset (Finset α))
    (U : Finset α → Submodule ℂ (EuclideanSpace ℂ β)) (hU : IsProjectionPacking D U)
    {A B : Finset α} (hAB : Disjoint A B) : packingUp D U A ≤ (packingUp D U B)ᗮ := by
  apply iSup_le
  intro C
  rw [packingUp, ← Submodule.iInf_orthogonal]
  apply le_iInf
  intro E
  apply hU C.val C.property.1 E.val E.property.1
  exact Finset.disjoint_left.mpr (fun i hi hj =>
    Finset.disjoint_left.mp hAB (C.property.2 hi) (E.property.2 hj))

/-- The coordinate matrix of the orthogonal projection onto a subspace. -/
def projectionMatrix (V : Submodule ℂ (EuclideanSpace ℂ β)) : Matrix β β ℂ :=
  LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun β ℂ)
    (V.starProjection : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β)

lemma projectionMatrix_hermitian (V : Submodule ℂ (EuclideanSpace ℂ β)) :
    (projectionMatrix V).IsHermitian := by
  change Star.star (projectionMatrix V) = projectionMatrix V
  rw [projectionMatrix, ← map_star]
  congr 1
  exact V.starProjection_isSymmetric.adjoint_eq

lemma projectionMatrix_action (V : Submodule ℂ (EuclideanSpace ℂ β))
    (v : EuclideanSpace ℂ β) :
    projectionMatrix V *ᵥ (fun i => v i) = fun i => V.starProjection v i := by
  have hh := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun β ℂ).toBasis
    (EuclideanSpace.basisFun β ℂ).toBasis
    (V.starProjection : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) v
  exact hh

lemma projectionMatrix_idempotent (V : Submodule ℂ (EuclideanSpace ℂ β)) :
    projectionMatrix V * projectionMatrix V = projectionMatrix V := by
  rw [projectionMatrix, ← map_mul]
  congr 1
  exact congrArg ContinuousLinearMap.toLinearMap V.isIdempotentElem_starProjection

lemma projectionMatrix_mul_zero (V W : Submodule ℂ (EuclideanSpace ℂ β)) (hVW : W ≤ Vᗮ) :
    projectionMatrix V * projectionMatrix W = 0 := by
  rw [projectionMatrix, projectionMatrix, ← map_mul]
  have hz : (V.starProjection : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) *
      (W.starProjection : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) = 0 := by
    apply LinearMap.ext
    intro x
    exact V.starProjection_apply_eq_zero_iff.mpr (hVW (W.starProjection_apply_mem x))
  rw [hz, map_zero]

lemma projectionMatrix_trace (V : Submodule ℂ (EuclideanSpace ℂ β)) :
    (projectionMatrix V).trace = (finrank ℂ V : ℂ) := by
  change (LinearMap.toMatrix (EuclideanSpace.basisFun β ℂ).toBasis
    (EuclideanSpace.basisFun β ℂ).toBasis
    (V.starProjection : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β)).trace = _
  rw [← LinearMap.trace_eq_matrix_trace]
  apply LinearMap.IsProj.trace
  constructor
  · exact V.starProjection_apply_mem
  · intro x hx
    exact V.starProjection_eq_self_iff.mpr hx

/-- The matrix-valued antipodal Fourier multiplier. -/
def packingWitness (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β))
    (T : Finset α) : Matrix β β ℂ := projectionMatrix (V T) - projectionMatrix (V Tᶜ)

lemma packingWitness_hermitian (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β))
    (T : Finset α) : (packingWitness V T).IsHermitian :=
  (projectionMatrix_hermitian (V T)).sub (projectionMatrix_hermitian (V Tᶜ))

lemma packingWitness_sum (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β)) :
    ∑ T, packingWitness V T = 0 := by
  let e : Finset α ≃ Finset α :=
    { toFun := compl, invFun := compl, left_inv := compl_compl, right_inv := compl_compl }
  unfold packingWitness
  have hh := e.sum_comp (fun T => projectionMatrix (V T))
  change (∑ T, projectionMatrix (V Tᶜ)) = ∑ T, projectionMatrix (V T) at hh
  rw [Finset.sum_sub_distrib, hh, sub_self]

lemma finset_disjoint_compl (T : Finset α) : Disjoint T Tᶜ :=
  Finset.disjoint_left.mpr (fun _ hi hj => (Finset.mem_compl.mp hj) hi)

lemma packingWitness_energy_le (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β))
    (ho : ∀ A B : Finset α, Disjoint A B → V A ≤ (V B)ᗮ) (T : Finset α) :
    (∑ i, ∑ j, Complex.normSq (packingWitness V T i j)) ≤ Fintype.card β := by
  have hd : Disjoint (V T) (V Tᶜ) :=
    (V Tᶜ).orthogonal_disjoint.symm.mono_left (ho T Tᶜ (finset_disjoint_compl T))
  have hr := Submodule.finrank_sup_add_finrank_inf_eq (V T) (V Tᶜ)
  rw [hd.eq_bot, finrank_bot, add_zero] at hr
  have hb : finrank ℂ (V T) + finrank ℂ (V Tᶜ) ≤ Fintype.card β := by
    rw [← hr]
    simpa using Submodule.finrank_le (V T ⊔ V Tᶜ)
  have htr : (packingWitness V T * packingWitness V T).trace =
      (finrank ℂ (V T) : ℂ) + (finrank ℂ (V Tᶜ) : ℂ) := by
    simp [packingWitness, mul_sub, sub_mul, projectionMatrix_idempotent,
      projectionMatrix_mul_zero (V T) (V Tᶜ) (ho Tᶜ T (finset_disjoint_compl T).symm),
      projectionMatrix_mul_zero (V Tᶜ) (V T) (ho T Tᶜ (finset_disjoint_compl T)),
      projectionMatrix_trace]
  rw [← hermitian_frobenius _ (packingWitness_hermitian V T), htr]
  simpa using (show ((finrank ℂ (V T) + finrank ℂ (V Tᶜ) : ℕ) : ℝ) ≤ Fintype.card β by
    exact_mod_cast hb)

omit [Fintype β] [DecidableEq β] in
lemma blockFourier_hermitian (h : Finset α → Matrix β β ℂ)
    (hh : ∀ T, (h T).IsHermitian) (T : Finset α) : (blockFourier h T).IsHermitian := by
  ext i j
  simp only [blockFourier, complexFourier, complexWalsh, Matrix.conjTranspose_apply,
    map_div₀, map_sum, RCLike.star_def, Complex.conj_natCast, mul_comm]
  apply congrArg (fun z : ℂ => z / Fintype.card (Finset α))
  apply Finset.sum_congr rfl
  intro X hX
  have hx := congrArg (fun M : Matrix β β ℂ => M i j) (hh X)
  simpa [Matrix.conjTranspose] using congrArg (fun z : ℂ => (chi T X : ℂ) * z) hx

lemma packingFourier_empty (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β)) :
    blockFourier (packingWitness V) ∅ = 0 := by
  ext i j
  have hs := congrArg (fun M : Matrix β β ℂ => M i j) (packingWitness_sum V)
  simpa [blockFourier, complexFourier, complexWalsh, Matrix.sum_apply] using
    congrArg (fun z : ℂ => z / Fintype.card (Finset α)) hs

omit [DecidableEq α] [DecidableEq β] in
lemma sum_cube_matrix_swap {R : Type*} [AddCommMonoid R]
    (f : Finset α → β → β → R) :
    (∑ T, ∑ i, ∑ j, f T i j) = ∑ i, ∑ j, ∑ T, f T i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

lemma packingFourier_energy_le (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β))
    (ho : ∀ A B : Finset α, Disjoint A B → V A ≤ (V B)ᗮ) :
    (∑ T, ∑ i, ∑ j, Complex.normSq (blockFourier (packingWitness V) T i j)) ≤
      Fintype.card β := by
  change (∑ T, ∑ i, ∑ j, Complex.normSq (complexFourier (fun X => packingWitness V X i j) T)) ≤ _
  rw [sum_cube_matrix_swap]
  simp_rw [complexFourier_parseval]
  simp_rw [← Finset.sum_div]
  rw [← sum_cube_matrix_swap]
  apply (div_le_iff₀ (cube_card_pos (α := α))).mpr
  calc
    _ ≤ ∑ T : Finset α, (Fintype.card β : ℝ) :=
      Finset.sum_le_sum (fun T _ => packingWitness_energy_le V ho T)
    _ = _ := by simp; ring

lemma energy_upper_total (D : Finset (Finset α)) (e : Finset α → ℝ) (M : ℕ)
    (he : ∀ T, 0 ≤ e T) (he0 : e ∅ = 0) (hM : ∀ i, (star D i).card ≤ M) :
    (∑ A ∈ D, ∑ B ∈ D, e (A ∆ B)) ≤ 2 * (M : ℝ) * ∑ T, e T := by
  rw [energy_reindex, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T hT
  by_cases ht : T = ∅
  · simp [ht, he0]
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr ht
  have hh : (overlap D T).card ≤ 2 * M :=
    (overlap_card_le D hi).trans (Nat.mul_le_mul_left 2 (hM i))
  apply mul_le_mul_of_nonneg_right _ (he T)
  exact_mod_cast hh

def tensorIndicator (f : Finset α → ℝ) (v : EuclideanSpace ℂ β) : Finset α × β → ℂ :=
  fun X => (f X.1 : ℂ) * v X.2

omit [DecidableEq β] in
lemma tensorIndicator_eigen (h : Finset α → Matrix β β ℂ) (f : Finset α → ℝ)
    (v : EuclideanSpace ℂ β) (t : ℂ)
    (he : ∀ T, walsh f T ≠ 0 → h T *ᵥ (fun i => v i) = t • (fun i => v i)) :
    blockKernel h *ᵥ tensorIndicator f v = t • tensorIndicator f v := by
  apply blockKernel_eigen
  intro T i
  simp only [tensorIndicator, complexWalsh_real_mul]
  by_cases hz : walsh f T = 0
  · simp [hz]
  have hh := congrFun (he T hz) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hh
  calc
    _ = (walsh f T : ℂ) * (∑ j, h T i j * v j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [hh]; ring

lemma packingWitness_down_action (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β))
    (hm : ∀ {A B}, A ⊆ B → V A ≤ V B)
    (ho : ∀ A B : Finset α, Disjoint A B → V A ≤ (V B)ᗮ)
    {A T : Finset α} (hAT : Disjoint A T) (v : V A) :
    packingWitness V T *ᵥ (fun i => (v.val) i) = (-1 : ℂ) • (fun i => (v.val) i) := by
  have hp : (V T).starProjection v.val = 0 :=
    (V T).starProjection_apply_eq_zero_iff.mpr (ho A T hAT v.property)
  have hq : (V Tᶜ).starProjection v.val = v.val :=
    (V Tᶜ).starProjection_eq_self_iff.mpr
      (hm (Finset.subset_compl_iff_disjoint_left.mpr hAT.symm) v.property)
  rw [packingWitness, sub_mulVec, projectionMatrix_action, projectionMatrix_action]
  ext i
  simp [hp, hq]

lemma packingWitness_signed_action (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β))
    (hm : ∀ {A B}, A ⊆ B → V A ≤ V B)
    (ho : ∀ A B : Finset α, Disjoint A B → V A ≤ (V B)ᗮ)
    {A T : Finset α} (hAT : A ⊆ T) (v : V A) :
    packingWitness V T *ᵥ (fun i => (v.val) i) = (fun i => (v.val) i) := by
  have hp : (V T).starProjection v.val = v.val :=
    (V T).starProjection_eq_self_iff.mpr (hm hAT v.property)
  have hq : (V Tᶜ).starProjection v.val = 0 :=
    (V Tᶜ).starProjection_apply_eq_zero_iff.mpr
      (ho A Tᶜ (Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_compl.mp hj) (hAT hi)))
        v.property)
  rw [packingWitness, sub_mulVec, projectionMatrix_action, projectionMatrix_action]
  ext i
  simp [hp, hq]

lemma packing_down_eigen (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β))
    (hm : ∀ {A B}, A ⊆ B → V A ≤ V B)
    (ho : ∀ A B : Finset α, Disjoint A B → V A ≤ (V B)ᗮ)
    (A : Finset α) (v : V A) :
    blockKernel (packingWitness V) *ᵥ tensorIndicator (downIndicator A) v.val =
      (-1 : ℂ) • tensorIndicator (downIndicator A) v.val := by
  apply tensorIndicator_eigen
  intro T hT
  apply packingWitness_down_action V hm ho _ v
  by_contra hn
  exact hT (walsh_downIndicator_zero A T hn)

lemma packing_signed_eigen (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β))
    (hm : ∀ {A B}, A ⊆ B → V A ≤ V B)
    (ho : ∀ A B : Finset α, Disjoint A B → V A ≤ (V B)ᗮ)
    (A : Finset α) (v : V A) :
    blockKernel (packingWitness V) *ᵥ tensorIndicator (signedIndicator A) v.val =
      tensorIndicator (signedIndicator A) v.val := by
  have he := tensorIndicator_eigen (packingWitness V) (signedIndicator A) v.val 1
  simp only [one_smul] at he
  apply he
  intro T hT
  rw [walsh_signedIndicator] at hT
  have hd : Disjoint A (T ∆ Finset.univ) := by
    by_contra hn
    exact hT (walsh_downIndicator_zero A (T ∆ Finset.univ) hn)
  have hAT : A ⊆ T := by
    intro i hi
    by_contra hn
    exact (Finset.disjoint_left.mp hd hi) (by simp [Finset.mem_symmDiff, hn])
  simpa using packingWitness_signed_action V hm ho hAT v

omit [DecidableEq β] in
lemma restrict_tensor_eigen (D : Finset (Finset α)) (h : Finset α → Matrix β β ℂ)
    (f : Finset α → ℝ) (v : EuclideanSpace ℂ β) (t : ℂ)
    (hf : ∀ B, B ∉ D → f B = 0)
    (he : blockKernel h *ᵥ tensorIndicator f v = t • tensorIndicator f v) :
    (fun X Y : D × β => blockFourier h (X.1.val ∆ Y.1.val) X.2 Y.2) *ᵥ
      (fun X : D × β => (f X.1.val : ℂ) * v X.2) =
        t • (fun X : D × β => (f X.1.val : ℂ) * v X.2) := by
  ext ⟨A,i⟩
  have hh := congrFun he (A.val,i)
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Pi.smul_apply,
    smul_eq_mul, blockKernel, tensorIndicator] at *
  rw [Finset.sum_coe_sort D (fun B => ∑ j, blockFourier h (A.val ∆ B) i j *
    ((f B : ℂ) * v j))]
  rw [← hh]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro B hB hn
  simp [hf B hn]

omit [Fintype α] [DecidableEq β] in
/-- Triangularity remains valid when the scalar coefficients are vectors. -/
lemma down_tensor_injective (D : Finset (Finset α)) (w : D → EuclideanSpace ℂ β)
    (hw : ∀ X : D, ∑ A : D, (downIndicator A.val X.val : ℂ) • w A = 0) :
    ∀ A, w A = 0 := by
  classical
  intro k
  by_contra hk
  let S : Finset D := Finset.univ.filter (fun A => w A ≠ 0)
  have hS : S.Nonempty := ⟨k, by simp [S, hk]⟩
  obtain ⟨A, hA, hmax⟩ := S.exists_max_image (fun B : D => B.val.card) hS
  have hwa : w A ≠ 0 := (Finset.mem_filter.mp hA).2
  have hz : ∀ B : D, B ≠ A → (downIndicator B.val A.val : ℂ) • w B = 0 := by
    intro B hBA
    by_cases hB : w B = 0
    · simp [hB]
    have hn : ¬ A.val ⊆ B.val := by
      intro hab
      have hcard := hmax B (by simp [S, hB])
      have heq : A = B := Subtype.ext (Finset.eq_of_subset_of_card_le hab hcard)
      exact hBA heq.symm
    simp [downIndicator, hn]
  have hs := hw A
  rw [Finset.sum_eq_single A] at hs
  · exact hwa (by simpa [downIndicator] using hs)
  · intro B hB hBA
    exact hz B hBA
  · simp

omit [Fintype α] [DecidableEq β] in
/-- A basis vector in every assigned subspace gives an independent tensor indicator. -/
lemma packing_down_independent (D : Finset (Finset α))
    (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β)) :
    LinearIndependent ℂ
      (fun k : (Σ A : D, Fin (finrank ℂ (V A.val))) => fun X : D × β =>
        (downIndicator k.1.val X.1.val : ℂ) *
          ((Module.finBasis ℂ (V k.1.val) k.2).val) X.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  let w : D → EuclideanSpace ℂ β := fun A =>
    ∑ b, c ⟨A,b⟩ • (Module.finBasis ℂ (V A.val) b).val
  have hw : ∀ X : D, ∑ A : D, (downIndicator A.val X.val : ℂ) • w A = 0 := by
    intro X
    apply PiLp.ext
    intro j
    have hh := congrArg (fun f : D × β → ℂ => f (X,j)) hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fintype.sum_sigma] at hh
    simpa [w, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_left_comm, mul_assoc] using hh
  have hz := down_tensor_injective D w hw
  have hli := (Module.finBasis ℂ (V k.1.val)).linearIndependent.map'
    (V k.1.val).subtype (Submodule.ker_subtype _)
  exact Fintype.linearIndependent_iff.mp hli (fun b => c ⟨k.1,b⟩) (hz k.1) k.2

omit [DecidableEq β] in
lemma packing_signed_independent (D : Finset (Finset α))
    (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β)) :
    LinearIndependent ℂ
      (fun k : (Σ A : D, Fin (finrank ℂ (V A.val))) => fun X : D × β =>
        (signedIndicator k.1.val X.1.val : ℂ) *
          ((Module.finBasis ℂ (V k.1.val) k.2).val) X.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  apply Fintype.linearIndependent_iff.mp (packing_down_independent D V) c
  funext X
  have hh := congrArg (fun f : D × β → ℂ => f X) hc
  have he : (chi Finset.univ X.1.val : ℂ) *
      (∑ k : (Σ A : D, Fin (finrank ℂ (V A.val))),
        c k * ((downIndicator k.1.val X.1.val : ℂ) *
          ((Module.finBasis ℂ (V k.1.val) k.2).val) X.2)) = 0 := by
    simpa [signedIndicator, Complex.ofReal_mul, Finset.mul_sum, mul_left_comm, mul_assoc] using hh
  have hn : (chi (Finset.univ : Finset α) X.1.val : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    intro hz
    have hs := chi_sq (Finset.univ : Finset α) X.1.val
    simp [hz] at hs
  simpa using (mul_eq_zero.mp he).resolve_left hn

omit [DecidableEq β] in
lemma block_energy_restrict (D : Finset (Finset α)) (h : Finset α → Matrix β β ℂ) :
    (∑ X : D × β, ∑ Y : D × β,
      Complex.normSq (blockFourier h (X.1.val ∆ Y.1.val) X.2 Y.2)) =
    ∑ A ∈ D, ∑ B ∈ D, ∑ i, ∑ j, Complex.normSq (blockFourier h (A ∆ B) i j) := by
  calc
    _ = ∑ A : D, ∑ B : D, ∑ i, ∑ j,
        Complex.normSq (blockFourier h (A.val ∆ B.val) i j) := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.sum_comm]
    _ = _ := by
      have hh (A : D) : (∑ B : D, ∑ i, ∑ j,
          Complex.normSq (blockFourier h (A.val ∆ B.val) i j)) =
          ∑ B ∈ D, ∑ i, ∑ j, Complex.normSq (blockFourier h (A.val ∆ B) i j) :=
        Finset.sum_coe_sort D (fun B => ∑ i, ∑ j,
          Complex.normSq (blockFourier h (A.val ∆ B) i j))
      simp_rw [hh]
      exact Finset.sum_coe_sort D (fun A => ∑ B ∈ D, ∑ i, ∑ j,
        Complex.normSq (blockFourier h (A ∆ B) i j))

lemma packing_spectral_lower (D : Finset (Finset α)) (hD : IsDownset D)
    (V : Finset α → Submodule ℂ (EuclideanSpace ℂ β))
    (hm : ∀ {A B}, A ⊆ B → V A ≤ V B)
    (ho : ∀ A B : Finset α, Disjoint A B → V A ≤ (V B)ᗮ) :
    2 * (∑ A ∈ D, (finrank ℂ (V A) : ℝ)) ≤
      ∑ A ∈ D, ∑ B ∈ D, ∑ i, ∑ j,
        Complex.normSq (blockFourier (packingWitness V) (A ∆ B) i j) := by
  let M : Matrix (D × β) (D × β) ℂ :=
    fun X Y => blockFourier (packingWitness V) (X.1.val ∆ Y.1.val) X.2 Y.2
  have hM : M.IsHermitian := by
    ext X Y
    have hh := congrArg (fun N : Matrix β β ℂ => N X.2 Y.2)
      (blockFourier_hermitian (packingWitness V) (packingWitness_hermitian V)
        (X.1.val ∆ Y.1.val))
    simpa [M, Matrix.conjTranspose, symmDiff_comm] using hh
  let p := fun k : (Σ A : D, Fin (finrank ℂ (V A.val))) => fun X : D × β =>
    (downIndicator k.1.val X.1.val : ℂ) * ((Module.finBasis ℂ (V k.1.val) k.2).val) X.2
  let q := fun k : (Σ A : D, Fin (finrank ℂ (V A.val))) => fun X : D × β =>
    (signedIndicator k.1.val X.1.val : ℂ) * ((Module.finBasis ℂ (V k.1.val) k.2).val) X.2
  have hep (k) : M *ᵥ p k = (-1 : ℂ) • p k :=
    restrict_tensor_eigen D (packingWitness V) (downIndicator k.1.val)
      (Module.finBasis ℂ (V k.1.val) k.2).val (-1)
      (fun B hB => down_support D hD k.1.property hB)
      (packing_down_eigen V hm ho k.1.val (Module.finBasis ℂ (V k.1.val) k.2))
  have heq (k) : M *ᵥ q k = q k := by
    have hs (B : Finset α) (hB : B ∉ D) : signedIndicator k.1.val B = 0 := by
      simp [signedIndicator, down_support D hD k.1.property hB]
    simpa using restrict_tensor_eigen D (packingWitness V) (signedIndicator k.1.val)
      (Module.finBasis ℂ (V k.1.val) k.2).val 1 hs
      (by simpa using packing_signed_eigen V hm ho k.1.val (Module.finBasis ℂ (V k.1.val) k.2))
  have hh := complex_spectral_lower M hM p q
    (packing_down_independent D V) (packing_signed_independent D V) hep heq
  change 2 * (Fintype.card (Σ A : D, Fin (finrank ℂ (V A.val))) : ℝ) ≤
    ∑ X : D × β, ∑ Y : D × β,
      Complex.normSq (blockFourier (packingWitness V) (X.1.val ∆ Y.1.val) X.2 Y.2) at hh
  rw [block_energy_restrict, Fintype.card_sigma] at hh
  simp only [Fintype.card_fin, Nat.cast_sum] at hh
  rw [Finset.sum_coe_sort D (fun A => (finrank ℂ (V A) : ℝ))] at hh
  exact hh

/-- Every projection packing is bounded by any common bound on star sizes. -/
theorem projectionPackingValue_le_of_star_bound [Nonempty β]
    (D : Finset (Finset α)) (hD : IsDownset D)
    (U : Finset α → Submodule ℂ (EuclideanSpace ℂ β)) (hU : IsProjectionPacking D U)
    (M : ℕ) (hM : ∀ i, (star D i).card ≤ M) : projectionPackingValue D U ≤ M := by
  let V := packingUp D U
  have hm : ∀ {A B}, A ⊆ B → V A ≤ V B := fun hAB => packingUp_mono D U hAB
  have ho : ∀ A B : Finset α, Disjoint A B → V A ≤ (V B)ᗮ :=
    fun A B hAB => packingUp_orthogonal D U hU hAB
  let e : Finset α → ℝ := fun T => ∑ i, ∑ j,
    Complex.normSq (blockFourier (packingWitness V) T i j)
  have he : ∀ T, 0 ≤ e T := fun T =>
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))
  have he0 : e ∅ = 0 := by simp [e, packingFourier_empty]
  have hl := packing_spectral_lower D hD V hm ho
  have hu := energy_upper_total D e M he he0 hM
  have henergy : ∑ T, e T ≤ Fintype.card β := packingFourier_energy_le V ho
  have hdim : (∑ A ∈ D, (finrank ℂ (U A) : ℝ)) ≤ ∑ A ∈ D, (finrank ℂ (V A) : ℝ) := by
    apply Finset.sum_le_sum
    intro A hA
    exact_mod_cast Submodule.finrank_mono (le_packingUp D U hA)
  have hu' : (∑ A ∈ D, ∑ B ∈ D, e (A ∆ B)) ≤ 2 * (M : ℝ) * Fintype.card β :=
    hu.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hb : (∑ A ∈ D, (finrank ℂ (U A) : ℝ)) ≤ (M : ℝ) * Fintype.card β := by
    change 2 * (∑ A ∈ D, (finrank ℂ (V A) : ℝ)) ≤ ∑ A ∈ D, ∑ B ∈ D, e (A ∆ B) at hl
    linarith
  exact (div_le_iff₀ (show (0 : ℝ) < Fintype.card β by exact_mod_cast Fintype.card_pos)).mpr hb

/-- Assign the whole ambient space to a star and the zero subspace elsewhere. -/
def starProjectionPacking (i : α) (A : Finset α) : Submodule ℂ (EuclideanSpace ℂ β) :=
  if i ∈ A then ⊤ else ⊥

omit [Fintype α] [DecidableEq β] in
lemma starProjectionPacking_isPacking (D : Finset (Finset α)) (i : α) :
    IsProjectionPacking D (starProjectionPacking (β := β) i) := by
  intro A hA B hB hAB
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B
  · exact False.elim (Finset.disjoint_left.mp hAB hiA hiB)
  · simp [starProjectionPacking, hiA, hiB]
  · simp [starProjectionPacking, hiA, hiB]
  · simp [starProjectionPacking, hiA, hiB]

omit [Fintype α] [DecidableEq β] in
lemma starProjectionPacking_value [Nonempty β] (D : Finset (Finset α)) (i : α) :
    projectionPackingValue D (starProjectionPacking (β := β) i) = (star D i).card := by
  have hs : (∑ A ∈ D, (finrank ℂ (starProjectionPacking (β := β) i A) : ℝ)) =
      ((star D i).card : ℝ) * Fintype.card β := by
    calc
      _ = ∑ A ∈ D, if i ∈ A then (Fintype.card β : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro A hA
        by_cases hi : i ∈ A
        · rw [starProjectionPacking, if_pos hi, if_pos hi]
          simp
        · rw [starProjectionPacking, if_neg hi, if_neg hi]
          simp
      _ = ∑ A ∈ star D i, (Fintype.card β : ℝ) := by rw [star, Finset.sum_filter]
      _ = _ := by simp
  unfold projectionPackingValue
  rw [hs]
  exact mul_div_cancel_right₀ _ (by exact_mod_cast Fintype.card_ne_zero)

/-- Theorem 3: one largest star attains the optimum in every positive dimension. -/
theorem projection_packing [Nonempty α] (D : Finset (Finset α)) (hD : IsDownset D) :
    ∃ i : α, (∀ j, (star D j).card ≤ (star D i).card) ∧
      ∀ d : ℕ, 0 < d →
        ∃ U : Finset α → Submodule ℂ (EuclideanSpace ℂ (Fin d)),
          IsProjectionPacking D U ∧ projectionPackingValue D U = (star D i).card ∧
          ∀ W : Finset α → Submodule ℂ (EuclideanSpace ℂ (Fin d)),
            IsProjectionPacking D W → projectionPackingValue D W ≤ (star D i).card := by
  obtain ⟨i, hi, hmax⟩ := Finset.univ.exists_max_image (fun i : α => (star D i).card)
    Finset.univ_nonempty
  have hM : ∀ j, (star D j).card ≤ (star D i).card := fun j => hmax j (Finset.mem_univ j)
  refine ⟨i, hM, ?_⟩
  intro d hd
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  refine ⟨starProjectionPacking i, starProjectionPacking_isPacking D i,
    starProjectionPacking_value D i, ?_⟩
  intro W hW
  exact projectionPackingValue_le_of_star_bound D hD W hW (star D i).card hM

end Chvatal
