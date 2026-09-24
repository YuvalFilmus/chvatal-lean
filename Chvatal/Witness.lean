import Chvatal.Cube
import Chvatal.Spectral

open scoped BigOperators symmDiff
open Finset Matrix
noncomputable section

namespace Chvatal
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Downward closure under taking subsets. -/
def IsDownset (D : Finset (Finset α)) : Prop :=
  ∀ A ∈ D, ∀ B, B ⊆ A → B ∈ D

/-- Includes the case A = B, so the empty set cannot be a member. -/
def IsIntersecting (I : Finset (Finset α)) : Prop :=
  ∀ A ∈ I, ∀ B ∈ I, ¬ Disjoint A B

def up (I : Finset (Finset α)) (T : Finset α) : Prop := ∃ A ∈ I, A ⊆ T

noncomputable def upIndicator (I : Finset (Finset α)) (T : Finset α) : ℝ := by
  classical
  exact if up I T then 1 else 0

def witness (I : Finset (Finset α)) (T : Finset α) : ℝ :=
  upIndicator I T - upIndicator I Tᶜ

lemma up_not_compl (I : Finset (Finset α)) (hI : IsIntersecting I)
    {T : Finset α} (hT : up I T) : ¬ up I Tᶜ := by
  rintro ⟨B, hB, hBT⟩
  obtain ⟨A, hA, hAT⟩ := hT
  apply hI A hA B hB
  apply Finset.disjoint_left.mpr
  intro i hiA hiB
  have hh := hBT hiB
  simp only [Finset.mem_compl] at hh
  exact hh (hAT hiA)

lemma witness_up (I : Finset (Finset α)) (hI : IsIntersecting I)
    {T : Finset α} (hT : up I T) : witness I T = 1 := by
  simp [witness, upIndicator, hT, up_not_compl I hI hT]

lemma witness_compl (I : Finset (Finset α)) (T : Finset α) :
    witness I Tᶜ = -witness I T := by
  simp only [witness, compl_compl]
  ring

lemma witness_sq_le (I : Finset (Finset α)) (T : Finset α) : witness I T ^ 2 ≤ 1 := by
  unfold witness upIndicator
  split_ifs <;> norm_num

lemma witness_sum (I : Finset (Finset α)) : ∑ T, witness I T = 0 := by
  let e : Finset α ≃ Finset α :=
    { toFun := compl, invFun := compl, left_inv := compl_compl, right_inv := compl_compl }
  have hh := e.sum_comp (witness I)
  change (∑ T, witness I Tᶜ) = ∑ T, witness I T at hh
  simp_rw [witness_compl, Finset.sum_neg_distrib] at hh
  linarith

lemma witness_fourier_empty (I : Finset (Finset α)) : fourier (witness I) ∅ = 0 := by
  simp [fourier, walsh, witness_sum]

lemma witness_parseval_le (I : Finset (Finset α)) :
    ∑ T, fourier (witness I) T ^ 2 ≤ 1 := by
  rw [fourier_parseval, div_le_one (cube_card_pos (α := α))]
  calc
    _ ≤ ∑ T : Finset α, (1 : ℝ) := Finset.sum_le_sum (fun T _ => witness_sq_le I T)
    _ = _ := by simp

lemma down_eigen (I : Finset (Finset α)) (hI : IsIntersecting I)
    {A : Finset α} (hA : A ∈ I) :
    kernel (witness I) *ᵥ downIndicator A = (-1 : ℝ) • downIndicator A := by
  apply kernel_eigen
  intro T
  by_cases hd : Disjoint A T
  · have hu : up I Tᶜ := ⟨A, hA, Finset.subset_compl_iff_disjoint_left.mpr hd.symm⟩
    have hh := witness_up I hI hu
    rw [witness_compl] at hh
    have hneg : witness I T = -1 := by linarith
    rw [hneg]
  · rw [walsh_downIndicator_zero A T hd]
    simp

lemma signed_eigen (I : Finset (Finset α)) (hI : IsIntersecting I)
    {A : Finset α} (hA : A ∈ I) :
    kernel (witness I) *ᵥ signedIndicator A = signedIndicator A := by
  have hh := kernel_eigen (witness I) (signedIndicator A) 1
  simp only [one_smul] at hh
  apply hh
  intro T
  rw [walsh_signedIndicator]
  by_cases hd : Disjoint A (T ∆ Finset.univ)
  · have hAT : A ⊆ T := by
      intro i hi
      by_contra hn
      exact (Finset.disjoint_left.mp hd hi) (by simp [Finset.mem_symmDiff, hn])
    rw [witness_up I hI ⟨A, hA, hAT⟩]
  · rw [walsh_downIndicator_zero A (T ∆ Finset.univ) hd]
    simp

omit [Fintype α] in
/-- Triangularity of the principal-downset indicators, restricted to a larger family. -/
lemma down_independent (D I : Finset (Finset α)) (hID : I ⊆ D) :
    LinearIndependent ℝ (fun A : I => fun X : D => downIndicator A.val X.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  by_contra hk
  let S : Finset I := Finset.univ.filter (fun A => c A ≠ 0)
  have hS : S.Nonempty := ⟨k, by simp [S, hk]⟩
  obtain ⟨A, hA, hmax⟩ := S.exists_max_image (fun B : I => B.val.card) hS
  have hca : c A ≠ 0 := (Finset.mem_filter.mp hA).2
  have hz : ∀ B : I, B ≠ A → c B * downIndicator B.val A.val = 0 := by
    intro B hBA
    by_cases hB : c B = 0
    · simp [hB]
    have hnot : ¬ A.val ⊆ B.val := by
      intro hab
      have hcard := hmax B (by simp [S, hB])
      have heq : A = B := Subtype.ext (Finset.eq_of_subset_of_card_le hab hcard)
      exact hBA heq.symm
    simp [downIndicator, hnot]
  have heval := congrArg (fun v : D → ℝ => v ⟨A.val, hID A.property⟩) hc
  have hs : (∑ B : I, c B * downIndicator B.val A.val) = 0 := by
    simpa using heval
  rw [Finset.sum_eq_single A] at hs
  · exact hca (by simpa [downIndicator] using hs)
  · intro B hB hBA
    exact hz B hBA
  · simp

lemma signed_independent (D I : Finset (Finset α)) (hID : I ⊆ D) :
    LinearIndependent ℝ (fun A : I => fun X : D => signedIndicator A.val X.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  apply Fintype.linearIndependent_iff.mp (down_independent D I hID) c
  funext X
  have heval := congrArg (fun v : D → ℝ => v X) hc
  have hh : chi Finset.univ X.val * (∑ A : I, c A * downIndicator A.val X.val) = 0 := by
    simpa [signedIndicator, Finset.mul_sum, mul_left_comm, mul_assoc] using heval
  have hne : chi (Finset.univ : Finset α) X.val ≠ 0 := by
    intro h
    have := chi_sq (Finset.univ : Finset α) X.val
    simp [h] at this
  have := (mul_eq_zero.mp hh).resolve_left hne
  simpa using this

omit [Fintype α] in
lemma down_support (D : Finset (Finset α)) (hD : IsDownset D)
    {A X : Finset α} (hA : A ∈ D) (hX : X ∉ D) : downIndicator A X = 0 := by
  have hn : ¬ X ⊆ A := fun h => hX (hD A hA X h)
  simp [downIndicator, hn]

omit [DecidableEq α] in
lemma restrict_eigen (D : Finset (Finset α)) (M : Matrix (Finset α) (Finset α) ℝ)
    (f : Finset α → ℝ) (t : ℝ) (hf : ∀ X, X ∉ D → f X = 0)
    (he : M *ᵥ f = t • f) :
    (fun A B : D => M A.val B.val) *ᵥ (fun A : D => f A.val) =
      t • (fun A : D => f A.val) := by
  ext A
  have hh := congrFun he A.val
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at *
  rw [Finset.sum_coe_sort D (fun X => M A.val X * f X)]
  rw [← hh]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro X hX hn
  rw [hf X hn, mul_zero]

lemma witness_lower (D I : Finset (Finset α)) (hD : IsDownset D)
    (hID : I ⊆ D) (hI : IsIntersecting I) :
    2 * (I.card : ℝ) ≤ ∑ A ∈ D, ∑ B ∈ D, fourier (witness I) (A ∆ B) ^ 2 := by
  let M : Matrix D D ℝ := fun A B => kernel (witness I) A.val B.val
  have hM : M.IsHermitian := by
    ext A B
    simp [M, Matrix.conjTranspose, kernel, symmDiff_comm]
  have hp := down_independent D I hID
  have hq := signed_independent D I hID
  have hep (A : I) : M *ᵥ (fun X : D => downIndicator A.val X.val) =
      (-1 : ℝ) • (fun X : D => downIndicator A.val X.val) :=
    restrict_eigen D (kernel (witness I)) (downIndicator A.val) (-1)
      (fun X hX => down_support D hD (hID A.property) hX) (down_eigen I hI A.property)
  have heq (A : I) : M *ᵥ (fun X : D => signedIndicator A.val X.val) =
      (fun X : D => signedIndicator A.val X.val) := by
    have hs (X : Finset α) (hX : X ∉ D) : signedIndicator A.val X = 0 := by
      simp [signedIndicator, down_support D hD (hID A.property) hX]
    simpa using restrict_eigen D (kernel (witness I)) (signedIndicator A.val) 1 hs
      (by simpa using signed_eigen I hI A.property)
  have hh := spectral_lower M hM _ _ hp hq hep heq
  change 2 * (Fintype.card I : ℝ) ≤
    ∑ A : D, ∑ B : D, fourier (witness I) (A.val ∆ B.val) ^ 2 at hh
  have hsum : (∑ A : D, ∑ B : D, fourier (witness I) (A.val ∆ B.val) ^ 2) =
      ∑ A ∈ D, ∑ B ∈ D, fourier (witness I) (A ∆ B) ^ 2 := by
    calc
      _ = ∑ A : D, ∑ B ∈ D, fourier (witness I) (A.val ∆ B) ^ 2 := by
        apply Finset.sum_congr rfl
        intro A hA
        exact Finset.sum_coe_sort D (fun B => fourier (witness I) (A.val ∆ B) ^ 2)
      _ = _ := Finset.sum_coe_sort D (fun A => ∑ B ∈ D, fourier (witness I) (A ∆ B) ^ 2)
  rw [hsum] at hh
  simpa only [Fintype.card_coe] using hh

end Chvatal
