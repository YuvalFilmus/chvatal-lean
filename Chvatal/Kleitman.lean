import Chvatal.Main

open scoped BigOperators symmDiff
open Finset
noncomputable section

namespace Chvatal
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Maximal under inclusion among intersecting families. -/
def IsMaximalIntersecting (U : Finset (Finset α)) : Prop :=
  IsIntersecting U ∧ ∀ V, U ⊆ V → IsIntersecting V → V ⊆ U

omit [Fintype α] in
lemma maximal_mem_of_intersects (U : Finset (Finset α)) (hU : IsMaximalIntersecting U)
    (T : Finset α) (hT : ¬ Disjoint T T)
    (hTU : ∀ A ∈ U, ¬ Disjoint T A) : T ∈ U := by
  apply hU.2 (insert T U) (subset_insert T U) _ (mem_insert_self T U)
  intro A hA B hB
  simp only [mem_insert] at hA hB
  rcases hA with rfl | hA <;> rcases hB with rfl | hB
  · exact hT
  · exact hTU B hB
  · exact fun hd => hTU A hA hd.symm
  · exact hU.1 A hA B hB

lemma maximal_nonempty [Nonempty α] (U : Finset (Finset α))
    (hU : IsMaximalIntersecting U) : U.Nonempty := by
  by_contra hn
  have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hm : (univ : Finset α) ∈ U := maximal_mem_of_intersects U hU univ
    (by simp [Finset.univ_nonempty.ne_empty]) (by simp [he])
  simp [he] at hm

omit [Fintype α] in
lemma maximal_up_iff (U : Finset (Finset α)) (hU : IsMaximalIntersecting U)
    (T : Finset α) : up U T ↔ T ∈ U := by
  constructor
  · rintro ⟨A, hA, hAT⟩
    apply maximal_mem_of_intersects U hU T
    · intro hd
      exact hU.1 A hA A hA (Finset.disjoint_left.mpr (fun i hi hj =>
        Finset.disjoint_left.mp hd (hAT hi) (hAT hj)))
    · intro B hB hd
      exact hU.1 A hA B hB (Finset.disjoint_left.mpr (fun i hi hj =>
        Finset.disjoint_left.mp hd (hAT hi) hj))
  · intro hT
    exact ⟨T, hT, Finset.Subset.refl _⟩

lemma maximal_mem_or_compl [Nonempty α] (U : Finset (Finset α))
    (hU : IsMaximalIntersecting U) (T : Finset α) : T ∈ U ∨ Tᶜ ∈ U := by
  by_cases hc : Tᶜ ∈ U
  · exact Or.inr hc
  have ht : ∀ A ∈ U, ¬ Disjoint T A := by
    intro A hA hd
    apply hc
    apply (maximal_up_iff U hU Tᶜ).mp
    exact ⟨A, hA, Finset.subset_compl_iff_disjoint_left.mpr hd⟩
  obtain ⟨A, hA⟩ := maximal_nonempty U hU
  have hTT : ¬ Disjoint T T := by
    intro hd
    have he : T = ∅ := (Finset.disjoint_self_iff_empty T).mp hd
    exact ht A hA (by simp [he])
  exact Or.inl (maximal_mem_of_intersects U hU T hTT ht)

/-- For a maximal family the spectral witness is exactly `2 1_U - 1`. -/
lemma maximal_witness_eq [Nonempty α] (U : Finset (Finset α))
    (hU : IsMaximalIntersecting U) (T : Finset α) :
    witness U T = 2 * (if T ∈ U then 1 else 0) - 1 := by
  classical
  rcases maximal_mem_or_compl U hU T with ht | hc
  · rw [witness_up U hU.1 ⟨T, ht, Finset.Subset.refl _⟩]
    norm_num [ht]
  · have hn : T ∉ U := by
      intro ht
      exact up_not_compl U hU.1 ⟨T, ht, Finset.Subset.refl _⟩
        ⟨Tᶜ, hc, Finset.Subset.refl _⟩
    have hh := witness_up U hU.1 ⟨Tᶜ, hc, Finset.Subset.refl _⟩
    rw [witness_compl] at hh
    simp only [hn, if_false, mul_zero, zero_sub]
    linarith

lemma maximal_parseval [Nonempty α] (U : Finset (Finset α))
    (hU : IsMaximalIntersecting U) : ∑ T, fourier (witness U) T ^ 2 = 1 := by
  have hs (T : Finset α) : witness U T ^ 2 = 1 := by
    rw [maximal_witness_eq U hU T]
    split_ifs <;> norm_num
  rw [fourier_parseval]
  simp_rw [hs]
  simp

/-- Allocate each nonempty Fourier interaction to its chosen coordinate. -/
def choiceCoefficient (U : Finset (Finset α)) (τ : Finset α → α) (i : α) : ℝ :=
  ∑ T : Finset α, if T ≠ ∅ ∧ τ T = i then fourier (witness U) T ^ 2 else 0

lemma choiceCoefficient_nonneg (U : Finset (Finset α)) (τ : Finset α → α) (i : α) :
    0 ≤ choiceCoefficient U τ i := by
  apply Finset.sum_nonneg
  intro T hT
  split_ifs <;> positivity

lemma choiceCoefficient_sum_mul (U : Finset (Finset α)) (τ : Finset α → α)
    (a : α → ℝ) :
    (∑ i, choiceCoefficient U τ i * a i) =
      ∑ T : Finset α, fourier (witness U) T ^ 2 * a (τ T) := by
  classical
  unfold choiceCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases ht : T = ∅
  · simp [ht, witness_fourier_empty]
  · simp [ht]

lemma choiceCoefficient_sum [Nonempty α] (U : Finset (Finset α))
    (hU : IsMaximalIntersecting U) (τ : Finset α → α) :
    ∑ i, choiceCoefficient U τ i = 1 := by
  have hh := choiceCoefficient_sum_mul U τ (fun _ => 1)
  simpa [maximal_parseval U hU] using hh

/-- A single Fourier allocation works simultaneously for every downset. -/
theorem kleitman_choice (U : Finset (Finset α)) (hU : IsIntersecting U)
    (τ : Finset α → α) (hτ : ∀ T, T.Nonempty → τ T ∈ T)
    (D : Finset (Finset α)) (hD : IsDownset D) :
    ((U ∩ D).card : ℝ) ≤ ∑ i, choiceCoefficient U τ i * (star D i).card := by
  have hl := witness_lower_subset D (U ∩ D) U hD inter_subset_right inter_subset_left hU
  rw [energy_reindex D (fun T => fourier (witness U) T ^ 2)] at hl
  have hu : (∑ T : Finset α, ((overlap D T).card : ℝ) * fourier (witness U) T ^ 2) ≤
      2 * ∑ i, choiceCoefficient U τ i * (star D i).card := by
    rw [choiceCoefficient_sum_mul, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro T hT
    by_cases ht : T = ∅
    · simp [ht, witness_fourier_empty]
    · have hh : ((overlap D T).card : ℝ) ≤ 2 * ((star D (τ T)).card : ℝ) := by
        exact_mod_cast overlap_card_le D (hτ T (Finset.nonempty_iff_ne_empty.mpr ht))
      calc
        _ ≤ (2 * ((star D (τ T)).card : ℝ)) * fourier (witness U) T ^ 2 :=
          mul_le_mul_of_nonneg_right hh (sq_nonneg _)
        _ = _ := by ring
  linarith

/-- The full normalized coefficient statement for an arbitrary choice function. -/
theorem kleitman_choice_coefficients [Nonempty α]
    (U : Finset (Finset α)) (hU : IsMaximalIntersecting U)
    (τ : Finset α → α) (hτ : ∀ T, T.Nonempty → τ T ∈ T) :
    (∀ i, 0 ≤ choiceCoefficient U τ i) ∧
    (∑ i, choiceCoefficient U τ i = 1) ∧
    ∀ D : Finset (Finset α), IsDownset D →
      ((U ∩ D).card : ℝ) ≤ ∑ i, choiceCoefficient U τ i * (star D i).card :=
  ⟨choiceCoefficient_nonneg U τ, choiceCoefficient_sum U hU τ,
    fun D hD => kleitman_choice U hU.1 τ hτ D hD⟩

variable [LinearOrder α] [Nonempty α]

/-- The value at the empty set is irrelevant to the coefficient formula. -/
def maxChoice (T : Finset α) : α :=
  if hT : T.Nonempty then T.max' hT else Classical.arbitrary α

omit [Fintype α] [DecidableEq α] in
lemma maxChoice_mem (T : Finset α) (hT : T.Nonempty) : maxChoice T ∈ T := by
  simp only [maxChoice, dif_pos hT]
  exact Finset.max'_mem T hT

/-- Kahn's coefficients, grouping Fourier energy by the largest coordinate. -/
def kahnCoefficient (U : Finset (Finset α)) (i : α) : ℝ :=
  choiceCoefficient U maxChoice i

/-- Kleitman's downset inequality with Kahn's explicit coefficients.
The coefficients are chosen before, and independently of, the downset. -/
theorem kleitman_kahn (U : Finset (Finset α)) (hU : IsMaximalIntersecting U) :
    (∀ i, 0 ≤ kahnCoefficient U i) ∧
    (∑ i, kahnCoefficient U i = 1) ∧
    ∀ D : Finset (Finset α), IsDownset D →
      ((U ∩ D).card : ℝ) ≤ ∑ i, kahnCoefficient U i * (star D i).card := by
  exact kleitman_choice_coefficients U hU maxChoice maxChoice_mem

end Chvatal
