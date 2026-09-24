import Chvatal.Cube

open scoped BigOperators symmDiff
open Finset
noncomputable section

namespace Chvatal
variable {α : Type*} [Fintype α] [DecidableEq α]

def star (D : Finset (Finset α)) (i : α) : Finset (Finset α) := D.filter (i ∈ ·)
def overlap (D : Finset (Finset α)) (T : Finset α) : Finset (Finset α) :=
  D.filter (fun A => A ∆ T ∈ D)

omit [Fintype α] in
lemma overlap_card_le (D : Finset (Finset α)) {T : Finset α} {i : α} (hi : i ∈ T) :
    (overlap D T).card ≤ 2 * (star D i).card := by
  classical
  have hpos : ((overlap D T).filter (i ∈ ·)).card ≤ (star D i).card := by
    apply Finset.card_le_card
    intro A hA
    simp only [mem_filter, overlap, star] at *
    exact ⟨hA.1.1, hA.2⟩
  have hneg : ((overlap D T).filter (fun A => i ∉ A)).card ≤ (star D i).card := by
    apply Finset.card_le_card_of_injOn (fun A => A ∆ T)
    · intro A hA
      simp only [mem_coe, mem_filter, overlap, star] at *
      exact ⟨hA.1.2, Finset.mem_symmDiff.mpr (Or.inr ⟨hi, hA.2⟩)⟩
    · intro A hA B hB hAB
      simpa using congrArg (fun X => X ∆ T) hAB
  have hh := Finset.card_filter_add_card_filter_not (s := overlap D T) (i ∈ ·)
  omega

lemma energy_reindex (D : Finset (Finset α)) (e : Finset α → ℝ) :
    (∑ A ∈ D, ∑ B ∈ D, e (A ∆ B)) =
      ∑ T : Finset α, ((overlap D T).card : ℝ) * e T := by
  classical
  have hrow (A : Finset α) :
      (∑ B ∈ D, e (A ∆ B)) = ∑ T : Finset α, if A ∆ T ∈ D then e T else 0 := by
    have hh := sum_toggle A (fun B => if B ∈ D then e (A ∆ B) else 0)
    have hleft : (∑ X : Finset α, if X ∆ A ∈ D then e (A ∆ (X ∆ A)) else 0) =
        ∑ X : Finset α, if A ∆ X ∈ D then e X else 0 := by
      apply Finset.sum_congr rfl
      intro X hX
      simp [symmDiff_comm X A]
    rw [hleft] at hh
    simpa [← Finset.sum_filter] using hh.symm
  simp_rw [hrow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  rw [overlap, ← Finset.sum_filter]
  simp

lemma energy_upper (D : Finset (Finset α)) (e : Finset α → ℝ) (M : ℕ)
    (he : ∀ T, 0 ≤ e T) (he0 : e ∅ = 0) (hesum : ∑ T, e T ≤ 1)
    (hM : ∀ i, (star D i).card ≤ M) :
    (∑ A ∈ D, ∑ B ∈ D, e (A ∆ B)) ≤ 2 * (M : ℝ) := by
  rw [energy_reindex]
  calc
    _ ≤ ∑ T : Finset α, 2 * (M : ℝ) * e T := by
      apply Finset.sum_le_sum
      intro T hT
      by_cases hT0 : T = ∅
      · simp [hT0, he0]
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hT0
      have hh : (overlap D T).card ≤ 2 * M :=
        (overlap_card_le D hi).trans (Nat.mul_le_mul_left 2 (hM i))
      apply mul_le_mul_of_nonneg_right _ (he T)
      exact_mod_cast hh
    _ = 2 * (M : ℝ) * ∑ T, e T := by rw [Finset.mul_sum]
    _ ≤ 2 * (M : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) M]

end Chvatal
