import Chvatal.Counting
import Chvatal.Witness

open scoped BigOperators symmDiff
open Finset
noncomputable section

namespace Chvatal
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Chvátal's inequality with any common upper bound on the star sizes. -/
theorem card_le_of_star_bound (D I : Finset (Finset α))
    (hD : IsDownset D) (hID : I ⊆ D) (hI : IsIntersecting I)
    (M : ℕ) (hM : ∀ i, (star D i).card ≤ M) : I.card ≤ M := by
  have hl := witness_lower D I hD hID hI
  have hu := energy_upper D (fun T => fourier (witness I) T ^ 2) M
    (fun T => sq_nonneg _) (by simp [witness_fourier_empty])
    (witness_parseval_le I) hM
  have hh : (I.card : ℝ) ≤ (M : ℝ) := by linarith
  exact_mod_cast hh

/-- Every intersecting subfamily of a downset is no larger than a star.
The ground type is nonempty so that the conclusion can name a star center. -/
theorem chvatal [Nonempty α] (D I : Finset (Finset α))
    (hD : IsDownset D) (hID : I ⊆ D) (hI : IsIntersecting I) :
    ∃ i : α, I.card ≤ (star D i).card := by
  obtain ⟨i, hi, hmax⟩ := Finset.univ.exists_max_image (fun i : α => (star D i).card)
    Finset.univ_nonempty
  exact ⟨i, card_le_of_star_bound D I hD hID hI _ (fun j => hmax j (Finset.mem_univ j))⟩

omit [Fintype α] in
lemma star_intersecting (D : Finset (Finset α)) (i : α) : IsIntersecting (star D i) := by
  intro A hA B hB hd
  exact (Finset.disjoint_left.mp hd (Finset.mem_filter.mp hA).2) (Finset.mem_filter.mp hB).2

/-- A downset has a maximum intersecting subfamily that is a star.
The center is chosen once, independently of the competing subfamily. -/
theorem exists_maximum_star [Nonempty α] (D : Finset (Finset α)) (hD : IsDownset D) :
    ∃ i : α, star D i ⊆ D ∧ IsIntersecting (star D i) ∧
      ∀ I : Finset (Finset α), I ⊆ D → IsIntersecting I → I.card ≤ (star D i).card := by
  obtain ⟨i, hi, hmax⟩ := Finset.univ.exists_max_image (fun i : α => (star D i).card)
    Finset.univ_nonempty
  refine ⟨i, Finset.filter_subset _ _, star_intersecting D i, ?_⟩
  intro I hID hI
  exact card_le_of_star_bound D I hD hID hI _ (fun j => hmax j (Finset.mem_univ j))

omit [Fintype α] [DecidableEq α] in
/-- The empty-ground-set case, for which there is no possible star center. -/
theorem card_eq_zero_of_isEmpty [IsEmpty α] (I : Finset (Finset α)) (hI : IsIntersecting I) :
    I.card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A hA
  have he : A = ∅ := Subsingleton.elim _ _
  exact hI A hA A hA (by simp [he])

end Chvatal
