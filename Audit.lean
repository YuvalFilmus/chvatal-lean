import Chvatal

#print axioms Chvatal.chvatal
#print axioms Chvatal.exists_maximum_star
#print axioms Chvatal.card_eq_zero_of_isEmpty
#print axioms Chvatal.kleitman_kahn
#print axioms Chvatal.kleitman_choice_coefficients
#print axioms Chvatal.maximal_witness_eq
#print axioms Chvatal.projection_packing
#print axioms Chvatal.projectionPackingValue_le_of_star_bound

-- Check that the public theorem has the usual, unconditional mathematical statement.
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (D I : Finset (Finset α))
    (hD : ∀ A ∈ D, ∀ B, B ⊆ A → B ∈ D)
    (hID : I ⊆ D)
    (hI : ∀ A ∈ I, ∀ B ∈ I, ¬ Disjoint A B) :
    ∃ i : α, I.card ≤ (D.filter (fun A => i ∈ A)).card :=
  Chvatal.chvatal D I hD hID hI

-- Maximality is inclusion-maximality, and the same coefficients work for every downset.
example {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    (U : Finset (Finset α))
    (hU : (∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B) ∧
      ∀ V : Finset (Finset α), U ⊆ V →
        (∀ A ∈ V, ∀ B ∈ V, ¬ Disjoint A B) → V ⊆ U) :
    (∀ i, 0 ≤ Chvatal.kahnCoefficient U i) ∧
    (∑ i, Chvatal.kahnCoefficient U i = 1) ∧
    ∀ D : Finset (Finset α),
      (∀ A ∈ D, ∀ B, B ⊆ A → B ∈ D) →
      ((U ∩ D).card : ℝ) ≤
        ∑ i, Chvatal.kahnCoefficient U i * (D.filter (fun A => i ∈ A)).card :=
  Chvatal.kleitman_kahn U hU

-- The projection packing theorem: arbitrary complex subspaces, including the empty-set loop,
-- with the packing value and all mathematical predicates expanded.
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (D : Finset (Finset α)) (hD : ∀ A ∈ D, ∀ B, B ⊆ A → B ∈ D) :
    ∃ i : α, (∀ j, (D.filter (j ∈ ·)).card ≤ (D.filter (i ∈ ·)).card) ∧
      ∀ d : ℕ, 0 < d →
        ∃ U : Finset α → Submodule ℂ (EuclideanSpace ℂ (Fin d)),
          (∀ A ∈ D, ∀ B ∈ D, Disjoint A B → U A ≤ (U B)ᗮ) ∧
          (∑ A ∈ D, (Module.finrank ℂ (U A) : ℝ)) / d = (D.filter (i ∈ ·)).card ∧
          ∀ W : Finset α → Submodule ℂ (EuclideanSpace ℂ (Fin d)),
            (∀ A ∈ D, ∀ B ∈ D, Disjoint A B → W A ≤ (W B)ᗮ) →
            (∑ A ∈ D, (Module.finrank ℂ (W A) : ℝ)) / d ≤ (D.filter (i ∈ ·)).card := by
  simpa only [Chvatal.IsProjectionPacking, Chvatal.projectionPackingValue,
    Chvatal.star, Fintype.card_fin] using Chvatal.projection_packing D hD
