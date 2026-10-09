import Chvatal

#print axioms Chvatal.chvatal
#print axioms Chvatal.exists_maximum_star
#print axioms Chvatal.card_eq_zero_of_isEmpty
#print axioms Chvatal.kleitman_kahn
#print axioms Chvatal.kleitman_choice_coefficients
#print axioms Chvatal.maximal_witness_eq

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
