import Chvatal

#print axioms Chvatal.chvatal
#print axioms Chvatal.exists_maximum_star
#print axioms Chvatal.card_eq_zero_of_isEmpty

-- Check that the public theorem has the usual, unconditional mathematical statement.
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (D I : Finset (Finset α))
    (hD : ∀ A ∈ D, ∀ B, B ⊆ A → B ∈ D)
    (hID : I ⊆ D)
    (hI : ∀ A ∈ I, ∀ B ∈ I, ¬ Disjoint A B) :
    ∃ i : α, I.card ≤ (D.filter (fun A => i ∈ A)).card :=
  Chvatal.chvatal D I hD hID hI
