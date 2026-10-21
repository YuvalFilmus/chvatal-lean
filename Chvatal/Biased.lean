import Chvatal.Kleitman

/-!
# Biased Chvátal from weighted Kleitman

Nonnegative antitone functions are finite nonnegative combinations of downset
indicators. Applying Kleitman's inequality to these layers gives the weighted
inequality, and hence the `p`-biased version for `0 ≤ p ≤ 1/2`.
-/

open scoped BigOperators
open Finset
noncomputable section

namespace Chvatal

/-- Finite layer-cake argument: inequalities on downsets extend to nonnegative
antitone weights. -/
private lemma sum_mul_nonneg_of_downsets {β : Type*} [Fintype β] [PartialOrder β]
    (a : β → ℝ)
    (ha : ∀ S : Finset β, (∀ x ∈ S, ∀ y, y ≤ x → y ∈ S) → 0 ≤ ∑ x ∈ S, a x)
    (h : β → ℝ) (h0 : ∀ x, 0 ≤ h x) (hh : Antitone h) :
    0 ≤ ∑ x, h x * a x := by
  classical
  suffices aux : ∀ n : ℕ, ∀ h : β → ℝ, (∀ x, 0 ≤ h x) → Antitone h →
      (univ.filter (fun x => 0 < h x)).card = n → 0 ≤ ∑ x, h x * a x by
    exact aux _ h h0 hh rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h h0 hh hn
    let S := univ.filter (fun x => 0 < h x)
    by_cases hs : S.Nonempty
    · obtain ⟨j, hj, hmin⟩ := S.exists_min_image h hs
      have hj0 : 0 < h j := (mem_filter.mp hj).2
      let k := fun x => max (h x - h j) 0
      have hk0 : ∀ x, 0 ≤ k x := fun x => le_max_right _ _
      have hkh : Antitone k := fun x y hxy => max_le_max (sub_le_sub_right (hh hxy) _) le_rfl
      have hks : univ.filter (fun x => 0 < k x) ⊂ S := by
        apply ssubset_iff_subset_ne.mpr
        constructor
        · intro x hx
          have hxk := (mem_filter.mp hx).2
          have : 0 < h x := by dsimp [k] at hxk; rcases (lt_max_iff.mp hxk) with hx | hx <;> linarith
          exact mem_filter.mpr ⟨mem_univ _, this⟩
        · intro he
          have hjk : j ∈ univ.filter (fun x => 0 < k x) := by rw [he]; exact hj
          have : 0 < k j := (mem_filter.mp hjk).2
          simp [k] at this
      have hk := ih _ (by simpa [S, hn] using card_lt_card hks) k hk0 hkh rfl
      have hS := ha S (by
        intro x hx y hy
        exact mem_filter.mpr ⟨mem_univ _, lt_of_lt_of_le (mem_filter.mp hx).2 (hh hy)⟩)
      have heq : (∑ x, h x * a x) = (∑ x, k x * a x) + h j * ∑ x ∈ S, a x := by
        rw [Finset.mul_sum]
        have hexp : (∑ x ∈ S, h j * a x) = ∑ x, if x ∈ S then h j * a x else 0 := by simp
        rw [hexp, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxs : x ∈ S
        · have hle : h j ≤ h x := hmin x hxs
          simp only [if_pos hxs]
          dsimp [k]
          rw [max_eq_left (sub_nonneg.mpr hle)]
          ring
        · have hx0 : h x = 0 := by
            have : ¬ 0 < h x := by simpa [S] using hxs
            linarith [h0 x]
          simp [hxs, hx0, k, max_eq_right (by linarith : -h j ≤ 0)]
      rw [heq]
      exact add_nonneg hk (mul_nonneg hj0.le hS)
    · have hz : ∀ x, h x = 0 := by
        intro x
        have : ¬ 0 < h x := by
          intro hx
          exact hs ⟨x, mem_filter.mpr ⟨mem_univ _, hx⟩⟩
        linarith [h0 x]
      simp [hz]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Kleitman's inequality for every nonnegative decreasing weight. The same
Fourier coefficients work simultaneously for all such weights. -/
theorem kleitman_choice_weighted (U : Finset (Finset α)) (hU : IsIntersecting U)
    (τ : Finset α → α) (hτ : ∀ T, T.Nonempty → τ T ∈ T)
    (h : Finset α → ℝ) (h0 : ∀ T, 0 ≤ h T) (hh : Antitone h) :
    (∑ T ∈ U, h T) ≤ ∑ i, choiceCoefficient U τ i * ∑ T ∈ star univ i, h T := by
  classical
  let a := fun T => (∑ i, if i ∈ T then choiceCoefficient U τ i else 0) -
    if T ∈ U then (1 : ℝ) else 0
  have ha : ∀ D : Finset (Finset α), IsDownset D → 0 ≤ ∑ T ∈ D, a T := by
    intro D hD
    have hc := kleitman_choice U hU τ hτ D hD
    have he : (∑ T ∈ D, a T) =
        (∑ i, choiceCoefficient U τ i * (star D i).card) - (U ∩ D).card := by
      simp only [a, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        simp [star, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      · simp [inter_comm]
    rw [he]
    linarith
  have hw := sum_mul_nonneg_of_downsets a ha h h0 hh
  have he : (∑ T, h T * a T) =
      (∑ i, choiceCoefficient U τ i * ∑ T ∈ star univ i, h T) - ∑ T ∈ U, h T := by
    simp only [a, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp [star, Finset.sum_filter, mul_comm]
    · simp
  rw [he] at hw
  linarith

/-- Kahn's normalized coefficients work for every nonnegative decreasing weight,
independently of that weight. This is the weighted Kleitman statement. -/
theorem kleitman_kahn_weighted [LinearOrder α] [Nonempty α]
    (U : Finset (Finset α)) (hU : IsMaximalIntersecting U) :
    (∀ i, 0 ≤ kahnCoefficient U i) ∧ (∑ i, kahnCoefficient U i = 1) ∧
      ∀ h : Finset α → ℝ, (∀ T, 0 ≤ h T) → Antitone h →
        (∑ T ∈ U, h T) ≤ ∑ i, kahnCoefficient U i * ∑ T ∈ star univ i, h T :=
  ⟨(kleitman_kahn U hU).1, (kleitman_kahn U hU).2.1,
    fun h h0 hh => kleitman_choice_weighted U hU.1 maxChoice maxChoice_mem h h0 hh⟩

/-- Mass of a single set under independent Bernoulli coordinates. -/
def biasedWeight (p : ℝ) (T : Finset α) : ℝ :=
  p ^ T.card * (1 - p) ^ (Fintype.card α - T.card)

/-- The `p`-biased measure of a family of subsets. -/
def biasedMeasure (p : ℝ) (F : Finset (Finset α)) : ℝ :=
  ∑ T ∈ F, biasedWeight p T

omit [DecidableEq α] in
lemma biasedWeight_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset α) :
    0 ≤ biasedWeight p T :=
  mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _)

omit [DecidableEq α] in
/-- The atom weights decrease with inclusion, including at `p = 0` and `p = 1/2`. -/
lemma biasedWeight_antitone (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    Antitone (biasedWeight (α := α) p) := by
  intro S T hST
  have hcard := Finset.card_le_card hST
  have hbound := Finset.card_le_univ T
  have hT : T.card = S.card + (T.card - S.card) := by omega
  have hn : Fintype.card α - S.card =
      (Fintype.card α - T.card) + (T.card - S.card) := by omega
  have hp1 : 0 ≤ 1 - p := by linarith
  have hpq : p ≤ 1 - p := by linarith
  have hh := pow_le_pow_left₀ hp hpq (T.card - S.card)
  unfold biasedWeight
  calc
    _ = (p ^ S.card * (1 - p) ^ (Fintype.card α - T.card)) * p ^ (T.card - S.card) := by
      conv_lhs => lhs; rw [hT, pow_add]
      ring
    _ ≤ (p ^ S.card * (1 - p) ^ (Fintype.card α - T.card)) * (1 - p) ^ (T.card - S.card) :=
      mul_le_mul_of_nonneg_left hh
        (mul_nonneg (pow_nonneg hp _) (pow_nonneg hp1 _))
    _ = _ := by rw [hn, pow_add]; ring

omit [DecidableEq α] in
@[simp] lemma biasedMeasure_empty (p : ℝ) : biasedMeasure (α := α) p ∅ = 0 := by
  simp [biasedMeasure]

omit [DecidableEq α] in
lemma biasedMeasure_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (F : Finset (Finset α)) : 0 ≤ biasedMeasure p F :=
  Finset.sum_nonneg (fun T _ => biasedWeight_nonneg p hp hp1 T)

omit [DecidableEq α] in
lemma biasedMeasure_mono (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {F G : Finset (Finset α)} (hFG : F ⊆ G) : biasedMeasure p F ≤ biasedMeasure p G :=
  Finset.sum_le_sum_of_subset_of_nonneg hFG (fun T _ _ => biasedWeight_nonneg p hp hp1 T)

/-- The coefficients from Kleitman's theorem also bound all biased measures
with `0 ≤ p ≤ 1/2`, simultaneously for every downset. -/
theorem kleitman_choice_biased (U : Finset (Finset α)) (hU : IsIntersecting U)
    (τ : Finset α → α) (hτ : ∀ T, T.Nonempty → τ T ∈ T)
    (D : Finset (Finset α)) (hD : IsDownset D)
    (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    biasedMeasure p (U ∩ D) ≤ ∑ i, choiceCoefficient U τ i * biasedMeasure p (star D i) := by
  classical
  let h := fun T => if T ∈ D then biasedWeight p T else 0
  have h0 : ∀ T, 0 ≤ h T := by
    intro T
    dsimp [h]
    split_ifs
    · exact biasedWeight_nonneg p hp (by linarith) T
    · exact le_rfl
  have hh : Antitone h := by
    intro S T hST
    by_cases ht : T ∈ D
    · simp only [h, if_pos ht, if_pos (hD T ht S hST)]
      exact biasedWeight_antitone p hp hp2 hST
    · simp only [h, if_neg ht]
      exact h0 S
  have hw := kleitman_choice_weighted U hU τ hτ h h0 hh
  have hsum (F : Finset (Finset α)) : (∑ T ∈ F, h T) = biasedMeasure p (F ∩ D) := by
    simp [h, biasedMeasure]
  have he (i : α) : star univ i ∩ D = star D i := by
    ext T
    simp [star, and_comm]
  simp_rw [hsum, he] at hw
  exact hw

/-- Every intersecting family extends to an inclusion-maximal one. -/
lemma exists_maximal_intersecting (I : Finset (Finset α)) (hI : IsIntersecting I) :
    ∃ U, I ⊆ U ∧ IsMaximalIntersecting U := by
  classical
  let F := univ.filter (fun U : Finset (Finset α) => I ⊆ U ∧ IsIntersecting U)
  have hi : I ∈ F := mem_filter.mpr ⟨mem_univ _, Subset.refl _, hI⟩
  obtain ⟨U, hu, hmax⟩ := F.exists_max_image Finset.card ⟨I, hi⟩
  obtain ⟨hIU, hU⟩ := (mem_filter.mp hu).2
  refine ⟨U, hIU, hU, ?_⟩
  intro V hUV hV
  have hv : V ∈ F := mem_filter.mpr ⟨mem_univ _, hIU.trans hUV, hV⟩
  have he : U = V := Finset.eq_of_subset_of_card_le hUV (hmax V hv)
  exact he ▸ Subset.refl U

/-- Biased Chvátal: every intersecting subfamily has measure at most that of a
star, for `0 ≤ p ≤ 1/2`. A nonempty ground type is needed to name its center. -/
theorem chvatal_biased [Nonempty α] (D I : Finset (Finset α))
    (hD : IsDownset D) (hID : I ⊆ D) (hI : IsIntersecting I)
    (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    ∃ i : α, biasedMeasure p I ≤ biasedMeasure p (star D i) := by
  classical
  obtain ⟨U, hIU, hU⟩ := exists_maximal_intersecting I hI
  let τ : Finset α → α := fun T => if ht : T.Nonempty then ht.choose else Classical.arbitrary α
  have hτ : ∀ T, T.Nonempty → τ T ∈ T := by
    intro T ht
    simp only [τ, dif_pos ht]
    exact ht.choose_spec
  obtain ⟨i, hi, hmax⟩ := univ.exists_max_image
    (fun i : α => biasedMeasure p (star D i)) univ_nonempty
  refine ⟨i, ?_⟩
  calc
    biasedMeasure p I ≤ biasedMeasure p (U ∩ D) :=
      biasedMeasure_mono p hp (by linarith) (subset_inter hIU hID)
    _ ≤ ∑ j, choiceCoefficient U τ j * biasedMeasure p (star D j) :=
      kleitman_choice_biased U hU.1 τ hτ D hD p hp hp2
    _ ≤ ∑ j, choiceCoefficient U τ j * biasedMeasure p (star D i) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
        (hmax j (mem_univ _)) (choiceCoefficient_nonneg U τ j))
    _ = biasedMeasure p (star D i) := by
      rw [← Finset.sum_mul, choiceCoefficient_sum U hU τ, one_mul]

/-- A single star maximizes biased measure over all intersecting subfamilies. -/
theorem exists_maximum_biased_star [Nonempty α] (D : Finset (Finset α))
    (hD : IsDownset D) (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    ∃ i : α, star D i ⊆ D ∧ IsIntersecting (star D i) ∧
      ∀ I : Finset (Finset α), I ⊆ D → IsIntersecting I →
        biasedMeasure p I ≤ biasedMeasure p (star D i) := by
  obtain ⟨i, hi, hmax⟩ := univ.exists_max_image
    (fun i : α => biasedMeasure p (star D i)) univ_nonempty
  refine ⟨i, filter_subset _ _, star_intersecting D i, ?_⟩
  intro I hID hI
  obtain ⟨j, hj⟩ := chvatal_biased D I hD hID hI p hp hp2
  exact hj.trans (hmax j (mem_univ _))

omit [DecidableEq α] in
/-- On the empty ground type every intersecting family has biased measure zero. -/
theorem biasedMeasure_eq_zero_of_isEmpty [IsEmpty α]
    (I : Finset (Finset α)) (hI : IsIntersecting I) (p : ℝ) : biasedMeasure p I = 0 := by
  rw [Finset.card_eq_zero.mp (card_eq_zero_of_isEmpty I hI)]
  exact biasedMeasure_empty p

end Chvatal
