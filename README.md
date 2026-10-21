# Chvátal's conjecture and its spectral strengthenings in Lean

A Lean formalization of Chvátal's conjecture, its $p$-biased extension, Kleitman's conjecture with Kahn's explicit coefficients, and the projection packing bound from *Chvátal's conjecture: a proof from The Book* by David Ellis, Yuval Filmus, and Ehud Friedgut.

## The theorem in English

Let $E$ be a nonempty finite set, and let $\mathcal D$ be a **downset** of subsets of $E$: if $A\in\mathcal D$ and $B\subseteq A$, then $B\in\mathcal D$. A family $\mathcal I\subseteq\mathcal D$ is **intersecting** if $A\cap B\ne\varnothing$ for every $A,B\in\mathcal I$, including $A=B$.

**Chvátal's theorem.** There is an element $i\in E$ such that the star

$$
\mathcal S_i=\{A\in\mathcal D:i\in A\}
$$

is a maximum-size intersecting subfamily of $\mathcal D$. Equivalently, the same choice of $i$ satisfies

$$
|\mathcal I|\le |\mathcal S_i|
\qquad\text{for every intersecting }\mathcal I\subseteq\mathcal D.
$$

The ground set must be nonempty to name a star center. For an empty ground set, every intersecting family is empty; this case is proved separately.

## The theorem in Lean

Sets are represented by `Finset α`, and families of sets by `Finset (Finset α)`. The ground type `α` has instances `[Fintype α] [DecidableEq α]`. Taking `α = Fin n` gives the usual ground set of size `n`.

The definitions, in namespace `Chvatal`, are:

```lean
def IsDownset (D : Finset (Finset α)) : Prop :=
  ∀ A ∈ D, ∀ B, B ⊆ A → B ∈ D

def IsIntersecting (I : Finset (Finset α)) : Prop :=
  ∀ A ∈ I, ∀ B ∈ I, ¬ Disjoint A B

def star (D : Finset (Finset α)) (i : α) : Finset (Finset α) :=
  D.filter (i ∈ ·)
```

`IsDownset` and `IsIntersecting` are defined in [Chvatal/Witness.lean](Chvatal/Witness.lean); `star` is defined in [Chvatal/Counting.lean](Chvatal/Counting.lean). The intersecting condition includes a set paired with itself, so the empty set cannot be a member.

The main result is `Chvatal.exists_maximum_star` in [Chvatal/Main.lean](Chvatal/Main.lean). Its declaration is:

```lean
theorem exists_maximum_star [Nonempty α]
    (D : Finset (Finset α)) (hD : IsDownset D) :
    ∃ i : α, star D i ⊆ D ∧ IsIntersecting (star D i) ∧
      ∀ I : Finset (Finset α),
        I ⊆ D → IsIntersecting I → I.card ≤ (star D i).card
```

The same file also proves:

- `Chvatal.chvatal`: each intersecting subfamily is no larger than some star.
- `Chvatal.card_le_of_star_bound`: any common upper bound on the star sizes bounds every intersecting subfamily. This formulation also works on an empty ground type.
- `Chvatal.star_intersecting`: every star is intersecting.
- `Chvatal.card_eq_zero_of_isEmpty`: an intersecting family on an empty ground type has cardinality zero.

## Proof of Chvátal's theorem

Fix an intersecting family $\mathcal I\subseteq\mathcal D$, and let $\mathcal I^\uparrow$ be its upward closure in $2^E$. Define

$$
h(T)=\mathbf 1_{\mathcal I^\uparrow}(T)
     -\mathbf 1_{\mathcal I^\uparrow}(E\setminus T).
$$

This function has mean zero and takes values in $\{-1,0,1\}$. Its normalized Fourier transform defines the real symmetric convolution matrix

$$
H(A,B)=\widehat h(A\mathbin{\triangle}B).
$$

Let $H_{\mathcal D}$ be the principal submatrix indexed by $\mathcal D$. The proof establishes

$$
2|\mathcal I|
\le \mathrm{Tr}(H_{\mathcal D}^2)
=\sum_{A,B\in\mathcal D}\widehat h(A\mathbin{\triangle}B)^2
\le 2\max_{i\in E}|\mathcal S_i|.
$$

For the lower bound, the functions $p_A(X)=\mathbf 1_{X\subseteq A}$ and $q_A(X)=(-1)^{|X|}p_A(X)$, for $A\in\mathcal I$, give linearly independent eigenvectors with eigenvalues $-1$ and $+1$, respectively. Downward closure ensures these functions are supported on $\mathcal D$.

For the upper bound, group matrix entries by their symmetric difference $T$. For each nonempty $T$ and $i\in T$, the number of relevant pairs is at most $2|\mathcal S_i|$. Parseval and $\mathbb E[h^2]\le1$ complete the estimate.

## Kleitman's theorem with Kahn's coefficients

Let $\mathcal U\subseteq 2^E$ be maximal under inclusion among intersecting families, and fix a linear order on the nonempty finite ground set $E$. Define

$$
h=2\mathbf 1_{\mathcal U}-1,
\qquad
c_i=\sum_{\substack{T\ne\varnothing\\\max(T)=i}}\widehat h(T)^2.
$$

**Kleitman's theorem with Kahn's formula.** These coefficients are nonnegative, sum to one, and satisfy

$$
|\mathcal U\cap\mathcal D|
\le \sum_{i\in E}c_i\,|\{A\in\mathcal D:i\in A\}|
\qquad\text{for every downset }\mathcal D\subseteq 2^E.
$$

The coefficients depend only on $\mathcal U$ and the fixed coordinate order, and work simultaneously for all downsets. The formalized statement is the downset inequality; no transport or max-flow construction is included.

The definitions and theorem are in [Chvatal/Kleitman.lean](Chvatal/Kleitman.lean):

```lean
def IsMaximalIntersecting (U : Finset (Finset α)) : Prop :=
  IsIntersecting U ∧ ∀ V, U ⊆ V → IsIntersecting V → V ⊆ U

theorem kleitman_kahn [LinearOrder α] [Nonempty α]
    (U : Finset (Finset α)) (hU : IsMaximalIntersecting U) :
    (∀ i, 0 ≤ kahnCoefficient U i) ∧
    (∑ i, kahnCoefficient U i = 1) ∧
    ∀ D : Finset (Finset α), IsDownset D →
      ((U ∩ D).card : ℝ) ≤ ∑ i, kahnCoefficient U i * (star D i).card
```

`kahnCoefficient U i` groups the squared Fourier coefficients of `witness U` by their largest coordinate. The lemma `maximal_witness_eq` proves that this witness is exactly $2\mathbf 1_{\mathcal U}-1$, and `maximal_parseval` proves that its total Fourier energy is one.

More generally, `choiceCoefficient U τ i` assigns the Fourier energy of each nonempty $T$ to any selected coordinate $\tau(T)\in T$. The theorem `kleitman_choice_coefficients` proves the same nonnegativity, normalization, and simultaneous downset inequalities for every such choice function. In Lean, `τ` is defined on all finite subsets; its value at the empty set is ignored.

The spectral proof keeps `witness U` fixed and applies `witness_lower_subset` to $\mathcal I=\mathcal U\cap\mathcal D$. Grouping by symmetric difference and using `overlap_card_le` gives

$$
2|\mathcal U\cap\mathcal D|
\le \sum_{T\ne\varnothing}|\mathrm{overlap}(\mathcal D,T)|\widehat h(T)^2
\le 2\sum_{T\ne\varnothing}|\mathcal D\cap\mathcal S_{\tau(T)}|\widehat h(T)^2.
$$

## The $p$-biased extension

The paragraph at the end of Section 3 extends Chvátal's theorem to the $p$-biased measure

$$
\mu_p(\mathcal F)=\sum_{A\in\mathcal F}p^{|A|}(1-p)^{|E|-|A|}.
$$

For **every $0\le p\le 1/2$**, every intersecting subfamily $\mathcal I$ of a downset $\mathcal D$ satisfies

$$
\mu_p(\mathcal I)\le\mu_p(\mathcal S_i)
$$

for some $i\in E$, where $\mathcal S_i=\{A\in\mathcal D:i\in A\}$. As in the counting theorem, the ground set is nonempty to name a center; the empty ground set is handled separately. Both endpoints $p=0$ and $p=1/2$ are included, with the usual convention $0^0=1$ in the atom weights.

[Chvatal/Biased.lean](Chvatal/Biased.lean) defines `biasedWeight p A` and `biasedMeasure p F` by these formulas and proves:

```lean
theorem chvatal_biased [Nonempty α] (D I : Finset (Finset α))
    (hD : IsDownset D) (hID : I ⊆ D) (hI : IsIntersecting I)
    (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    ∃ i : α, biasedMeasure p I ≤ biasedMeasure p (star D i)
```

`exists_maximum_biased_star` chooses a single star that maximizes $\mu_p$ among all intersecting subfamilies of the downset. Its center may depend on $p$ and $\mathcal D$, but is independent of the competing family.

The proof follows the paragraph's weighted Kleitman argument. A finite layer decomposition extends the downset inequality to every nonnegative antitone function $h$. The theorem `kleitman_kahn_weighted` proves that the same nonnegative, normalized Kahn coefficients work simultaneously for every such $h$:

$$
\sum_{A\in\mathcal U}h(A)
\le \sum_i c_i\sum_{A\ni i}h(A).
$$

These unnormalized sums are equivalent to the paper's uniform-expectation formulation after division by $2^{|E|}$. For $0\le p\le1/2$, the function $h(A)=p^{|A|}(1-p)^{|E|-|A|}1_{A\in\mathcal D}$ is nonnegative and antitone. `kleitman_choice_biased` therefore gives

$$
\mu_p(\mathcal U\cap\mathcal D)
\le \sum_i c_i\mu_p(\mathcal S_i).
$$

Extending $\mathcal I$ to a maximal intersecting family and bounding this convex combination by a largest star proves the claim. `kleitman_choice_weighted` and `kleitman_choice_biased` also support arbitrary coordinate choices in the Fourier allocation. `biasedMeasure_eq_zero_of_isEmpty` covers the empty ground type.

## Projection packing theorem

[Theorem 3 of the paper](https://arxiv.org/html/2609.28404v2#S4) assigns a complex subspace $U_A\subseteq\mathbb C^d$ to each $A\in\mathcal D$, subject to $U_A\perp U_B$ whenever $A\cap B=\varnothing$. This includes $A=B=\varnothing$, forcing the empty set's subspace to be zero. The packing value is

$$
\frac{1}{d}\sum_{A\in\mathcal D}\dim_{\mathbb C} U_A.
$$

**Projection packing theorem.** For every positive integer $d$, the largest packing value equals the largest star size. The upper bound holds for arbitrary subspaces. It is attained by assigning $\mathbb C^d$ to each member of a largest star and the zero subspace elsewhere.

`Chvatal.projection_packing` in [Chvatal/ProjectionPacking.lean](Chvatal/ProjectionPacking.lean) chooses one largest star and proves optimality simultaneously for every positive dimension. Subspaces use Mathlib's `Submodule ℂ (EuclideanSpace ℂ (Fin d))`; `IsProjectionPacking` expresses precisely the orthogonality condition, and `projectionPackingValue` is the normalized sum of complex dimensions. Assignments are represented on the whole Boolean cube, but values outside the downset impose no constraints and do not contribute to the packing value.

The public statement is:

```lean
theorem projection_packing [Nonempty α]
    (D : Finset (Finset α)) (hD : IsDownset D) :
    ∃ i : α, (∀ j, (star D j).card ≤ (star D i).card) ∧
      ∀ d : ℕ, 0 < d →
        ∃ U : Finset α → Submodule ℂ (EuclideanSpace ℂ (Fin d)),
          IsProjectionPacking D U ∧ projectionPackingValue D U = (star D i).card ∧
          ∀ W : Finset α → Submodule ℂ (EuclideanSpace ℂ (Fin d)),
            IsProjectionPacking D W → projectionPackingValue D W ≤ (star D i).card
```

The proof follows Section 4 of the paper. First, `packingUp` replaces an arbitrary packing by its monotone span closure, preserving orthogonality and increasing dimensions. Its orthogonal projections define the matrix-valued witness $h(T)=P_T-P_{\overline T}$. Complex Fourier Parseval bounds its energy by $d$, and the existing overlap estimate gives the upper bound. For the lower bound, tensor the principal-downset and signed indicators with bases of the assigned subspaces. These give independent eigenvectors of eigenvalues $-1$ and $+1$ in the restricted complex block matrix.

`projectionPackingValue_le_of_star_bound` supplies the upper bound for any common bound on star sizes; `starProjectionPacking_isPacking` and `starProjectionPacking_value` prove attainment.

## File and definition guide

All declarations below are in namespace `Chvatal`.

| File | Definitions | Part of the proof |
| --- | --- | --- |
| [Chvatal/Cube.lean](Chvatal/Cube.lean) | `chi`: real Walsh characters; `toggle`: symmetric-difference equivalence; `walsh`: unnormalized Walsh transform; `fourier`: normalized Fourier transform; `kernel`: convolution matrix; `downIndicator`: $p_A$; `signedIndicator`: $q_A$. | Character identities and orthogonality (`chi_orthogonal`), inversion (`walsh_twice`), Parseval (`fourier_parseval`), the multiplier action (`kernel_action`, `kernel_eigen`), and Fourier support identities (`walsh_downIndicator_zero`, `walsh_signedIndicator`). |
| [Chvatal/Counting.lean](Chvatal/Counting.lean) | `star D i`: the star centered at `i`; `overlap D T`: those $A\in\mathcal D$ for which $A\triangle T\in\mathcal D$. | `overlap_card_le` proves the pair-counting bound. `energy_reindex` groups entries by symmetric difference. `energy_upper` proves the upper bound for any nonnegative Fourier-energy weights with zero weight at the empty set and total weight at most one. |
| [Chvatal/Spectral.lean](Chvatal/Spectral.lean) | No new definitions. | The general linear-algebra argument: `eigenvector_card_le` bounds eigenvalue multiplicities, `trace_square` expresses the trace as a sum of squared eigenvalues, and `spectral_lower` counts independent $-1$ and $+1$ eigenvectors. Uses Mathlib's spectral theorem and the bound of geometric by algebraic multiplicity. |
| [Chvatal/Witness.lean](Chvatal/Witness.lean) | `IsDownset`, `IsIntersecting`; `up`: upward closure; `upIndicator`: its real indicator; `witness`: the function $h$ above. | Proves the witness's mean-zero and norm bounds, the two eigenvector identities (`down_eigen`, `signed_eigen`), independence by triangularity (`down_independent`, `signed_independent`), support and restriction to $\mathcal D$ (`down_support`, `restrict_eigen`), and the lower bound with a fixed containing witness family (`witness_lower_subset`), specialized in `witness_lower`. |
| [Chvatal/Main.lean](Chvatal/Main.lean) | No new definitions. | Combines the bounds in `card_le_of_star_bound`, proves `chvatal` and `exists_maximum_star`, and handles the empty ground type. |
| [Chvatal/Kleitman.lean](Chvatal/Kleitman.lean) | `IsMaximalIntersecting`, `choiceCoefficient`, `maxChoice`, `kahnCoefficient`. | Maximal-family witness identities, normalized Fourier allocations, and Kleitman's inequality with arbitrary choices and Kahn's formula. |
| [Chvatal/Biased.lean](Chvatal/Biased.lean) | `biasedWeight`, `biasedMeasure`. | Finite layer decomposition, weighted Kleitman inequalities, the biased inequality for arbitrary Fourier allocations, and `chvatal_biased` / `exists_maximum_biased_star` for $0≤p≤1/2$. |
| [Chvatal/ComplexCube.lean](Chvatal/ComplexCube.lean) | `complexWalsh`, `complexFourier`, `blockFourier`, `blockKernel`. | Complex Fourier inversion and Parseval, and the action of matrix-valued Fourier multipliers. |
| [Chvatal/ComplexSpectral.lean](Chvatal/ComplexSpectral.lean) | No new definitions. | Complex Hermitian eigenvalue multiplicities and the Frobenius-energy lower bound. |
| [Chvatal/ProjectionPacking.lean](Chvatal/ProjectionPacking.lean) | `IsProjectionPacking`, `projectionPackingValue`, `packingUp`, `projectionMatrix`, `packingWitness`, `starProjectionPacking`. | Monotone closure, block spectral bounds, and the optimal packing value in every positive dimension. |
| [Chvatal.lean](Chvatal.lean) | No new definitions. | Public entry point: `import Chvatal` imports the complete proof. |
| [Audit.lean](Audit.lean) | No new definitions. | Prints the axioms and checks the main theorems and the biased extension with the mathematical definitions expanded. |

The dependency order is `Cube → Counting`, `Cube + Spectral → Witness`, and `Counting + Witness → Main → Kleitman → Biased`. The complex Fourier and spectral modules extend this machinery for `ProjectionPacking`. The formalization covers all three main theorems of the paper; it also includes the weighted Kleitman and $p$-biased Chvátal extensions at the end of Section 3. It does not include the other weighted or correlation extensions, an explicit transport construction, or a separate formalization of quantum independent sets.

## Build and verify

The project pins Lean **4.27.0** and Mathlib **v4.27.0** (commit `a3a10db0e9d66acbebf76c5e6a135066525ac900`). Transitive dependency commits are recorded in [lake-manifest.json](lake-manifest.json).

With Elan/Lake installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The first command obtains Mathlib's compiled cache. Build products and dependency checkouts under `.lake/` are not tracked.

The proof is general for every finite ground type; it is not a check of finitely many instances. There are no `sorry`/`admit` placeholders, no newly declared axioms, and no `native_decide` proofs in this project. The axiom audit for the main results reports exactly Lean's standard logical axioms:

```text
[propext, Classical.choice, Quot.sound]
```
