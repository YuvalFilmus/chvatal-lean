# Chvátal's conjecture in Lean

A Lean formalization of the scalar spectral proof of Chvátal's conjecture, following *Chvátal's conjecture: a proof from The Book* by David Ellis, Yuval Filmus, and Ehud Friedgut.

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

## Proof overview

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

## File and definition guide

All declarations below are in namespace `Chvatal`.

| File | Definitions | Part of the proof |
| --- | --- | --- |
| [Chvatal/Cube.lean](Chvatal/Cube.lean) | `chi`: real Walsh characters; `toggle`: symmetric-difference equivalence; `walsh`: unnormalized Walsh transform; `fourier`: normalized Fourier transform; `kernel`: convolution matrix; `downIndicator`: $p_A$; `signedIndicator`: $q_A$. | Character identities and orthogonality (`chi_orthogonal`), inversion (`walsh_twice`), Parseval (`fourier_parseval`), the multiplier action (`kernel_action`, `kernel_eigen`), and Fourier support identities (`walsh_downIndicator_zero`, `walsh_signedIndicator`). |
| [Chvatal/Counting.lean](Chvatal/Counting.lean) | `star D i`: the star centered at `i`; `overlap D T`: those $A\in\mathcal D$ for which $A\triangle T\in\mathcal D$. | `overlap_card_le` proves the pair-counting bound. `energy_reindex` groups entries by symmetric difference. `energy_upper` proves the upper bound for any nonnegative Fourier-energy weights with zero weight at the empty set and total weight at most one. |
| [Chvatal/Spectral.lean](Chvatal/Spectral.lean) | No new definitions. | The general linear-algebra argument: `eigenvector_card_le` bounds eigenvalue multiplicities, `trace_square` expresses the trace as a sum of squared eigenvalues, and `spectral_lower` counts independent $-1$ and $+1$ eigenvectors. Uses Mathlib's spectral theorem and the bound of geometric by algebraic multiplicity. |
| [Chvatal/Witness.lean](Chvatal/Witness.lean) | `IsDownset`, `IsIntersecting`; `up`: upward closure; `upIndicator`: its real indicator; `witness`: the function $h$ above. | Proves the witness's mean-zero and norm bounds, the two eigenvector identities (`down_eigen`, `signed_eigen`), independence by triangularity (`down_independent`, `signed_independent`), support and restriction to $\mathcal D$ (`down_support`, `restrict_eigen`), and the complete lower bound (`witness_lower`). |
| [Chvatal/Main.lean](Chvatal/Main.lean) | No new definitions. | Combines the bounds in `card_le_of_star_bound`, proves `chvatal` and `exists_maximum_star`, and handles the empty ground type. |
| [Chvatal.lean](Chvatal.lean) | No new definitions. | Public entry point: `import Chvatal` imports the complete proof. |
| [Audit.lean](Audit.lean) | No new definitions. | Prints the axioms used by the main theorems and checks the cardinality statement with the family definitions expanded. |

The dependency order is `Cube → Counting`, `Cube + Spectral → Witness`, and `Counting + Witness → Main`. The formalization covers the scalar theorem; it does not include the weighted, projection packing, flow, or correlation extensions.

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
