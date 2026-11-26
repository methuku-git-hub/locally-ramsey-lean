# Locally Ramsey graphs in Lean

This repository contains a Lean 4 and Mathlib formalization of Theorem 1 of
*A simplified proof of a lower bound for locally Ramsey graphs*, by József
Balogh, Matija Bucić, Haoran Luo and Abhishek Methuku. The targets are
`LocallyRamsey.lower_bound` and `LocallyRamsey.upper_bound`.

## Abstract

Let $m_n(r)$ be the least $m$ for which some $n$-vertex graph
contains both a clique and an independent set of order $r$ in every
set of $m$ vertices. With logarithms to base two, put $r=\lceil\log n\rceil$.
In 1991 Erdős asked whether $m_n(r)\le\lceil(\log n)^3\rceil$
for arbitrarily large $n$. We answer this question negatively by proving that

$$
m_n(r)>\frac{(\log n)^{7/2}}{(\log\log n)^{24}}
$$

for all sufficiently large $n$.
This improves the lower bound of Alon and Sudakov (2007).
We also give a simple construction that improves the upper bound of
Alon, Bucić and Sudakov (2021) from $2^{\,2^{(\log\log n)^{1/2+o(1)}}}$
to $2^{(9/2+o(1))(\log\log n)^2}$.

## The mathematical statement

**Theorem 1.** For every $\varepsilon>0$ and all sufficiently large $n$,
with $r=\lceil\log n\rceil$,

$$
\frac{(\log n)^{7/2}}{(\log\log n)^{24}}
<m_n(r)\le 2^{(9/2+\varepsilon)(\log\log n)^2}.
$$

### Exact Lean statements

In the `LocallyRamsey` namespace, [`threshold n r`](Challenge.lean#L28) is
$m_n(r)$ and [`target n`](Challenge.lean#L33) is $\lceil\log n\rceil$.
The statement of [`lower_bound`](Challenge.lean#L37) is

```lean
theorem lower_bound :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (Real.logb 2 (n : ℝ)) ^ (7 / 2 : ℝ) / (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 24
        < (threshold n (target n) : ℝ)
```

The statement of [`upper_bound`](Challenge.lean#L45) is

```lean
theorem upper_bound :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (threshold n (target n) : ℝ) ≤
        (2 : ℝ) ^ ((9 / 2 + ε) * (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2)
```

### Proof entry point

[`Challenge.lean`](Challenge.lean) independently states the two bounds and
uses the intentional placeholders required for the comparison.
[`Solution.lean`](Solution.lean) supplies both proofs from the
[lower-bound](LocallyRamsey/Lower/MainBound.lean) and
[upper-bound](LocallyRamsey/Upper/LocalBound.lean) developments. Comparator
checks the statements and proofs in separate environments.

## Building

The project uses Lean `v4.35.0`, pinned in [`lean-toolchain`](lean-toolchain),
with dependencies pinned in [`lake-manifest.json`](lake-manifest.json).
With Git and [Elan](https://github.com/leanprover/elan) installed, run

```bash
git clone https://github.com/methuku-git-hub/locally-ramsey-lean.git
cd locally-ramsey-lean
lake exe cache get
lake build LocallyRamsey +Challenge:olean +Solution:olean
lake comparator --config comparator.json
```

## Verification

The [local Comparator run](verification/comparator-theorem1.log) checked both
bounds with Lean's kernel and NanoDa. The [axiom audit](verification/axioms.log)
records `propext`, `Classical.choice` and `Quot.sound` as the only axioms
used by the two proofs. The local macOS run used Comparator's sandbox-disabled
option.

## Sources and attribution

The mathematical source is Theorem 1 of the revised 23 November 2026
manuscript. [`formalization.yaml`](formalization.yaml) records the source
hash and the scope of the formalization.

Abhishek Methuku is the formalization author and responsible maintainer.
OpenAI Codex developed and checked the Lean proofs under his direction.

## License and further reading

The repository is licensed under [Apache 2.0](LICENSE). See the
[project metadata](formalization.yaml) and the
[Comparator configuration](comparator.json) for further details.
