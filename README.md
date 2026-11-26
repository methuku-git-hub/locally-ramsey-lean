# Locally Ramsey graphs in Lean

This repository contains a Lean 4 and Mathlib formalization of Theorem 1 of
*A simplified proof of a lower bound for locally Ramsey graphs*, by József
Balogh, Matija Bucić, Haoran Luo and Abhishek Methuku.

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

Theorem 1 concerns $m_n(\lceil\log_2 n\rceil)$ and gives a strict
lower bound with exponent $7/2$ and an asymptotic upper bound with leading
coefficient $9/2$. The upper inequality is formalized with an arbitrary
fixed $\varepsilon>0$ added to $9/2$, for all sufficiently large $n$.

### Exact Lean statements and proof entry points

| Bound | Statement | Proof |
| --- | --- | --- |
| Lower | [`LocallyRamsey.lower_bound`](Challenge.lean#L37) | [`Solution.lean`](Solution.lean#L11), [lower-bound development](LocallyRamsey/Lower/MainBound.lean) |
| Upper | [`LocallyRamsey.upper_bound`](Challenge.lean#L45) | [`Solution.lean`](Solution.lean#L19), [upper-bound development](LocallyRamsey/Upper/LocalBound.lean) |

[`Challenge.lean`](Challenge.lean) independently states the two bounds and
uses the intentional placeholders required for the comparison. Comparator
checks the proofs supplied by [`Solution.lean`](Solution.lean) in a separate
environment.

## Building

The project uses Lean `v4.35.0`, pinned in [`lean-toolchain`](lean-toolchain),
with dependencies pinned in [`lake-manifest.json`](lake-manifest.json). With
[Elan](https://github.com/leanprover/elan) installed, use these commands from
the repository root.

```sh
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

## Provenance

[`formalization.yaml`](formalization.yaml) records the manuscript revision,
the scope of the formalization, and the use of OpenAI Codex in developing and
checking the Lean proofs.
