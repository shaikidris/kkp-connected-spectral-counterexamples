# Connected counterexamples to the exact color-critical spectral bound

Let `F = K₅−e = K₃ ∨ I₂`. It has chromatic number four, and deleting a core
edge lowers its chromatic number. For every integer `s≥3`, join `K_{s,s,s}`
and `K₄` by one bridge. The resulting graph `G_s` is connected and `F`-free,
has `m=3s²+7` unordered edges, and satisfies

\[
\lambda_1(G_s)^2+\lambda_2(G_s)^2-\frac43m
\ge\frac{656s^2-1366s+62}{3(37s-1)^2}>0.
\]

The family has arbitrarily large edge counts, so it refutes the exact assertion
in [Kannan–Kumar–Pragada Conjecture 1.16](https://arxiv.org/html/2512.01409v2)
and [Li–Liu–Zhang Conjecture 5.4](https://arxiv.org/html/2511.15431v3), including
the connected convention. No novelty or priority claim is made. The bounded
positive excess does not refute the asymptotic bound in Conjecture 1.17.

The graph definitions in `Challenge.lean` show every adjacency rule. Its two
selected declarations state the full family certificate and unbounded edge
counts. `Solution.lean` uses the concrete graph proofs, exact integer-vector
quadratic forms, and the compression of the actual adjacency matrix. The
compression bound follows from the kernel-checked rank-two variational theorem;
no interlacing or graph-spectrum axiom is introduced. The selected eigenvalues
are ordered algebraic eigenvalues, not absolute eigenvalues or the scalar
certificate expression. Noncompleteness identifies their sum of squares with the
positive-spectrum statistic.

Commands from this directory:

```sh
lake build
lake comparator --config comparator.json
```

The package pins Lean 4.35.0-rc3 and Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, including Mathlib's complete
dependency closure. The supported Comparator sandbox requires Linux and permits
only `propext`, `Classical.choice`, and `Quot.sound`.

The [release rehearsal](.github/workflows/release-rehearsal.yml) runs the pinned
full Palomar verifier, Comparator with NanoDa and con-ron, and the Challenge
renderer, then checks the reports and rendered declarations in a browser.
Commit-specific reports are preserved in the
[GitHub Actions artifacts](https://github.com/shaikidris/kkp-connected-spectral-counterexamples/actions).
Editorial review and registration are separate gates.

The connected family and exact certificate are presented in Idris Ali Shaik,
[*Three conjectures on the first two graph eigenvalues*](https://hexagonmath.org/2610.00305v1),
v1, Theorem 1.2 and Section 4. Section 8 identifies the selected Lean declarations
`KKP.connected_counterexample_family` and `KKP.unbounded_connected_counterexamples`.

[PALOMAR-2026-10-16-000012 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-16-000012&version=1)
registers the proof snapshot at `c611a4a733fe796809cd941f96ff8f2c294fd1ef`, preserved
in the [Palomar archive](https://github.com/PalomarArchive/shaikidris--kkp-connected-spectral-counterexamples--a1b9d82c88cb/tree/c611a4a733fe796809cd941f96ff8f2c294fd1ef).
The paper is CC BY 4.0; this repository's code is Apache-2.0.

The five BN modules adapt spectral
definitions and
variational lemmas from [Shengtong Zhang's BN development](https://github.com/ShengtongZhang-alt/BN/tree/5f4741254398424b730c9a893220a51e1cd829c5),
with its Apache-2.0 notices retained. See [SOURCE_PROVENANCE.md](SOURCE_PROVENANCE.md)
for the module boundaries and source and dependency revisions.
