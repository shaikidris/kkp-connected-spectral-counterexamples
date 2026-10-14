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
in KKP Conjecture 1.16 and Li–Liu–Zhang Conjecture 5.4, including the connected
convention. No novelty or priority claim is made.

The graph definitions in `Challenge.lean` show every adjacency rule. Its two
selected declarations state the full family certificate and unbounded edge
counts. `Solution.lean` uses the concrete graph proofs, exact integer-vector
quadratic forms, and the compression of the actual adjacency matrix. The
compression bound follows from the kernel-checked rank-two variational theorem;
no interlacing or graph-spectrum axiom is introduced. The selected eigenvalues
are ordered algebraic eigenvalues, not absolute eigenvalues or the scalar
certificate expression. Noncompleteness identifies their squared sum with the
positive-spectrum statistic.

Commands from this directory:

```sh
lake build
lake comparator --config comparator.json
```

The package uses Lean 4.35.0-rc3 and locked Mathlib
`dd56d02cb7a58fa066c4a2c7fddec3cbb59ae8df`. Its local development audit reports
only `propext`, `Classical.choice`, and `Quot.sound`. The supported Comparator
sandbox requires Linux; independent-kernel verification and the complete
Palomar mechanical and rendering rehearsals have not run. The public source
repository is <https://github.com/shaikidris/kkp-connected-spectral-counterexamples>.
Its GitHub rehearsal runs the pinned Palomar preparation entry point and a
sandboxed Linux Comparator with NanoDa and con-ron. This rehearsal is distinct
from the full Palomar workflow, rendering, editorial review, and registration.

The informal source is the supplied research manuscript and exact certificate.
The BN spectral support retains Shengtong Zhang's source notices and licence.
See `SOURCE_PROVENANCE.md` for source and dependency roles.
