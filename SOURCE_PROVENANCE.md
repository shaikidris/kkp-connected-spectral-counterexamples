# Source provenance

This repository contains the substantive Lean proof of the connected graph
counterexample family described in [README.md](README.md). Its KKP modules
implement the graph construction, exact integer-vector certificate, and
adjacency-matrix compression. The mathematical target is the exact inequality
of Li, Liu and Zhang (Conjecture 5.4 of arXiv:2511.15431v3), restated by Kannan,
Kumar and Pragada (Conjecture 1.16 of arXiv:2512.01409v2).

The Lean development used the informal manuscript
*Asymptotic rank two spectral bounds and a color critical counterexample*, section
"A connected color-critical counterexample", as its mathematical source.
The public account of the same construction and certificate is Idris Ali Shaik,
[*Three conjectures on the first two graph eigenvalues*](https://hexagonmath.org/2610.00305v1),
v1 (17 October 2026), Theorem 1.2 and Section 4. Section 8 identifies
`KKP.connected_counterexample_family` and `KKP.unbounded_connected_counterexamples`.
The public citation supplies an accessible exposition while retaining the informal
proof lineage. The conjecture references provide context; BN supplies reused Lean
code. No novelty or priority claim is made.

| Role | Repository | Commit |
|---|---|---|
| Registered v1 proof snapshot ([PALOMAR-2026-10-16-000012 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-16-000012&version=1)) | [Palomar archive](https://github.com/PalomarArchive/shaikidris--kkp-connected-spectral-counterexamples--a1b9d82c88cb/tree/c611a4a733fe796809cd941f96ff8f2c294fd1ef) | `c611a4a733fe796809cd941f96ff8f2c294fd1ef` |
| Reused spectral proof source by Shengtong Zhang | ShengtongZhang-alt/BN | 5f4741254398424b730c9a893220a51e1cd829c5 |
| Mathlib dependency of this package | leanprover-community/mathlib4 | c55e6e786f49471c72fbddbec5415808896aec1e |
| Mechanically verified candidate (official run 38806182664) | shaikidris/kkp-connected-spectral-counterexamples | 03eddd88ba6b43c03f4c8fc844f969988e62bc64 |

`KKP.Bridge`, `KKP.Witness`, `KKP.Certificate`, `KKP.Compression`, and
`KKP.SpectralWitness` contain the graph counterexample proof. `BN.Basic.Inner`,
`BN.Basic.Spectrum`, `BN.Definition`, `BN.Spectral.Interlace`, and
`BN.Spectral.Variational` adapt the cited BN spectral support to the selected
toolchain. These five files retain Shengtong Zhang's copyright, authorship,
and Apache-2.0 notices. The BN revision identifies the reused code; the Mathlib
revision identifies a software dependency. The submitted repository contains
both the KKP proof and these adapted BN modules.

The immutable candidate commit and its verification receipts are identified by
the corresponding GitHub Actions run. They are separate from the upstream
source and dependency revisions above. AI assistance and review scope are
recorded in [formalization.yaml](formalization.yaml).
