module
public import Mathlib
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
@[expose] public section

/-!
# Connected counterexamples to the exact color-critical spectral bound

The forbidden graph is `K₅−e = K₃ ∨ I₂`, with chromatic number four and a
chromatic-number-reducing core edge. The graphs are `K_{s,s,s}` and `K₄`
joined by exactly one bridge. They are connected and forbidden-free, have
`3s²+7` edges, and violate the ordered two-eigenvalue `4m/3` bound for every
integer `s≥3`, at arbitrarily large edge counts.
-/

namespace BN
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Adjacency eigenvalues indexed by vertices, counting algebraic multiplicity. -/
noncomputable def adjacencyEigenvalues (G : SimpleGraph V) [DecidableRel G.Adj] : V → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues
/-- Adjacency eigenvalues in nonincreasing order, with multiplicity. -/
noncomputable def adjacencyEigenvalues₀ (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin (Fintype.card V) → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues₀
/-- The largest adjacency eigenvalue. -/
noncomputable def lambda1 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨0, Fintype.card_pos⟩
/-- The second largest ordered adjacency eigenvalue. -/
noncomputable def lambda2 (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨1, Fintype.one_lt_card⟩
end BN

namespace KKP
/-- Three parts of size `s`, together with four clique vertices. -/
abbrev BridgeVertex (s : ℕ) := (Fin 3 × Fin s) ⊕ Fin 4
/-- Tripartite adjacency, clique adjacency, and the unique zero-coordinate bridge. -/
def bridgeAdj (s : ℕ) : BridgeVertex s → BridgeVertex s → Prop
  | .inl (i, _), .inl (j, _) => i ≠ j
  | .inr a, .inr b => a ≠ b
  | .inl (i, a), .inr b => i.val = 0 ∧ a.val = 0 ∧ b.val = 0
  | .inr b, .inl (i, a) => i.val = 0 ∧ a.val = 0 ∧ b.val = 0
/-- The literal simple graph in the counterexample family. -/
def bridgeGraph (s : ℕ) : SimpleGraph (BridgeVertex s) where
  Adj := bridgeAdj s
  symm := ⟨by intro v w; cases v <;> cases w <;> simp_all [bridgeAdj, ne_comm]⟩
  loopless := ⟨by intro v; cases v <;> simp [bridgeAdj]⟩
instance bridgeAdjDecidable (s : ℕ) : DecidableRel (bridgeGraph s).Adj := by
  intro v w
  cases v <;> cases w <;> simp only [bridgeGraph, bridgeAdj] <;> infer_instance
/-- The complete graph on five vertices with only the edge `{3,4}` removed. -/
def forbiddenGraph : SimpleGraph (Fin 5) where
  Adj i j := i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)
  symm := ⟨by intro i j; simp [ne_comm, and_comm]⟩
  loopless := ⟨by intro i; simp⟩
instance forbiddenAdjDecidable : DecidableRel forbiddenGraph.Adj := by
  intro i j
  dsimp [forbiddenGraph]
  infer_instance

/-- Every graph in the stated range is a connected counterexample, including the exact positive
gap certificate. Forbidden copies are injective edge-preserving maps, hence need not be induced. -/
theorem connected_counterexample_family (s : ℕ) (hs : 3 ≤ s) :
    forbiddenGraph.chromaticNumber = 4 ∧
      (∃ i j : Fin 5, forbiddenGraph.Adj i j ∧
        (forbiddenGraph.deleteEdges {s(i, j)}).chromaticNumber < forbiddenGraph.chromaticNumber) ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      (bridgeGraph s).edgeFinset.card = 3 * s ^ 2 + 7 ∧
      (656 * (s : ℝ) ^ 2 - 1366 * (s : ℝ) + 62) /
          (3 * (37 * (s : ℝ) - 1) ^ 2) ≤
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 -
          (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) ∧
      (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) <
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 := by
  sorry

/-- The connected counterexamples have arbitrarily large edge counts. This defeats the
“sufficiently large” quantifier in the exact color-critical inequality. -/
theorem unbounded_connected_counterexamples (B : ℕ) :
    ∃ s : ℕ, 3 ≤ s ∧ B ≤ (bridgeGraph s).edgeFinset.card ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) <
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 := by
  sorry
end KKP
