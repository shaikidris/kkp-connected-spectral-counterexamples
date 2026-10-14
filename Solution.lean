module
public import KKP.SpectralWitness
@[expose] public section

/-! # The connected counterexample family and its exact positive spectral gap -/

namespace KKP
/-- The complete graph, forbidden-subgraph, and ordered-spectrum certificate. -/
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
  refine ⟨forbidden_chromaticNumber, forbidden_color_critical,
    bridgeGraph_connected s (by omega), bridgeGraph_free s, bridgeGraph_edge_count s (by omega),
    ?_, bridgeGraph_ordered_excess s hs⟩
  have h := bridgeGraph_spectral_gap s hs
  rwa [BN.F_adjMatrix_eq (bridgeGraph s) (bridgeGraph_noncomplete s hs)] at h
end KKP
