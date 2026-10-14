module
public import KKP.Bridge
@[expose] public section

/-! # Exact adjacency identities for the two integer witnesses -/

namespace KKP
open Matrix

lemma zero_coordinate_card (s : ℕ) (hs : 0 < s) :
    ((Finset.univ : Finset (Fin s)).filter fun x => x.val = 0).card = 1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨⟨0, hs⟩, ?_⟩
  ext x
  simp [Fin.ext_iff]

lemma zero_pair_card (s : ℕ) (hs : 0 < s) :
    ((Finset.univ : Finset (Fin 3 × Fin s)).filter fun x =>
      x.1 = 0 ∧ x.2.val = 0).card = 1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨(0, ⟨0, hs⟩), ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Prod.mk.injEq, Prod.eta]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact Prod.ext h₁ (Fin.ext h₂)
  · intro h
    cases h
    exact ⟨rfl, rfl⟩

/-- The adjacency action on the first integer vector. -/
theorem adjacency_witnessU (s : ℕ) (hs : 0 < s) (v : BridgeVertex s) :
    ((bridgeGraph s).adjMatrix ℝ *ᵥ witnessU s) v =
      match v with
      | .inl _ => 2 * (s : ℝ)
      | .inr b => if b.val = 0 then 1 else 0 := by
  cases v with
  | inl p =>
    rcases p with ⟨i, a⟩
    fin_cases i <;>
      simp [mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
        SimpleGraph.adjMatrix, bridgeGraph, bridgeAdj, witnessU, Fin.sum_univ_succ]
    all_goals ring
  | inr b =>
    by_cases hb : b.val = 0 <;>
      simp [mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
        SimpleGraph.adjMatrix, bridgeGraph, bridgeAdj, witnessU,
        Fin.sum_univ_succ, hb, sum_zero_coordinate s hs, zero_pair_card s hs]

/-- The adjacency action on the second integer vector. -/
theorem adjacency_witnessV (s : ℕ) (hs : 0 < s) (v : BridgeVertex s) :
    ((bridgeGraph s).adjMatrix ℝ *ᵥ witnessV s) v =
      match v with
      | .inl (i, a) => if i.val = 0 ∧ a.val = 0 then 3 * (s : ℝ) else 0
      | .inr b => 9 * (s : ℝ) + if b.val = 0 then (s : ℝ) - 1 else 0 := by
  cases v with
  | inl p =>
    rcases p with ⟨i, a⟩
    fin_cases i <;> by_cases ha : a.val = 0 <;>
      simp [mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
        SimpleGraph.adjMatrix, bridgeGraph, bridgeAdj, witnessV,
        Fin.sum_univ_succ, ha, balanced_part_sum s hs]
    all_goals ring
  | inr b =>
    fin_cases b <;>
      simp +contextual [mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
        SimpleGraph.adjMatrix, bridgeGraph, bridgeAdj, witnessV,
        Fin.sum_univ_succ, sum_zero_coordinate s hs]
    all_goals ring

/-- Raw quadratic form of the first integer witness. -/
theorem witnessU_quadratic (s : ℕ) (hs : 0 < s) :
    witnessU s ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ witnessU s = 6 * (s : ℝ) ^ 2 := by
  simp [dotProduct, adjacency_witnessU s hs, Fintype.sum_sum_type,
    witnessU, Fintype.card_prod]
  ring

/-- Raw mixed adjacency form of the two integer witnesses. -/
theorem witnesses_mixed (s : ℕ) (hs : 0 < s) :
    witnessU s ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ witnessV s = 3 * (s : ℝ) := by
  simp [dotProduct, adjacency_witnessV s hs, Fintype.sum_sum_type,
    Fintype.sum_prod_type, witnessU, Fin.sum_univ_succ, sum_zero_coordinate s hs]

/-- Raw quadratic form of the second integer witness. -/
theorem witnessV_quadratic (s : ℕ) (hs : 0 < s) :
    witnessV s ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ witnessV s =
      (s : ℝ) * (114 * (s : ℝ) - 6) := by
  simp only [dotProduct, adjacency_witnessV s hs, Fintype.sum_sum_type,
    Fintype.sum_prod_type, witnessV, Fin.sum_univ_succ, mul_ite, ite_mul,
    sum_zero_coordinate s hs, ite_self, ite_true, ite_false]
  norm_num
  simp +contextual [ite_mul, mul_ite, sum_zero_coordinate s hs]
  ring

lemma sum_zero_coordinate_nat (s : ℕ) (hs : 0 < s) (t : ℕ) :
    (∑ a : Fin s, if a.val = 0 then t else 0) = t := by
  let a₀ : Fin s := ⟨0, hs⟩
  have heq (a : Fin s) : (a.val = 0) ↔ a = a₀ := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; subst a; rfl
  simp only [heq]
  simp

/-- The graph has exactly `3s²+7` unordered edges. -/
theorem bridgeGraph_edge_count (s : ℕ) (hs : 0 < s) :
    (bridgeGraph s).edgeFinset.card = 3 * s ^ 2 + 7 := by
  have hdegree (v : BridgeVertex s) : (bridgeGraph s).degree v =
      ∑ w : BridgeVertex s, if (bridgeGraph s).Adj v w then 1 else 0 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    simp
  have hsum : (∑ v : BridgeVertex s, ∑ w : BridgeVertex s,
      if (bridgeGraph s).Adj v w then (1 : ℕ) else 0) = 6 * s ^ 2 + 14 := by
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.sum_add_distrib,
      bridgeGraph, bridgeAdj, Fin.sum_univ_succ, sum_zero_coordinate_nat s hs]
    rw [zero_coordinate_card s hs, zero_pair_card s hs]
    ring
  have h := (bridgeGraph s).sum_degrees_eq_twice_card_edges
  simp_rw [hdegree] at h
  rw [hsum] at h
  omega

end KKP
