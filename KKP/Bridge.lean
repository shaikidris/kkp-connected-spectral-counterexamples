module
public import Mathlib
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
@[expose] public section

/-!
# The tripartite graph and clique joined by a bridge

The vertices are three classes of size `s`, together with four clique vertices.
Only the vertices with zero coordinates are joined across the two components.
All forbidden copies mean injective graph homomorphisms, hence need not be induced.
-/

namespace KKP

/-- Vertices of the graph `K_{s,s,s}` joined to `K₄`. -/
abbrev BridgeVertex (s : ℕ) := (Fin 3 × Fin s) ⊕ Fin 4

/-- The literal adjacency relation: tripartite edges, clique edges, and one bridge. -/
def bridgeAdj (s : ℕ) : BridgeVertex s → BridgeVertex s → Prop
  | .inl (i, _), .inl (j, _) => i ≠ j
  | .inr a, .inr b => a ≠ b
  | .inl (i, a), .inr b => i.val = 0 ∧ a.val = 0 ∧ b.val = 0
  | .inr b, .inl (i, a) => i.val = 0 ∧ a.val = 0 ∧ b.val = 0

/-- The connected counterexample family, with a single bridge between its components. -/
def bridgeGraph (s : ℕ) : SimpleGraph (BridgeVertex s) where
  Adj := bridgeAdj s
  symm := ⟨fun v w => match v, w with
    | .inl (_, _), .inl (_, _) => fun h => Ne.symm h
    | .inr _, .inr _ => fun h => Ne.symm h
    | .inl (_, _), .inr _ => fun h => h
    | .inr _, .inl (_, _) => fun h => h⟩
  loopless := ⟨fun v => match v with
    | .inl (_, _) => fun h => h rfl
    | .inr _ => fun h => h rfl⟩

instance bridgeAdjDecidable (s : ℕ) : DecidableRel (bridgeGraph s).Adj :=
  fun v w => match v, w with
    | .inl (i, _), .inl (j, _) => inferInstanceAs (Decidable (i ≠ j))
    | .inr a, .inr b => inferInstanceAs (Decidable (a ≠ b))
    | .inl (i, a), .inr b =>
      inferInstanceAs (Decidable (i.val = 0 ∧ a.val = 0 ∧ b.val = 0))
    | .inr b, .inl (i, a) =>
      inferInstanceAs (Decidable (i.val = 0 ∧ a.val = 0 ∧ b.val = 0))

/-- The forbidden graph `K₅` with just the edge between vertices 3 and 4 removed. -/
def forbiddenGraph : SimpleGraph (Fin 5) where
  Adj i j := i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)
  symm := ⟨fun i j h => ⟨Ne.symm h.1, fun hji => h.2 ⟨hji.2, hji.1⟩⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance forbiddenAdjDecidable : DecidableRel forbiddenGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)))

/-- Every edge of the forbidden graph is in a triangle. -/
theorem forbidden_edge_triangle {i j : Fin 5} (h : forbiddenGraph.Adj i j) :
    ∃ k : Fin 5, forbiddenGraph.Adj i k ∧ forbiddenGraph.Adj j k := by
  revert i j
  decide +kernel

/-- The bridge has no common neighbor, so belongs to no triangle. -/
theorem bridge_no_triangle (s : ℕ) (a : Fin s) :
    ¬ ∃ w, (bridgeGraph s).Adj (.inl (0, a)) w ∧
      (bridgeGraph s).Adj (.inr 0) w := by
  rintro ⟨w, h₁, h₂⟩
  cases w with
  | inl p =>
    rcases p with ⟨i, b⟩
    simp only [bridgeGraph, bridgeAdj] at h₁ h₂
    exact h₁ (Fin.ext h₂.1).symm
  | inr b =>
    simp only [bridgeGraph, bridgeAdj] at h₁ h₂
    exact h₂ (Fin.ext h₁.2.2).symm

/-- For a positive class size, every vertex can reach clique vertex zero. -/
theorem bridgeGraph_connected (s : ℕ) (hs : 0 < s) : (bridgeGraph s).Connected := by
  let a : Fin s := ⟨0, hs⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable (bridgeGraph s)).mpr
  refine ⟨.inr 0, ?_⟩
  intro w
  cases w with
  | inr b =>
    by_cases hb : b = 0
    · subst b; exact SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable (by simpa [bridgeGraph, bridgeAdj] using Ne.symm hb)
  | inl p =>
    rcases p with ⟨i, b⟩
    have hbridge : (bridgeGraph s).Reachable (.inr 0) (.inl (0, a)) :=
      SimpleGraph.Adj.reachable (by simp [bridgeGraph, bridgeAdj, a])
    by_cases hi : i = 0
    · subst i
      have h₁ : (bridgeGraph s).Adj (.inl (0, a)) (.inl (1, a)) := by
        simp [bridgeGraph, bridgeAdj]
      have h₂ : (bridgeGraph s).Adj (.inl (1, a)) (.inl (0, b)) := by
        simp [bridgeGraph, bridgeAdj]
      exact hbridge.trans (h₁.reachable.trans h₂.reachable)
    · exact hbridge.trans (SimpleGraph.Adj.reachable
        (by simpa [bridgeGraph, bridgeAdj] using Ne.symm hi))

/-- The first integer witness, equal to one on the tripartite component. -/
def witnessU (s : ℕ) : BridgeVertex s → ℝ
  | .inl _ => 1
  | .inr _ => 0

/-- The second integer witness, balanced on the first part and constant on the clique. -/
def witnessV (s : ℕ) : BridgeVertex s → ℝ
  | .inl (i, a) => if i.val = 0 then (if a.val = 0 then (s : ℝ) - 1 else -1) else 0
  | .inr _ => 3 * (s : ℝ)

/-- A triangle cannot cross the bridge. -/
theorem triangle_same_side {s : ℕ} {x y z : BridgeVertex s}
    (hxy : (bridgeGraph s).Adj x y) (hxz : (bridgeGraph s).Adj x z)
    (hyz : (bridgeGraph s).Adj y z) : x.isLeft = y.isLeft := by
  cases x with
  | inl p =>
    rcases p with ⟨i, a⟩
    cases y with
    | inl q => rfl
    | inr b =>
      cases z with
      | inl q =>
        rcases q with ⟨j, c⟩
        simp only [bridgeGraph, bridgeAdj] at hxy hxz hyz
        exact (hxz (Fin.ext (hxy.1.trans hyz.1.symm))).elim
      | inr c =>
        simp only [bridgeGraph, bridgeAdj] at hxy hxz hyz
        exact (hyz (Fin.ext (hxy.2.2.trans hxz.2.2.symm))).elim
  | inr b =>
    cases y with
    | inr c => rfl
    | inl p =>
      rcases p with ⟨i, a⟩
      cases z with
      | inl q =>
        rcases q with ⟨j, c⟩
        simp only [bridgeGraph, bridgeAdj] at hxy hxz hyz
        exact (hyz (Fin.ext (hxy.1.trans hxz.1.symm))).elim
      | inr c =>
        simp only [bridgeGraph, bridgeAdj] at hxy hxz hyz
        exact (hxz (Fin.ext (hxy.2.2.trans hyz.2.2.symm))).elim

/-- No injective, edge-preserving copy of `K₅−e` exists in the bridge graph. -/
theorem bridgeGraph_free (s : ℕ) : forbiddenGraph.Free (bridgeGraph s) := by
  classical
  rintro ⟨f⟩
  have hside (i : Fin 5) : (f i).isLeft = (f 0).isLeft := by
    by_cases hi : i = 0
    · subst i; rfl
    have ha : forbiddenGraph.Adj i 0 := by simp [forbiddenGraph, hi]
    obtain ⟨k, hik, h0k⟩ := forbidden_edge_triangle ha
    exact triangle_same_side (f.toHom.map_rel ha) (f.toHom.map_rel hik)
      (f.toHom.map_rel h0k)
  cases hf0 : f 0 with
  | inl p =>
    have hleft (i : Fin 5) : ∃ p : Fin 3 × Fin s, f i = .inl p := by
      cases hfi : f i with
      | inl q => exact ⟨q, rfl⟩
      | inr b => have h := hside i; simp [hf0, hfi] at h
    choose p hp using hleft
    let c : Fin 4 → Fin 3 := fun i => (p (i.castLE (by decide))).1
    have hc : Function.Injective c := by
      intro i j heq
      by_contra hne
      have hne' : i.castLE (show 4 ≤ 5 by decide) ≠ j.castLE (by decide) := by
        intro h; exact hne (Fin.ext (congrArg (fun x : Fin 5 => x.val) h))
      have ha : forbiddenGraph.Adj (i.castLE (by decide)) (j.castLE (by decide)) := by
        simp only [forbiddenGraph]
        exact ⟨hne', by have hi := i.isLt; have hj := j.isLt; simp only [Fin.val_castLE]; omega⟩
      have h := f.toHom.map_rel ha
      change (bridgeGraph s).Adj (f _) (f _) at h
      rw [hp, hp] at h
      exact h heq
    have hcard := Fintype.card_le_of_injective c hc
    norm_num at hcard
  | inr b =>
    have hright (i : Fin 5) : ∃ b : Fin 4, f i = .inr b := by
      cases hfi : f i with
      | inr c => exact ⟨c, rfl⟩
      | inl p => have h := hside i; simp [hf0, hfi] at h
    choose c hc using hright
    have hinj : Function.Injective c := by
      intro i j heq
      apply f.injective
      change f i = f j
      rw [hc, hc, heq]
    have hcard := Fintype.card_le_of_injective c hinj
    norm_num at hcard

open Matrix

lemma sum_zero_coordinate (s : ℕ) (hs : 0 < s) (t : ℝ) :
    (∑ a : Fin s, if a.val = 0 then t else 0) = t := by
  let a₀ : Fin s := ⟨0, hs⟩
  have heq (a : Fin s) : (a.val = 0) ↔ a = a₀ := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; subst a; rfl
  simp only [heq]
  simp

lemma balanced_part_sum (s : ℕ) (hs : 0 < s) :
    (∑ a : Fin s, if a.val = 0 then (s : ℝ) - 1 else -1) = 0 := by
  have heq (a : Fin s) :
      (if a.val = 0 then (s : ℝ) - 1 else -1) =
        (if a.val = 0 then (s : ℝ) else 0) - 1 := by split_ifs <;> ring
  simp_rw [heq]
  rw [Finset.sum_sub_distrib, sum_zero_coordinate s hs]
  simp

/-- The integer witnesses are perpendicular. -/
theorem witnesses_orthogonal (s : ℕ) (hs : 0 < s) :
    witnessU s ⬝ᵥ witnessV s = 0 := by
  simp [dotProduct, Fintype.sum_sum_type, witnessU, witnessV,
    Fintype.sum_prod_type, balanced_part_sum s hs]

/-- Squared norm of the first witness. -/
theorem witnessU_norm (s : ℕ) : witnessU s ⬝ᵥ witnessU s = 3 * (s : ℝ) := by
  simp [dotProduct, Fintype.sum_sum_type, witnessU, Fintype.card_prod]

/-- Squared norm of the second witness. -/
theorem witnessV_norm (s : ℕ) (hs : 0 < s) :
    witnessV s ⬝ᵥ witnessV s = (s : ℝ) * (37 * (s : ℝ) - 1) := by
  have heq (a : Fin s) :
      (if a.val = 0 then (s : ℝ) - 1 else -1) ^ 2 =
        (if a.val = 0 then (s : ℝ) ^ 2 - 2 * (s : ℝ) else 0) + 1 := by
    split_ifs <;> ring
  have hsum : (∑ a : Fin s, (if a.val = 0 then (s : ℝ) - 1 else -1) ^ 2) =
      (s : ℝ) ^ 2 - (s : ℝ) := by
    simp_rw [heq]
    rw [Finset.sum_add_distrib, sum_zero_coordinate s hs]
    simp
    ring
  have hsum' : (∑ a : Fin s, if a.val = 0 then ((s : ℝ) - 1) ^ 2 else 1) =
      (s : ℝ) ^ 2 - (s : ℝ) := by simpa only [ite_pow, neg_one_sq] using hsum
  simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, witnessV]
  simp only [← pow_two, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  norm_num [Fin.sum_univ_succ, hsum']
  ring

/-- A proper four-coloring of `K₅−e`. -/
def forbiddenColoring : forbiddenGraph.Coloring (Fin 4) :=
  .mk (fun i => ⟨min i.val 3, by omega⟩) (by decide +kernel)

/-- Its chromatic number is exactly four, witnessed by a four-clique and a coloring. -/
theorem forbidden_chromaticNumber : forbiddenGraph.chromaticNumber = 4 := by
  apply le_antisymm (SimpleGraph.Colorable.chromaticNumber_le ⟨forbiddenColoring⟩)
  apply SimpleGraph.le_chromaticNumber_of_pairwise_adj
    (ι := Fin 4) (by simp) (fun i => i.castLE (by decide))
  intro i j hij
  exact ⟨(by intro h; exact hij (Fin.ext (congrArg (fun x : Fin 5 => x.val) h))), by
    have hi := i.isLt
    have hj := j.isLt
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [Fin.val_castLE]
    omega⟩

/-- Deleting the core edge `{0,1}` permits a proper three-coloring. -/
def forbiddenDeletedColoring :
    (forbiddenGraph.deleteEdges {s(0, 1)}).Coloring (Fin 3) :=
  .mk (fun i => ⟨if i.val ≤ 1 then 0 else if i.val = 2 then 1 else 2, by
    split_ifs <;> omega⟩) (by decide +kernel)

/-- The forbidden graph is color-critical in the edge-deletion sense. -/
theorem forbidden_color_critical :
    ∃ i j : Fin 5, forbiddenGraph.Adj i j ∧
      (forbiddenGraph.deleteEdges {s(i, j)}).chromaticNumber < forbiddenGraph.chromaticNumber := by
  refine ⟨0, 1, by decide, ?_⟩
  rw [forbidden_chromaticNumber]
  exact lt_of_le_of_lt
    (SimpleGraph.Colorable.chromaticNumber_le ⟨forbiddenDeletedColoring⟩) (by norm_num)

end KKP
