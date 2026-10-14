module
public import Mathlib
public section

namespace CounterexampleCertificate

/-- The denominator of the two-vector compression certificate. -/
theorem denominator_pos (s : ℝ) (hs : 3 ≤ s) : 0 < 37 * s - 1 := by
  linarith

/-- Positive numerator of the compression determinant. -/
theorem determinant_numerator_pos (s : ℝ) (hs : 3 ≤ s) :
    0 < 228 * s ^ 2 - 12 * s - 3 := by
  have h₁ : 0 ≤ 228 * (s - 3) ^ 2 := by positivity
  have h₂ : 0 ≤ 1356 * (s - 3) := by
    have : 0 ≤ s - 3 := by linarith
    positivity
  nlinarith

/-- Positive scalar determinant of the displayed two-vector compression.
This declaration does not assert a graph eigenvalue or interlacing theorem. -/
theorem compression_determinant_pos (s : ℝ) (hs : 3 ≤ s) :
    0 < 2 * s * ((114 * s - 6) / (37 * s - 1)) -
      3 / (37 * s - 1) := by
  have hd := denominator_pos s hs
  have hn := determinant_numerator_pos s hs
  have he :
      2 * s * ((114 * s - 6) / (37 * s - 1)) -
        3 / (37 * s - 1) =
      (228 * s ^ 2 - 12 * s - 3) / (37 * s - 1) := by
    field_simp [ne_of_gt hd]
    <;> ring
  rw [he]
  exact div_pos hn hd

/-- The exact excess numerator is positive throughout the infinite family. -/
theorem excess_numerator_pos (s : ℝ) (hs : 3 ≤ s) :
    0 < 656 * s ^ 2 - 1366 * s + 62 := by
  have h₁ : 0 ≤ 656 * (s - 3) ^ 2 := by positivity
  have h₂ : 0 ≤ 2570 * (s - 3) := by
    have : 0 ≤ s - 3 := by linarith
    positivity
  nlinarith

/-- Exact rational identity for tr(C_s^2) minus 4m/3. -/
theorem compression_gap_identity (s : ℝ) (hd : 37 * s - 1 ≠ 0) :
    (4 * s ^ 2 + ((114 * s - 6) / (37 * s - 1)) ^ 2 +
      6 / (37 * s - 1)) - (4 / 3 : ℝ) * (3 * s ^ 2 + 7) =
    (656 * s ^ 2 - 1366 * s + 62) / (3 * (37 * s - 1) ^ 2) := by
  let d := 37 * s - 1
  have hd' : d ≠ 0 := hd
  change (4 * s ^ 2 + ((114 * s - 6) / d) ^ 2 + 6 / d) -
    (4 / 3 : ℝ) * (3 * s ^ 2 + 7) =
    (656 * s ^ 2 - 1366 * s + 62) / (3 * d ^ 2)
  field_simp
  dsimp [d] at *
  nlinarith [sq_nonneg (37 * s - 1)]

/-- The compression certificate strictly exceeds the claimed edge bound. -/
theorem compression_excess (s : ℝ) (hs : 3 ≤ s) :
    (4 / 3 : ℝ) * (3 * s ^ 2 + 7) <
      4 * s ^ 2 + ((114 * s - 6) / (37 * s - 1)) ^ 2 +
        6 / (37 * s - 1) := by
  have hd := denominator_pos s hs
  have hn := excess_numerator_pos s hs
  have hp : 0 < 3 * (37 * s - 1) ^ 2 := by positivity
  have hg := div_pos hn hp
  rw [← compression_gap_identity s (ne_of_gt hd)] at hg
  linarith

/-- The certificates occur at arbitrarily large natural edge counts.
This theorem concerns the explicit scalar certificate; the graph interpretation
and eigenvalue interlacing are not formalized in this module. -/
theorem unbounded_certificates (B : ℕ) :
    ∃ s : ℕ, B ≤ 3 * s ^ 2 + 7 ∧ 3 ≤ s ∧
      (4 / 3 : ℝ) * (3 * (s : ℝ) ^ 2 + 7) <
        4 * (s : ℝ) ^ 2 +
          ((114 * (s : ℝ) - 6) / (37 * (s : ℝ) - 1)) ^ 2 +
            6 / (37 * (s : ℝ) - 1) := by
  refine ⟨B + 3, ?_, ?_, ?_⟩
  · nlinarith [Nat.zero_le B, Nat.zero_le (B ^ 2)]
  · omega
  · apply compression_excess
    exact_mod_cast (show 3 ≤ B + 3 by omega)

end CounterexampleCertificate

#print axioms CounterexampleCertificate.compression_determinant_pos
#print axioms CounterexampleCertificate.compression_excess
#print axioms CounterexampleCertificate.unbounded_certificates
