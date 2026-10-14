module
public import BN.Spectral.Variational
public import BN.Spectral.Interlace
@[expose] public section

/-!
# Positive rank-two compression and the actual ordered spectrum

An orthonormal two-column matrix identifies a two-dimensional subspace.
For a positive semidefinite compression, its squared Frobenius mass is bounded
by the squares of the two largest positive eigenvalues of the ambient matrix.
The proof uses the checked rank-two variational theorem of the pinned BN source.
-/

namespace KKP
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive two-dimensional compression is controlled by the actual positive spectrum. -/
theorem positive_compression_le (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (Q : Matrix n (Fin 2) ℝ) (hQ : Qᵀ * Q = 1)
    (hC : (Qᵀ * A * Q).PosSemidef) :
    BN.inner (Qᵀ * A * Q) (Qᵀ * A * Q) ≤ BN.F hA := by
  let C := Qᵀ * A * Q
  let X := Q * C * Qᵀ
  have hX : X.PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hC.mul_mul_conjTranspose_same Q
  have hr : X.rank ≤ 2 := by
    exact (rank_mul_le_left _ _).trans
      ((rank_mul_le_left _ _).trans (by simpa using Q.rank_le_card_width))
  have hCt : Cᵀ = C := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hC.isHermitian.eq
  have hAt : Aᵀ = A := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hAX : BN.inner A X = BN.inner C C := by
    simp only [BN.inner, X, hAt, hCt]
    calc
      (A * (Q * C * Qᵀ)).trace = (Qᵀ * A * (Q * C)).trace := by
        rw [Matrix.mul_assoc Q C Qᵀ, ← Matrix.mul_assoc A Q (C * Qᵀ),
          trace_mul_cycle' (A * Q) C Qᵀ]
        simp only [Matrix.mul_assoc]
      _ = (C * C).trace := by simp only [C, Matrix.mul_assoc]
  have hXt : Xᵀ = X := by
    simp only [X, transpose_mul, transpose_transpose, hCt, Matrix.mul_assoc]
  have hXX : BN.inner X X = BN.inner C C := by
    simp only [BN.inner, hXt, hCt, X]
    calc
      ((Q * C * Qᵀ) * (Q * C * Qᵀ)).trace =
          (Q * C * (Qᵀ * Q) * C * Qᵀ).trace := by simp only [Matrix.mul_assoc]
      _ = (Q * (C * C) * Qᵀ).trace := by rw [hQ]; simp only [mul_one, Matrix.mul_assoc]
      _ = (Qᵀ * Q * (C * C)).trace := trace_mul_cycle _ _ _
      _ = (C * C).trace := by rw [hQ, one_mul]
  have hn : 0 ≤ BN.inner C C := by
    rw [BN.inner_self]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hv := BN.variational_lemma hA hX hr
  rw [hAX, hXX] at hv
  have hs : (BN.inner C C) ^ 2 ≤ BN.F hA * BN.inner C C := by
    have hp := mul_nonneg (BN.F_nonneg hA) hn
    rw [← Real.sqrt_mul (BN.F_nonneg hA)] at hv
    exact (Real.le_sqrt hn hp).mp hv
  by_cases hz : BN.inner C C = 0
  · rw [hz]; exact BN.F_nonneg hA
  · have hp : 0 < BN.inner C C := lt_of_le_of_ne hn (Ne.symm hz)
    exact (mul_le_mul_iff_of_pos_right hp).mp (by simpa [pow_two] using hs)

end KKP
