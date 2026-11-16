/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# Second moments of the linearized system (Section 2.4): (2.19) ⇔ (2.21) and `W'(t)`

For the linearized system (2.16), `dY = (AY + Θ) dt + ∑ᵢ (BᵢY + Bᵢm) dWᵢ`, the paper takes from
the literature that `P(t) = 𝔼[Y Yᵀ]` and `M(t) = 𝔼[Y]` solve the matrix ODE (2.19) and the
vector ODE (2.20). That step needs Itô calculus, which Mathlib does not have, so (2.19) is our
starting point. From it we prove, for symmetric `Bᵢ` (the paper's `Bᵢ` are diagonal):
* the vectorized form (2.21), `Z' = S Z + T` with `Z = vec P`,
  `S = I ⊗ A + A ⊗ I + ∑ᵢ Bᵢ ⊗ Bᵢ` and the paper's `T` (`vec_momentRHS`, `hasDerivAt_vec`);
* the formula for `W'(t)`, where `W = tr P = 𝔼[YᵀY]` (`trace_momentRHS`, `hasDerivAt_W`).

`vec` is Mathlib's column-stacking `Matrix.vec` (`vec P (i, j) = P j i`), the paper's ordering.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Matrix Kronecker

namespace SgLVResilience

variable {N : ℕ}

/-- The right-hand side of (2.19):
`AP + PAᵀ + ∑ᵢ BᵢPBᵢ + ΘMᵀ + MΘᵀ + ∑ᵢ Bᵢ(Mmᵀ + mMᵀ + mmᵀ)Bᵢ`. -/
def momentRHS (A : Matrix (Fin N) (Fin N) ℝ) (B : Fin N → Matrix (Fin N) (Fin N) ℝ)
    (Θ m M : Fin N → ℝ) (P : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  A * P + P * Aᵀ + ∑ i, B i * P * B i + vecMulVec Θ M + vecMulVec M Θ +
    ∑ i, B i * (vecMulVec M m + vecMulVec m M + vecMulVec m m) * B i

/-- The mean-square stability matrix `S = I ⊗ A + A ⊗ I + ∑ᵢ Bᵢ ⊗ Bᵢ` of (2.21). -/
def msMatrix (A : Matrix (Fin N) (Fin N) ℝ) (B : Fin N → Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℝ :=
  1 ⊗ₖ A + A ⊗ₖ 1 + ∑ i, B i ⊗ₖ B i

/-- The forcing `T = vec(ΘMᵀ + MΘᵀ) + ∑ᵢ (Bᵢ ⊗ Bᵢ) vec(Mmᵀ + mMᵀ + mmᵀ)` of (2.21). -/
def msForcing (B : Fin N → Matrix (Fin N) (Fin N) ℝ) (Θ m M : Fin N → ℝ) : Fin N × Fin N → ℝ :=
  vec (vecMulVec Θ M + vecMulVec M Θ) +
    ∑ i, (B i ⊗ₖ B i) *ᵥ vec (vecMulVec M m + vecMulVec m M + vecMulVec m m)

theorem sum_mulVec' {ι : Type*} (s : Finset ι) (C : ι → Matrix (Fin N × Fin N) (Fin N × Fin N) ℝ)
    (v : Fin N × Fin N → ℝ) : (∑ i ∈ s, C i) *ᵥ v = ∑ i ∈ s, C i *ᵥ v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]

variable {A : Matrix (Fin N) (Fin N) ℝ} {B : Fin N → Matrix (Fin N) (Fin N) ℝ} {Θ m : Fin N → ℝ}

/-- **(2.19) ⇔ (2.21), the algebra.** For symmetric `Bᵢ`,
`vec(AP + PAᵀ + ∑ᵢ BᵢPBᵢ + ...) = S vec P + T`. -/
theorem vec_momentRHS (hB : ∀ i, (B i)ᵀ = B i) (M : Fin N → ℝ) (P : Matrix (Fin N) (Fin N) ℝ) :
    vec (momentRHS A B Θ m M P) = msMatrix A B *ᵥ vec P + msForcing B Θ m M := by
  have h1 : (1 ⊗ₖ A) *ᵥ vec P = vec (A * P) := by
    rw [kronecker_mulVec_vec, transpose_one, Matrix.mul_one]
  have h2 : (A ⊗ₖ 1) *ᵥ vec P = vec (P * Aᵀ) := by
    rw [kronecker_mulVec_vec, Matrix.one_mul]
  have h3 : ∀ i, (B i ⊗ₖ B i) *ᵥ vec P = vec (B i * P * B i) := fun i => by
    rw [kronecker_mulVec_vec, hB i]
  have h4 : ∀ i, (B i ⊗ₖ B i) *ᵥ vec (vecMulVec M m + vecMulVec m M + vecMulVec m m) =
      vec (B i * (vecMulVec M m + vecMulVec m M + vecMulVec m m) * B i) := fun i => by
    rw [kronecker_mulVec_vec, hB i]
  simp only [msForcing, h4]
  simp only [momentRHS, msMatrix, add_mulVec, sum_mulVec', h1, h2, h3, vec_add, vec_sum]
  abel

/-- **(2.21).** If `P` solves (2.19) at time `t`, then `Z = vec P` satisfies `Z' = S Z + T`. -/
theorem hasDerivAt_vec (hB : ∀ i, (B i)ᵀ = B i) {P : ℝ → Matrix (Fin N) (Fin N) ℝ}
    {M : ℝ → Fin N → ℝ} {t : ℝ} (hP : HasDerivAt P (momentRHS A B Θ m (M t) (P t)) t) :
    HasDerivAt (fun s => vec (P s)) (msMatrix A B *ᵥ vec (P t) + msForcing B Θ m (M t)) t := by
  rw [← vec_momentRHS hB]
  refine hasDerivAt_pi.mpr fun ⟨i, j⟩ => ?_
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hP j) i

/-- **The formula for `W'(t)`, the algebra.** For symmetric `Bᵢ`, the trace of (2.19) is
`[vec(Aᵀ + A) + ∑ᵢ vec(Bᵢ²)]ᵀ vec P + ΘᵀM + MᵀΘ + ∑ᵢ (mᵀBᵢ²M + MᵀBᵢ²m + mᵀBᵢ²m)`. -/
theorem trace_momentRHS (hB : ∀ i, (B i)ᵀ = B i) (M : Fin N → ℝ)
    (P : Matrix (Fin N) (Fin N) ℝ) :
    trace (momentRHS A B Θ m M P) =
      (vec (Aᵀ + A) + ∑ i, vec (B i * B i)) ⬝ᵥ vec P + Θ ⬝ᵥ M + M ⬝ᵥ Θ +
        ∑ i, (m ⬝ᵥ (B i * B i) *ᵥ M + M ⬝ᵥ (B i * B i) *ᵥ m + m ⬝ᵥ (B i * B i) *ᵥ m) := by
  -- each `vec X ⬝ᵥ vec P` is `tr(Xᵀ P)`
  have hv : ∀ X : Matrix (Fin N) (Fin N) ℝ, vec X ⬝ᵥ vec P = trace (Xᵀ * P) := fun X => by
    simp only [vec_dotProduct_vec, trace, diag, mul_apply, transpose_apply]
  have hBB : ∀ i, (B i * B i)ᵀ = B i * B i := fun i => by rw [transpose_mul, hB i]
  have hcyc : ∀ (i : Fin N) (X : Matrix (Fin N) (Fin N) ℝ),
      trace (B i * X * B i) = trace ((B i * B i) * X) := fun i X => by
    rw [trace_mul_comm, ← Matrix.mul_assoc]
  have hq : ∀ (C : Matrix (Fin N) (Fin N) ℝ) (u v : Fin N → ℝ),
      trace (C * vecMulVec u v) = v ⬝ᵥ C *ᵥ u := fun C u v => by
    simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hAP : trace (P * Aᵀ) = trace (Aᵀ * P) := trace_mul_comm _ _
  simp only [momentRHS, trace_add, trace_sum, hcyc, Matrix.mul_add, trace_add, hq, add_dotProduct,
    sum_dotProduct, hv, hBB, transpose_add, transpose_transpose, Matrix.add_mul, hAP,
    trace_vecMulVec]

/-- **`W'(t)`.** If `P` solves (2.19) at time `t`, then `W = tr P` has the derivative given by
`trace_momentRHS`. -/
theorem hasDerivAt_W {P : ℝ → Matrix (Fin N) (Fin N) ℝ} {M : ℝ → Fin N → ℝ} {t : ℝ}
    (hP : HasDerivAt P (momentRHS A B Θ m (M t) (P t)) t) :
    HasDerivAt (fun s => trace (P s)) (trace (momentRHS A B Θ m (M t) (P t))) t := by
  simp only [trace, diag]
  exact HasDerivAt.fun_sum fun i _ => hasDerivAt_pi.mp (hasDerivAt_pi.mp hP i) i

end SgLVResilience
