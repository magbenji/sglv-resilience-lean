/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# The generalized Lotka–Volterra drift and its linearization (Sections 2.1 and 2.3)

States are vectors `x : Fin N → ℝ`. For growth rates `α : Fin N → ℝ` and interaction matrix
`β : Matrix (Fin N) (Fin N) ℝ`:
* `percap α β x i = α i + ∑ⱼ β i j * x j` is the per-capita growth rate `fᵢ(x)`;
* `drift α β x i = x i * fᵢ(x)` is the drift `hᵢ(x)` of (2.1)–(2.3);
* `jac α β m` is the Jacobian matrix `∂hᵢ/∂xⱼ (m)`.

The statistical linearization of Section 2.3 replaces `hᵢ(X)` by `Φᵢ + ∑ⱼ γᵢⱼ (Xⱼ - mⱼ)`, choosing
`Φ` and `γ` so that the error is small as `X → m`. We prove that the error is `o(‖X - m‖)` for
`Φ = h(m)` (2.12) and `γ = jac α β m`, and that these are the only coefficients with this
property (`linearization_unique`). The diagonal entries are
`γᵢᵢ = αᵢ + ∑ₖ βᵢₖ mₖ + βᵢᵢ mᵢ` (`jac_diag`): the printed (2.13) omits the term `βᵢᵢ mᵢ`
(`jac_diag_ne_printed`).
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open Filter Topology Asymptotics

namespace SgLVResilience

variable {N : ℕ}

/-- The per-capita growth rate `fᵢ(x) = αᵢ + ∑ⱼ βᵢⱼ xⱼ`. -/
def percap (α : Fin N → ℝ) (β : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  α i + (β.mulVec x) i

/-- The gLV drift `hᵢ(x) = xᵢ (αᵢ + ∑ⱼ βᵢⱼ xⱼ)` of (2.1)–(2.3). -/
def drift (α : Fin N → ℝ) (β : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => x i * percap α β x i

/-- The Jacobian matrix `∂hᵢ/∂xⱼ (m) = δᵢⱼ fᵢ(m) + βᵢⱼ mᵢ`. -/
def jac (α : Fin N → ℝ) (β : Matrix (Fin N) (Fin N) ℝ) (m : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (if i = j then percap α β m i else 0) + β i j * m i

/-- The Jacobian as a continuous linear map. -/
noncomputable def jacCLM (α : Fin N → ℝ) (β : Matrix (Fin N) (Fin N) ℝ) (m : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin (jac α β m))

variable (α : Fin N → ℝ) (β : Matrix (Fin N) (Fin N) ℝ)

theorem jac_mulVec (m v : Fin N → ℝ) (i : Fin N) :
    (jac α β m).mulVec v i = percap α β m i * v i + m i * (β.mulVec v) i := by
  simp only [jac, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The Jacobian of the gLV drift.** `h` is differentiable with derivative `jac α β m`. -/
theorem hasFDerivAt_drift (m : Fin N → ℝ) :
    HasFDerivAt (drift α β) (jacCLM α β m) m := by
  refine hasFDerivAt_pi'' fun i => ?_
  have h1 : HasFDerivAt (fun x : Fin N → ℝ => x i) (ContinuousLinearMap.proj i) m :=
    hasFDerivAt_apply (𝕜 := ℝ) i m
  have hB := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin β)).hasFDerivAt (x := m)
  have h2 : HasFDerivAt (fun x => percap α β x i)
      ((ContinuousLinearMap.proj i).comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin β)))
      m := by
    have := ((hasFDerivAt_apply (𝕜 := ℝ) i
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin β) m)).comp m hB).const_add (α i)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    simp [percap]
  have hcl : (ContinuousLinearMap.proj i).comp (jacCLM α β m) =
      m i • (ContinuousLinearMap.proj i).comp
        (LinearMap.toContinuousLinearMap (Matrix.mulVecLin β)) +
      percap α β m i • ContinuousLinearMap.proj i := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [jacCLM, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.proj_apply, LinearMap.coe_toContinuousLinearMap',
      Matrix.mulVecLin_apply, jac_mulVec, add_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hcl]
  exact (h1.mul h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => rfl)

theorem jac_diag (m : Fin N → ℝ) (i : Fin N) :
    jac α β m i i = α i + ∑ k, β i k * m k + β i i * m i := by
  simp [jac, percap, Matrix.mulVec, dotProduct]

theorem jac_offdiag (m : Fin N → ℝ) {i j : Fin N} (hij : i ≠ j) :
    jac α β m i j = β i j * m i := by
  simp [jac, hij]

/-- The diagonal of (2.13) as printed, `αᵢ + ∑ₖ βᵢₖ mₖ`, is not `∂hᵢ/∂xᵢ (m)` when
`βᵢᵢ ≠ 0` and `mᵢ ≠ 0` (for example `βᵢᵢ = -αᵢ cᵢ < 0` and `mᵢ > 0`). -/
theorem jac_diag_ne_printed (m : Fin N → ℝ) (i : Fin N) (hβ : β i i ≠ 0) (hm : m i ≠ 0) :
    jac α β m i i ≠ α i + ∑ k, β i k * m k := by
  rw [jac_diag]
  intro h
  exact mul_ne_zero hβ hm (by linarith)

/-- **(2.12)–(2.13): the linearization.** With `Φ = h(m)` and `γ = jac α β m`,
`h(X) = Φ + γ (X - m) + o(‖X - m‖)` as `X → m`. -/
theorem linearization_isLittleO (m : Fin N → ℝ) :
    (fun X => drift α β X - (drift α β m + (jac α β m).mulVec (X - m))) =o[𝓝 m]
      fun X => X - m := by
  have := hasFDerivAt_iff_isLittleO.mp (hasFDerivAt_drift α β m)
  refine this.congr_left fun X => ?_
  simp only [jacCLM, LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply]
  abel

/-- **Uniqueness of the linearization.** If `h(X) = Φ' + γ' (X - m) + o(‖X - m‖)` as `X → m`, then
`Φ' = h(m)` and `γ' = jac α β m`: the coefficients (2.12)–(2.13) are the only ones that make the
error (2.11) vanish to first order. -/
theorem linearization_unique (m Φ' : Fin N → ℝ) (γ' : Matrix (Fin N) (Fin N) ℝ)
    (h : (fun X => drift α β X - (Φ' + γ'.mulVec (X - m))) =o[𝓝 m] fun X => X - m) :
    Φ' = drift α β m ∧ γ' = jac α β m := by
  -- evaluating the estimate at `X = m` gives `Φ' = h(m)`
  have hΦ : Φ' = drift α β m := by
    have hb := (h.bound one_pos).self_of_nhds
    simp only [sub_self, Matrix.mulVec_zero, add_zero, norm_zero, mul_zero] at hb
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp hb)).symm
  refine ⟨hΦ, ?_⟩
  subst hΦ
  -- so `γ'` is a derivative of `h` at `m`, and derivatives are unique
  have hd : HasFDerivAt (drift α β) (LinearMap.toContinuousLinearMap (Matrix.mulVecLin γ')) m := by
    refine hasFDerivAt_iff_isLittleO.mpr (h.congr_left fun X => ?_)
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply]
    abel
  have hu := hd.unique (hasFDerivAt_drift α β m)
  have hl : ∀ v, γ'.mulVec v = (jac α β m).mulVec v := fun v => by
    simpa [jacCLM] using congrArg (fun L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) => L v) hu
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (hl (Pi.single j 1)) i

/-- `h(m)` is the vector `Φ` of (2.12): `Φᵢ = mᵢ (αᵢ + ∑ⱼ βᵢⱼ mⱼ)`. -/
theorem drift_apply (m : Fin N → ℝ) (i : Fin N) :
    drift α β m i = m i * (α i + ∑ j, β i j * m j) := by
  simp [drift, percap, Matrix.mulVec, dotProduct]

/-- The noise covariance `Σ = Γ Γᵀ`, `σᵢⱼ = ∑ₖ τᵢₖ τⱼₖ`. -/
def noiseCov (Γ : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ := Γ * Γ.transpose

theorem noiseCov_apply (Γ : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    noiseCov Γ i j = ∑ k, Γ i k * Γ j k := by
  simp [noiseCov, Matrix.mul_apply]

end SgLVResilience
