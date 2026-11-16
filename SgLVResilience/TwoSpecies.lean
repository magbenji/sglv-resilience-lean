/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# The two-species model (Section 3.1)

The model (3.1) is
`dX₁ = X₁(α₁ - β₁₁X₁ + β₁₂X₂)dt + X₁(τ₁₁dW₁ + τ₁₂dW₂)`,
`dX₂ = X₂(α₂ + β₂₁X₁ - β₂₂X₂)dt + X₂(τ₂₁dW₁ + τ₂₂dW₂)`, with `β₁₁, β₂₂ > 0`.
It is the general model (2.2) with `α = (α₁, α₂)`, `β = [[-β₁₁, β₁₂], [β₂₁, -β₂₂]]` and
`Γ = [[τ₁₁, τ₁₂], [τ₂₁, τ₂₂]]`.

We prove:
* `noiseCov_posDef_iff`: `Σ = ΓΓᵀ` is positive definite iff `τ₁₁τ₂₂ - τ₁₂τ₂₁ ≠ 0`, which is
  equivalent to the paper's three conditions (`noiseCov_posDef_iff'`);
* `jac_two`: the coefficients of (3.5). The correct diagonal entries are
  `γ₁₁ = α₁ - 2β₁₁m₁ + β₁₂m₂` and `γ₂₂ = α₂ + β₂₁m₁ - 2β₂₂m₂`; the printed `+2β₁₁m₁`, `+2β₂₂m₂`
  are sign typos (Table 1 was computed with the correct signs);
* `msMatrix_two`, `msForcing_two`: the explicit `S` and `T` of Section 3.1;
* `mutualistic_identity`: the identity behind the blow-up argument for mutualism;
* `tightness`: inequality (3.4), i.e. Assumption 3's drift condition, for the competitive and
  predator–prey cases.
-/
module

public import SgLVResilience.Basic
public import SgLVResilience.Moments
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

open Matrix Kronecker

namespace SgLVResilience

/-- The parameters of the two-species model (3.1). -/
structure TwoSpecies where
  α₁ : ℝ
  α₂ : ℝ
  β₁₁ : ℝ
  β₁₂ : ℝ
  β₂₁ : ℝ
  β₂₂ : ℝ
  τ₁₁ : ℝ
  τ₁₂ : ℝ
  τ₂₁ : ℝ
  τ₂₂ : ℝ
  β₁₁_pos : 0 < β₁₁
  β₂₂_pos : 0 < β₂₂

namespace TwoSpecies

variable (p : TwoSpecies)

/-- Growth rates `α = (α₁, α₂)`. -/
def alpha : Fin 2 → ℝ := ![p.α₁, p.α₂]

/-- Interaction matrix `β = [[-β₁₁, β₁₂], [β₂₁, -β₂₂]]` in the convention of (2.1). -/
def beta : Matrix (Fin 2) (Fin 2) ℝ := !![-p.β₁₁, p.β₁₂; p.β₂₁, -p.β₂₂]

/-- Noise intensities `Γ = [[τ₁₁, τ₁₂], [τ₂₁, τ₂₂]]`. -/
def Gam : Matrix (Fin 2) (Fin 2) ℝ := !![p.τ₁₁, p.τ₁₂; p.τ₂₁, p.τ₂₂]

/-- `σ₁₁ = τ₁₁² + τ₁₂²`. -/
def σ₁₁ : ℝ := p.τ₁₁ ^ 2 + p.τ₁₂ ^ 2
/-- `σ₂₂ = τ₂₁² + τ₂₂²`. -/
def σ₂₂ : ℝ := p.τ₂₁ ^ 2 + p.τ₂₂ ^ 2
/-- `σ₁₂ = σ₂₁ = τ₁₁τ₂₁ + τ₁₂τ₂₂`. -/
def σ₁₂ : ℝ := p.τ₁₁ * p.τ₂₁ + p.τ₁₂ * p.τ₂₂

/-- Per-capita growth rate of species 1, `f₁ = α₁ - β₁₁x₁ + β₁₂x₂`. -/
def f₁ (x₁ x₂ : ℝ) : ℝ := p.α₁ - p.β₁₁ * x₁ + p.β₁₂ * x₂
/-- Per-capita growth rate of species 2, `f₂ = α₂ + β₂₁x₁ - β₂₂x₂`. -/
def f₂ (x₁ x₂ : ℝ) : ℝ := p.α₂ + p.β₂₁ * x₁ - p.β₂₂ * x₂

theorem percap_eq (x : Fin 2 → ℝ) :
    percap p.alpha p.beta x = ![p.f₁ (x 0) (x 1), p.f₂ (x 0) (x 1)] := by
  ext i; fin_cases i <;> simp [percap, alpha, beta, f₁, f₂, mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

theorem noiseCov_eq : noiseCov p.Gam = !![p.σ₁₁, p.σ₁₂; p.σ₁₂, p.σ₂₂] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [noiseCov, Gam, σ₁₁, σ₁₂, σ₂₂, mul_apply, Fin.sum_univ_two] <;> ring

/-- **`Σ` is positive definite** iff `det Γ = τ₁₁τ₂₂ - τ₁₂τ₂₁ ≠ 0`. -/
theorem noiseCov_posDef_iff :
    (noiseCov p.Gam).PosDef ↔ p.τ₁₁ * p.τ₂₂ - p.τ₁₂ * p.τ₂₁ ≠ 0 := by
  have hsemi : (noiseCov p.Gam).PosSemidef := by
    simpa [noiseCov, conjTranspose_eq_transpose_of_trivial] using
      posSemidef_self_mul_conjTranspose p.Gam
  rw [hsemi.posDef_iff_mulVec_injective, mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, noiseCov, det_mul, det_transpose, ← sq, pow_ne_zero_iff two_ne_zero]
  simp [Gam, det_fin_two]

/-- **The paper's form of the condition**: `Σ` is positive definite iff `τ₁₁² + τ₁₂² > 0`,
`τ₂₁² + τ₂₂² > 0` and `τ₁₁τ₂₂ - τ₁₂τ₂₁ ≠ 0` (the first two follow from the third). -/
theorem noiseCov_posDef_iff' :
    (noiseCov p.Gam).PosDef ↔
      0 < p.σ₁₁ ∧ 0 < p.σ₂₂ ∧ p.τ₁₁ * p.τ₂₂ - p.τ₁₂ * p.τ₂₁ ≠ 0 := by
  rw [noiseCov_posDef_iff]
  refine ⟨fun h => ⟨?_, ?_, h⟩, fun h => h.2.2⟩
  · by_contra h1
    have h11 : p.τ₁₁ = 0 := by unfold σ₁₁ at h1; nlinarith [sq_nonneg p.τ₁₁, sq_nonneg p.τ₁₂]
    have h12 : p.τ₁₂ = 0 := by unfold σ₁₁ at h1; nlinarith [sq_nonneg p.τ₁₁, sq_nonneg p.τ₁₂]
    exact h (by rw [h11, h12]; ring)
  · by_contra h1
    have h21 : p.τ₂₁ = 0 := by unfold σ₂₂ at h1; nlinarith [sq_nonneg p.τ₂₁, sq_nonneg p.τ₂₂]
    have h22 : p.τ₂₂ = 0 := by unfold σ₂₂ at h1; nlinarith [sq_nonneg p.τ₂₁, sq_nonneg p.τ₂₂]
    exact h (by rw [h21, h22]; ring)

/-! ### The linearized system (3.5) -/

/-- **The coefficients of (3.5).** At `m = (m₁, m₂)`:
`Φ₁ = α₁m₁ - β₁₁m₁² + β₁₂m₁m₂`, `Φ₂ = α₂m₂ + β₂₁m₂m₁ - β₂₂m₂²`, and
`γ₁₁ = α₁ - 2β₁₁m₁ + β₁₂m₂`, `γ₁₂ = β₁₂m₁`, `γ₂₁ = β₂₁m₂`, `γ₂₂ = α₂ + β₂₁m₁ - 2β₂₂m₂`. -/
theorem jac_two (m₁ m₂ : ℝ) :
    drift p.alpha p.beta ![m₁, m₂] =
      ![p.α₁ * m₁ - p.β₁₁ * m₁ ^ 2 + p.β₁₂ * m₁ * m₂,
        p.α₂ * m₂ + p.β₂₁ * m₂ * m₁ - p.β₂₂ * m₂ ^ 2] ∧
    jac p.alpha p.beta ![m₁, m₂] =
      !![p.α₁ - 2 * p.β₁₁ * m₁ + p.β₁₂ * m₂, p.β₁₂ * m₁;
         p.β₂₁ * m₂, p.α₂ + p.β₂₁ * m₁ - 2 * p.β₂₂ * m₂] := by
  constructor
  · ext i; fin_cases i <;>
      simp [drift, percap, alpha, beta, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [jac, percap, alpha, beta, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The printed `γ₁₁ = α₁ + 2β₁₁m₁ + β₁₂m₂` is not `∂h₁/∂x₁` when `m₁ ≠ 0`. -/
theorem printed_gamma11_ne (m₁ m₂ : ℝ) (hm : m₁ ≠ 0) :
    jac p.alpha p.beta ![m₁, m₂] 0 0 ≠ p.α₁ + 2 * p.β₁₁ * m₁ + p.β₁₂ * m₂ := by
  rw [(p.jac_two m₁ m₂).2]
  simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one]
  intro h
  have := mul_ne_zero p.β₁₁_pos.ne' hm
  apply this
  linarith

/-- The noise matrices `B₁ = diag(τ₁₁, τ₂₁)` and `B₂ = diag(τ₁₂, τ₂₂)` of (3.6). -/
def Bmat : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![diagonal ![p.τ₁₁, p.τ₂₁], diagonal ![p.τ₁₂, p.τ₂₂]]

theorem Bmat_symm (i : Fin 2) : (p.Bmat i)ᵀ = p.Bmat i := by
  fin_cases i <;> simp [Bmat]

/-- **The matrix `S` of Section 3.1.** With `A = [[γ₁₁, γ₁₂], [γ₂₁, γ₂₂]]`, `S = I₂ ⊗ A + A ⊗ I₂ +
B₁ ⊗ B₁ + B₂ ⊗ B₂` is, in the paper's ordering `(Y₁², Y₂Y₁, Y₁Y₂, Y₂²)`,
`[[2γ₁₁+σ₁₁, γ₁₂, γ₁₂, 0], [γ₂₁, γ₁₁+γ₂₂+σ₁₂, 0, γ₁₂], [γ₂₁, 0, γ₁₁+γ₂₂+σ₁₂, γ₁₂],
[0, γ₂₁, γ₂₁, 2γ₂₂+σ₂₂]]`. -/
theorem msMatrix_two (g₁₁ g₁₂ g₂₁ g₂₂ : ℝ) :
    msMatrix !![g₁₁, g₁₂; g₂₁, g₂₂] p.Bmat =
      Matrix.of fun a b => (!![2 * g₁₁ + p.σ₁₁, g₁₂, g₁₂, 0;
        g₂₁, g₁₁ + g₂₂ + p.σ₁₂, 0, g₁₂;
        g₂₁, 0, g₁₁ + g₂₂ + p.σ₁₂, g₁₂;
        0, g₂₁, g₂₁, 2 * g₂₂ + p.σ₂₂] : Matrix (Fin 4) (Fin 4) ℝ)
        (finProdFinEquiv a) (finProdFinEquiv b) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [msMatrix, Bmat, σ₁₁, σ₁₂, σ₂₂, kroneckerMap_apply, Fin.sum_univ_two, one_apply,
      finProdFinEquiv] <;> ring

/-- **The forcing `T` of Section 3.1**, with `Θ = (Φ₁, Φ₂)`, `M = 𝔼 Y` and `m = (m₁, m₂)`:
`T = (2Φ₁M₁ + σ₁₁(2M₁m₁ + m₁²), Φ₂M₁ + Φ₁M₂ + σ₁₂(M₂m₁ + m₂M₁ + m₂m₁), (same),
2Φ₂M₂ + σ₂₂(2M₂m₂ + m₂²))`. (The paper prints `m₁θ₁`, `m₁θ₂ + m₂θ₁`, `m₂θ₂` for the first terms;
from `vec(ΘMᵀ + MΘᵀ)` they involve `M`, not `m`.) -/
theorem msForcing_two (Φ₁ Φ₂ m₁ m₂ M₁ M₂ : ℝ) :
    msForcing p.Bmat ![Φ₁, Φ₂] ![m₁, m₂] ![M₁, M₂] =
      fun a => (![2 * Φ₁ * M₁ + p.σ₁₁ * (2 * M₁ * m₁ + m₁ ^ 2),
        Φ₂ * M₁ + Φ₁ * M₂ + p.σ₁₂ * (M₂ * m₁ + m₂ * M₁ + m₂ * m₁),
        Φ₂ * M₁ + Φ₁ * M₂ + p.σ₁₂ * (M₁ * m₂ + m₁ * M₂ + m₁ * m₂),
        2 * Φ₂ * M₂ + p.σ₂₂ * (2 * M₂ * m₂ + m₂ ^ 2)] : Fin 4 → ℝ) (finProdFinEquiv a) := by
  funext ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [msForcing, Bmat, σ₁₁, σ₁₂, σ₂₂, kroneckerMap_apply, Fin.sum_univ_two, mulVec,
      dotProduct, diagonal_apply, finProdFinEquiv, Fintype.sum_prod_type, Pi.add_apply,
      flip] <;>
    ring

/-! ### The mutualistic case: the identity behind the blow-up argument -/

/-- **The identity in the mutualistic case.** `β₂₂ f₁ + β₁₂ f₂ = β₂₂α₁ + β₁₂α₂ +
(β₁₂β₂₁ - β₁₁β₂₂) x₁`, so by Itô's formula `β₂₂ ln X₁ + β₁₂ ln X₂` has drift
`β₂₂(α₁ - σ₁₁/2) + β₁₂(α₂ - σ₂₂/2) + (β₁₂β₂₁ - β₁₁β₂₂) X₁`. -/
theorem mutualistic_identity (x₁ x₂ : ℝ) :
    p.β₂₂ * p.f₁ x₁ x₂ + p.β₁₂ * p.f₂ x₁ x₂ =
      p.β₂₂ * p.α₁ + p.β₁₂ * p.α₂ + (p.β₁₂ * p.β₂₁ - p.β₁₁ * p.β₂₂) * x₁ := by
  simp only [f₁, f₂]; ring

/-- Under the paper's mutualistic assumptions (`β₁₂ > 0`, `α₁ - σ₁₁/2 > 0`, `α₂ - σ₂₂/2 > 0`,
`β₁₁β₂₂ - β₁₂β₂₁ ≤ 0`), that drift is bounded below by a positive constant on `x₁ ≥ 0`. -/
theorem mutualistic_drift_pos (hβ₁₂ : 0 < p.β₁₂) (h₁ : 0 < p.α₁ - p.σ₁₁ / 2)
    (h₂ : 0 < p.α₂ - p.σ₂₂ / 2) (hdet : p.β₁₁ * p.β₂₂ - p.β₁₂ * p.β₂₁ ≤ 0) {x₁ : ℝ}
    (hx : 0 ≤ x₁) :
    0 < p.β₂₂ * (p.α₁ - p.σ₁₁ / 2) + p.β₁₂ * (p.α₂ - p.σ₂₂ / 2) +
      (p.β₁₂ * p.β₂₁ - p.β₁₁ * p.β₂₂) * x₁ := by
  have := p.β₂₂_pos
  have : 0 ≤ (p.β₁₂ * p.β₂₁ - p.β₁₁ * p.β₂₂) * x₁ := mul_nonneg (by linarith) hx
  have := mul_pos p.β₂₂_pos h₁
  have := mul_pos hβ₁₂ h₂
  linarith

/-! ### Tightness: the drift condition (3.4) -/

/-- The left-hand side of (3.4), with weights `c = (c₁, c₂)` as in Assumption 3. -/
noncomputable def tightLHS (c₁ c₂ δ x₁ x₂ : ℝ) : ℝ :=
  (c₁ * x₁ * p.f₁ x₁ x₂ + c₂ * x₂ * p.f₂ x₁ x₂) / (1 + c₁ * x₁ + c₂ * x₂) -
    (p.σ₁₁ * c₁ ^ 2 * x₁ ^ 2 + 2 * p.σ₁₂ * c₁ * c₂ * x₁ * x₂ + p.σ₂₂ * c₂ ^ 2 * x₂ ^ 2) /
      (2 * (1 + c₁ * x₁ + c₂ * x₂) ^ 2) +
    δ * (3 + |p.f₁ x₁ x₂| + |p.f₂ x₁ x₂|)

/-- In the predator–prey case (`β₁₂β₂₁ < 0`) there are `c₁, c₂ > 0` with `c₁β₁₂ + c₂β₂₁ = 0`. -/
theorem exists_weights_predPrey (h : p.β₁₂ * p.β₂₁ < 0) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₁ * p.β₁₂ + c₂ * p.β₂₁ = 0 := by
  rcases lt_or_gt_of_ne (show p.β₁₂ ≠ 0 by rintro h0; simp [h0] at h) with h1 | h1
  · have h2 : 0 < p.β₂₁ := by nlinarith
    exact ⟨p.β₂₁, -p.β₁₂, h2, by linarith, by ring⟩
  · have h2 : p.β₂₁ < 0 := by nlinarith
    exact ⟨-p.β₂₁, p.β₁₂, by linarith, h1, by ring⟩

set_option maxHeartbeats 1600000 in
/-- **Inequality (3.4) (Assumption 3).** If `c₁, c₂ > 0` and `c₁β₁₂ + c₂β₂₁ ≤ 0` (the competitive
case with `c = (1, 1)`, or the predator–prey case with the weights of
`exists_weights_predPrey`), then there are `δ > 0` and `R` such that the left-hand side of (3.4)
is negative for all `x ∈ ℝ²₊` with `x₁ + x₂ ≥ R`. -/
theorem tightness {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hcross : c₁ * p.β₁₂ + c₂ * p.β₂₁ ≤ 0) :
    ∃ δ > 0, ∃ R, ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → 0 ≤ x₂ → R ≤ x₁ + x₂ → p.tightLHS c₁ c₂ δ x₁ x₂ < 0 := by
  have hb₁ := p.β₁₁_pos
  have hb₂ := p.β₂₂_pos
  -- constants
  set κ := min (c₁ * p.β₁₁) (c₂ * p.β₂₂) / 2 with hκ
  have hκpos : 0 < κ := by
    have := lt_min (mul_pos hc₁ hb₁) (mul_pos hc₂ hb₂); positivity
  set C := c₁ + c₂ with hC
  set a := c₁ * |p.α₁| + c₂ * |p.α₂| with ha
  set K := p.β₁₁ + |p.β₁₂| + |p.β₂₁| + p.β₂₂ with hK
  have hK0 : 0 ≤ K := by positivity
  set A₀ := 3 + |p.α₁| + |p.α₂| with hA₀
  set δ := κ / (8 * (1 + C) * (1 + K)) with hδ
  have hδpos : 0 < δ := by positivity
  have hCnn : 0 ≤ C := by positivity
  clear_value κ C a K A₀ δ
  refine ⟨δ, hδpos, max 1 (max (2 * a / κ) A₀), fun x₁ x₂ hx₁ hx₂ hR => ?_⟩
  set s := x₁ + x₂ with hs
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hR
  have hsa : 2 * a / κ ≤ s := ((le_max_left _ _).trans (le_max_right _ _)).trans hR
  have hsA : A₀ ≤ s := ((le_max_right _ _).trans (le_max_right _ _)).trans hR
  have hsa' : 2 * a ≤ κ * s := by have := (div_le_iff₀ hκpos).mp hsa; linarith
  -- the numerator is at most `-(κ/2) s²`
  set Q := c₁ * x₁ * p.f₁ x₁ x₂ + c₂ * x₂ * p.f₂ x₁ x₂ with hQ
  have hκ1 : κ ≤ c₁ * p.β₁₁ / 2 := by
    rw [hκ]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hκ2 : κ ≤ c₂ * p.β₂₂ / 2 := by
    rw [hκ]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hlin : c₁ * p.α₁ * x₁ + c₂ * p.α₂ * x₂ ≤ a * s := by
    have e1 : c₁ * p.α₁ * x₁ ≤ c₁ * |p.α₁| * x₁ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) hc₁.le) hx₁
    have e2 : c₂ * p.α₂ * x₂ ≤ c₂ * |p.α₂| * x₂ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) hc₂.le) hx₂
    have e3 : c₁ * |p.α₁| * x₁ + c₂ * |p.α₂| * x₂ ≤ a * s := by
      rw [ha, hs]; nlinarith [abs_nonneg p.α₁, abs_nonneg p.α₂, mul_nonneg hc₁.le (abs_nonneg p.α₁),
        mul_nonneg hc₂.le (abs_nonneg p.α₂)]
    linarith
  have hquad : κ * s ^ 2 ≤ c₁ * p.β₁₁ * x₁ ^ 2 + c₂ * p.β₂₂ * x₂ ^ 2 := by
    have e1 := mul_le_mul_of_nonneg_right hκ1 (sq_nonneg x₁)
    have e2 := mul_le_mul_of_nonneg_right hκ2 (sq_nonneg x₂)
    have e3 : s ^ 2 ≤ 2 * (x₁ ^ 2 + x₂ ^ 2) := by rw [hs]; nlinarith [sq_nonneg (x₁ - x₂)]
    have e4 := mul_le_mul_of_nonneg_left e3 hκpos.le
    linarith
  have hcross' : (c₁ * p.β₁₂ + c₂ * p.β₂₁) * (x₁ * x₂) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcross (mul_nonneg hx₁ hx₂)
  have hQle : Q ≤ -(κ / 2) * s ^ 2 := by
    have e : Q = c₁ * p.α₁ * x₁ + c₂ * p.α₂ * x₂ - (c₁ * p.β₁₁ * x₁ ^ 2 + c₂ * p.β₂₂ * x₂ ^ 2) +
        (c₁ * p.β₁₂ + c₂ * p.β₂₁) * (x₁ * x₂) := by rw [hQ]; simp only [f₁, f₂]; ring
    rw [e]
    have hs0 : 0 ≤ s := by linarith
    have h := mul_le_mul_of_nonneg_right hsa' hs0
    have has : a * s ≤ κ / 2 * s ^ 2 := by nlinarith [h]
    linarith
  -- the denominator
  set D := 1 + c₁ * x₁ + c₂ * x₂ with hD
  have hDpos : 0 < D := by positivity
  clear_value Q D s
  have hDle : D ≤ (1 + C) * s := by
    rw [hD, hC]; nlinarith [mul_nonneg hc₁.le hx₂, mul_nonneg hc₂.le hx₁]
  have hfirst : Q / D ≤ -(κ / (2 * (1 + C))) * s := by
    have hneg : Q ≤ 0 := by have : 0 ≤ κ / 2 * s ^ 2 := by positivity
                            linarith
    rw [div_le_iff₀ hDpos]
    have hk : 0 ≤ κ / (2 * (1 + C)) * s := by positivity
    have h := mul_le_mul_of_nonneg_left hDle hk
    have hC1 : 0 < 1 + C := by positivity
    have h2 : κ / (2 * (1 + C)) * s * ((1 + C) * s) = κ / 2 * s ^ 2 := by
      field_simp
    linarith only [h, h2, hQle]
  -- the noise term is nonpositive
  have hnoise : 0 ≤ (p.σ₁₁ * c₁ ^ 2 * x₁ ^ 2 + 2 * p.σ₁₂ * c₁ * c₂ * x₁ * x₂ +
      p.σ₂₂ * c₂ ^ 2 * x₂ ^ 2) / (2 * D ^ 2) := by
    apply div_nonneg _ (by positivity)
    have : p.σ₁₁ * c₁ ^ 2 * x₁ ^ 2 + 2 * p.σ₁₂ * c₁ * c₂ * x₁ * x₂ + p.σ₂₂ * c₂ ^ 2 * x₂ ^ 2 =
        (p.τ₁₁ * c₁ * x₁ + p.τ₂₁ * c₂ * x₂) ^ 2 + (p.τ₁₂ * c₁ * x₁ + p.τ₂₂ * c₂ * x₂) ^ 2 := by
      simp only [σ₁₁, σ₁₂, σ₂₂]; ring
    rw [this]; positivity
  -- the `δ` term
  have hf₁ : |p.f₁ x₁ x₂| ≤ |p.α₁| + K * s := by
    unfold f₁
    calc |p.α₁ - p.β₁₁ * x₁ + p.β₁₂ * x₂| ≤ |p.α₁| + p.β₁₁ * x₁ + |p.β₁₂| * x₂ := by
          have e1 := abs_add_le (p.α₁ - p.β₁₁ * x₁) (p.β₁₂ * x₂)
          have e2 := abs_sub (p.α₁) (p.β₁₁ * x₁)
          have e3 : |p.β₁₂ * x₂| = |p.β₁₂| * x₂ := by rw [abs_mul, abs_of_nonneg hx₂]
          have e4 : |p.β₁₁ * x₁| = p.β₁₁ * x₁ := abs_of_nonneg (mul_nonneg hb₁.le hx₁)
          linarith
      _ ≤ |p.α₁| + K * s := by
          rw [hK, hs]
          nlinarith [abs_nonneg p.β₁₂, abs_nonneg p.β₂₁, mul_nonneg (abs_nonneg p.β₁₂) hx₁,
            mul_nonneg (abs_nonneg p.β₂₁) hx₁, mul_nonneg (abs_nonneg p.β₂₁) hx₂,
            mul_nonneg hb₂.le hx₁, mul_nonneg hb₂.le hx₂, mul_nonneg hb₁.le hx₂]
  have hf₂ : |p.f₂ x₁ x₂| ≤ |p.α₂| + K * s := by
    unfold f₂
    calc |p.α₂ + p.β₂₁ * x₁ - p.β₂₂ * x₂| ≤ |p.α₂| + |p.β₂₁| * x₁ + p.β₂₂ * x₂ := by
          have e1 := abs_sub (p.α₂ + p.β₂₁ * x₁) (p.β₂₂ * x₂)
          have e2 := abs_add_le (p.α₂) (p.β₂₁ * x₁)
          have e3 : |p.β₂₁ * x₁| = |p.β₂₁| * x₁ := by rw [abs_mul, abs_of_nonneg hx₁]
          have e4 : |p.β₂₂ * x₂| = p.β₂₂ * x₂ := abs_of_nonneg (mul_nonneg hb₂.le hx₂)
          linarith
      _ ≤ |p.α₂| + K * s := by
          rw [hK, hs]
          nlinarith [abs_nonneg p.β₁₂, abs_nonneg p.β₂₁, mul_nonneg (abs_nonneg p.β₁₂) hx₁,
            mul_nonneg (abs_nonneg p.β₁₂) hx₂, mul_nonneg (abs_nonneg p.β₂₁) hx₂,
            mul_nonneg hb₁.le hx₁, mul_nonneg hb₁.le hx₂, mul_nonneg hb₂.le hx₁]
  have hδterm : δ * (3 + |p.f₁ x₁ x₂| + |p.f₂ x₁ x₂|) < κ / (2 * (1 + C)) * s := by
    have h1 : 3 + |p.f₁ x₁ x₂| + |p.f₂ x₁ x₂| ≤ s + 2 * K * s := by
      have : A₀ ≤ s := hsA
      rw [hA₀] at this
      linarith
    have h2 : δ * (3 + |p.f₁ x₁ x₂| + |p.f₂ x₁ x₂|) ≤ δ * ((1 + 2 * K) * s) := by
      have := mul_le_mul_of_nonneg_left h1 hδpos.le
      linarith
    have h3 : δ * ((1 + 2 * K) * s) ≤ κ / (4 * (1 + C)) * s := by
      rw [hδ]
      have hC0 : 0 ≤ C := by positivity
      have hs0 : 0 ≤ s := by linarith
      rw [show κ / (8 * (1 + C) * (1 + K)) * ((1 + 2 * K) * s) =
          κ / (4 * (1 + C)) * s * ((1 + 2 * K) / (2 * (1 + K))) by field_simp; ring]
      have hr : (1 + 2 * K) / (2 * (1 + K)) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have : 0 ≤ κ / (4 * (1 + C)) * s := by positivity
      nlinarith
    have h4 : κ / (4 * (1 + C)) * s < κ / (2 * (1 + C)) * s := by
      have : 0 < κ * s := by positivity
      have hC0 : 0 < 1 + C := by positivity
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  -- combine
  have : p.tightLHS c₁ c₂ δ x₁ x₂ = Q / D -
      (p.σ₁₁ * c₁ ^ 2 * x₁ ^ 2 + 2 * p.σ₁₂ * c₁ * c₂ * x₁ * x₂ + p.σ₂₂ * c₂ ^ 2 * x₂ ^ 2) /
        (2 * D ^ 2) + δ * (3 + |p.f₁ x₁ x₂| + |p.f₂ x₁ x₂|) := by rw [hQ, hD, tightLHS]
  rw [this]
  linarith only [hfirst, hnoise, hδterm]

end TwoSpecies

end SgLVResilience
