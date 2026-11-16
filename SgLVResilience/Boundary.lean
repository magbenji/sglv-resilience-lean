/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# Invariant measures on the boundary and the classification C1–C4 (Section 3.1)

**The one-species stationary law (Cases 2 and 3).** On an axis the model reduces to the
stochastic logistic equation `dX = X(α - βX)dt + X(τ₁dW₁ + τ₂dW₂)`, with `σ = τ₁² + τ₂²`. Its
stationary density solves the zero-flux Fokker–Planck equation `(σ/2 · x² p)' = x(α - βx) p`.
We prove that `p(x) = x^{k-1} e^{-rx}` with shape `k = 2α/σ - 1` and rate `r = 2β/σ` solves it
(`zeroFlux`), and that it can be normalized to a probability density iff `α - σ/2 > 0`
(`integrableOn_statDensity_iff`). Normalized, it is the Gamma law with shape `k` and scale
`1/r = σ/(2β)`; its mean is `(α - σ/2)/β` (`integral_id_gammaMeasure`). (The paper prints the
scale of `π₁` as `(τ₂₁² + τ₂₂²)/(2β₁₁)`; for species 1 it is `(τ₁₁² + τ₁₂²)/(2β₁₁)`.)

**Lyapunov exponents.** For a probability measure `μ` on `ℝ²₊`,
`λᵢ(μ) = ∫ fᵢ dμ - σᵢᵢ/2`. With `μ₀ = δ₀ × δ₀`, `μ₁ = π₁ × δ₀`, `μ₂ = δ₀ × π₂` we prove the
paper's six formulas (`lyap₁_μ₀`, ..., `lyap₂_μ₂`), that `πᵢ` exists iff `λᵢ(μ₀) > 0`, and that
`λᵢ` is affine on convex combinations (`lyap_mix`). From these, Assumption 4 holds in cases
C2(i), C3(i) and C4(i) (`assumption4_C2i`, `assumption4_C3i`, `assumption4_C4i`). The
conclusions the paper then draws (persistence, extinction) come from Theorems 2.3–2.5, which are
cited results about SDEs and are not formalized.
-/
module

public import SgLVResilience.TwoSpecies
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace SgLVResilience

/-! ### The stochastic logistic equation: stationary density -/

/-- Shape `k = 2α/σ - 1` of the stationary Gamma law. -/
noncomputable def shape (α σ : ℝ) : ℝ := 2 * α / σ - 1

/-- Rate `r = 2β/σ` of the stationary Gamma law (scale `σ/(2β)`). -/
noncomputable def rate (β σ : ℝ) : ℝ := 2 * β / σ

/-- The unnormalized stationary density `p(x) = x^{k-1} e^{-rx}`. -/
noncomputable def statDensity (α β σ x : ℝ) : ℝ :=
  x ^ (shape α σ - 1) * exp (-(rate β σ * x))

/-- **Zero-flux stationary Fokker–Planck equation.** For `x > 0`,
`d/dx [σ/2 · x² p(x)] = x(α - βx) p(x)`. -/
theorem zeroFlux {α β σ x : ℝ} (hσ : σ ≠ 0) (hx : 0 < x) :
    HasDerivAt (fun y => σ / 2 * y ^ 2 * statDensity α β σ y)
      (x * (α - β * x) * statDensity α β σ x) x := by
  set k := shape α σ with hk
  set r := rate β σ with hr
  -- on `y > 0`, `y² · y^{k-1} = y^{k+1}`
  have hev : (fun y => σ / 2 * y ^ (k + 1) * exp (-(r * y))) =ᶠ[𝓝 x]
      fun y => σ / 2 * y ^ 2 * statDensity α β σ y := by
    filter_upwards [lt_mem_nhds hx] with y hy
    simp only [statDensity, ← hk, ← hr]
    rw [show k + 1 = 2 + (k - 1) by ring, rpow_add hy, rpow_two]
    ring
  have hd : HasDerivAt (fun y => σ / 2 * y ^ (k + 1) * exp (-(r * y)))
      (σ / 2 * ((k + 1) * x ^ (k + 1 - 1)) * exp (-(r * x)) +
        σ / 2 * x ^ (k + 1) * (exp (-(r * x)) * -(r * 1))) x :=
    ((hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul (σ / 2)).mul
      ((((hasDerivAt_id x).const_mul r).neg).exp)
  refine (hd.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  have e1 : x ^ (k + 1 - 1) = x * x ^ (k - 1) := by
    rw [show k + 1 - 1 = 1 + (k - 1) by ring, rpow_add hx, rpow_one]
  have e2 : x ^ (k + 1) = x ^ 2 * x ^ (k - 1) := by
    rw [show k + 1 = 2 + (k - 1) by ring, rpow_add hx, rpow_two]
  rw [e1, e2, statDensity, ← hk, ← hr, hk, hr, shape, rate]
  field_simp
  ring

theorem shape_pos_iff {α σ : ℝ} (hσ : 0 < σ) : 0 < shape α σ ↔ 0 < α - σ / 2 := by
  rw [shape, sub_pos, lt_div_iff₀ hσ, sub_pos]
  constructor <;> intro h <;> linarith

theorem rate_pos {β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) : 0 < rate β σ := by
  unfold rate; positivity

/-- **The stationary density is normalizable iff `α - σ/2 > 0`.** So the one-species equation has
an invariant probability law on `(0, ∞)` with this density exactly when `α - σ/2 > 0`. -/
theorem integrableOn_statDensity_iff {α β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) :
    IntegrableOn (statDensity α β σ) (Ioi 0) ↔ 0 < α - σ / 2 := by
  rw [← shape_pos_iff hσ]
  have hr := rate_pos hβ hσ
  constructor
  · intro h
    by_contra hk
    push Not at hk
    -- then `x^{k-1}` would be integrable on `(0, 1)`
    have hI : IntegrableOn (fun x : ℝ => x ^ (shape α σ - 1)) (Ioo 0 1) := by
      refine Integrable.mono' ((h.mono_set Ioo_subset_Ioi_self).const_mul (exp (rate β σ)))
        ((measurable_id.pow_const _).aestronglyMeasurable) ?_
      refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_)
      have hxp : 0 ≤ x ^ (shape α σ - 1) := rpow_nonneg hx.1.le _
      rw [Real.norm_eq_abs, abs_of_nonneg hxp, statDensity]
      have h1 : 1 ≤ exp (rate β σ) * exp (-(rate β σ * x)) := by
        rw [← exp_add]
        exact one_le_exp (by nlinarith [hx.2])
      nlinarith
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mp hI
    linarith
  · intro hk
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := shape α σ - 1) (p := 1)
      (by linarith) one_pos hr
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp [statDensity, rpow_one, neg_mul]

/-- For `x ≥ 0` the Gamma pdf is the normalized stationary density. -/
theorem gammaPDFReal_eq {α β σ x : ℝ} (hx : 0 ≤ x) :
    gammaPDFReal (shape α σ) (rate β σ) x =
      rate β σ ^ shape α σ / Gamma (shape α σ) * statDensity α β σ x := by
  simp [gammaPDFReal, hx, statDensity, mul_assoc]

/-- **The mean of the Gamma law**: `∫ x d Gamma(a, r) = a / r`, and `x` is integrable. -/
theorem integral_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (gammaMeasure a r) ∧ ∫ x, x ∂gammaMeasure a r = a / r := by
  have hmeas : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure ℝ), gammaPDF a r x < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hconv : ∀ x : ℝ, (gammaPDF a r x).toReal • x = gammaPDFReal a r x * x := fun x => by
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), smul_eq_mul]
  -- the integral over `(0, ∞)`
  have hIoi : ∫ x in Ioi 0, gammaPDFReal a r x * x = a / r := by
    have : ∀ x ∈ Ioi (0 : ℝ), gammaPDFReal a r x * x =
        r ^ a / Gamma a * (x ^ (a + 1 - 1) * exp (-(r * x))) := fun x hx => by
      have hx' : (0 : ℝ) < x := hx
      simp only [gammaPDFReal, hx'.le, ite_true]
      rw [show a + 1 - 1 = (a - 1) + 1 by ring, rpow_add_one hx'.ne']
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul,
      integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hr, Gamma_add_one ha.ne',
      rpow_add_one (by positivity : (1 / r) ≠ 0)]
    have hG : 0 < Gamma a := Gamma_pos_of_pos ha
    have hra : r ^ a * (1 / r) ^ a = 1 := by
      rw [← mul_rpow hr.le (by positivity), mul_one_div_cancel hr.ne', one_rpow]
    field_simp
    nlinarith [hra]
  have hzero : ∀ x, x ∉ Ioi (0 : ℝ) → gammaPDFReal a r x * x = 0 := fun x hx => by
    rcases (not_lt.mp hx).lt_or_eq with h | h
    · simp [gammaPDFReal, not_le.mpr h]
    · simp [h]
  have hfull : ∫ x, gammaPDFReal a r x * x = a / r := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, hIoi]
  have hint : Integrable (fun x => gammaPDFReal a r x * x) :=
    Integrable.of_integral_ne_zero (by rw [hfull]; positivity)
  refine ⟨?_, ?_⟩
  · rw [gammaMeasure, integrable_withDensity_iff_integrable_smul' hmeas hlt]
    simpa only [hconv] using hint
  · rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas hlt]
    simpa only [hconv] using hfull

/-! ### Lyapunov exponents of the boundary measures -/

namespace TwoSpecies

variable (p : TwoSpecies)

/-- The Lyapunov exponent (invasion rate) of species 1, `λ₁(μ) = ∫ f₁ dμ - σ₁₁/2`. -/
noncomputable def lyap₁ (μ : Measure (ℝ × ℝ)) : ℝ := ∫ z, p.f₁ z.1 z.2 ∂μ - p.σ₁₁ / 2

/-- The Lyapunov exponent (invasion rate) of species 2, `λ₂(μ) = ∫ f₂ dμ - σ₂₂/2`. -/
noncomputable def lyap₂ (μ : Measure (ℝ × ℝ)) : ℝ := ∫ z, p.f₂ z.1 z.2 ∂μ - p.σ₂₂ / 2

/-- `π₁ = Gamma(2α₁/σ₁₁ - 1, scale σ₁₁/(2β₁₁))`, the stationary law of species 1 alone. -/
noncomputable def π₁ : Measure ℝ := gammaMeasure (shape p.α₁ p.σ₁₁) (rate p.β₁₁ p.σ₁₁)

/-- `π₂ = Gamma(2α₂/σ₂₂ - 1, scale σ₂₂/(2β₂₂))`, the stationary law of species 2 alone. -/
noncomputable def π₂ : Measure ℝ := gammaMeasure (shape p.α₂ p.σ₂₂) (rate p.β₂₂ p.σ₂₂)

/-- `μ₀ = δ₀ × δ₀`. -/
noncomputable def μ₀ : Measure (ℝ × ℝ) := Measure.dirac (0, 0)

/-- `μ₁ = π₁ × δ₀`. -/
noncomputable def μ₁ : Measure (ℝ × ℝ) := p.π₁.prod (Measure.dirac 0)

/-- `μ₂ = δ₀ × π₂`. -/
noncomputable def μ₂ : Measure (ℝ × ℝ) := (Measure.dirac 0).prod p.π₂

theorem continuous_f₁ : Continuous fun z : ℝ × ℝ => p.f₁ z.1 z.2 := by unfold f₁; fun_prop
theorem continuous_f₂ : Continuous fun z : ℝ × ℝ => p.f₂ z.1 z.2 := by unfold f₂; fun_prop

theorem lyap₁_μ₀ : p.lyap₁ μ₀ = p.α₁ - p.σ₁₁ / 2 := by
  simp [lyap₁, μ₀, f₁]

theorem lyap₂_μ₀ : p.lyap₂ μ₀ = p.α₂ - p.σ₂₂ / 2 := by
  simp [lyap₂, μ₀, f₂]

/-- **`π₁` exists** (the one-species stationary density of species 1 is normalizable) iff
`λ₁(μ₀) > 0`. -/
theorem exists_π₁_iff (hσ : 0 < p.σ₁₁) :
    IntegrableOn (statDensity p.α₁ p.β₁₁ p.σ₁₁) (Ioi 0) ↔ 0 < p.lyap₁ μ₀ := by
  rw [integrableOn_statDensity_iff p.β₁₁_pos hσ, lyap₁_μ₀]

/-- **`π₂` exists** iff `λ₂(μ₀) > 0`. -/
theorem exists_π₂_iff (hσ : 0 < p.σ₂₂) :
    IntegrableOn (statDensity p.α₂ p.β₂₂ p.σ₂₂) (Ioi 0) ↔ 0 < p.lyap₂ μ₀ := by
  rw [integrableOn_statDensity_iff p.β₂₂_pos hσ, lyap₂_μ₀]

section Exists₁

variable {p} (hσ : 0 < p.σ₁₁) (h₁ : 0 < p.α₁ - p.σ₁₁ / 2)
include hσ h₁

theorem prob_π₁ : IsProbabilityMeasure p.π₁ :=
  isProbabilityMeasure_gammaMeasure ((shape_pos_iff hσ).mpr h₁) (rate_pos p.β₁₁_pos hσ)

/-- The mean of `π₁` is `(α₁ - σ₁₁/2)/β₁₁`. -/
theorem mean_π₁ : Integrable (fun x : ℝ => x) p.π₁ ∧
    ∫ x, x ∂p.π₁ = (p.α₁ - p.σ₁₁ / 2) / p.β₁₁ := by
  obtain ⟨hi, he⟩ := integral_id_gammaMeasure ((shape_pos_iff hσ).mpr h₁)
    (rate_pos p.β₁₁_pos hσ)
  refine ⟨hi, ?_⟩
  rw [π₁, he, shape, rate]
  have := p.β₁₁_pos
  field_simp

theorem integral_μ₁ {g : ℝ × ℝ → ℝ} (hg : Continuous g) :
    ∫ z, g z ∂p.μ₁ = ∫ x, g (x, 0) ∂p.π₁ := by
  have := prob_π₁ hσ h₁
  rw [μ₁, Measure.prod_dirac, integral_map (by fun_prop) hg.aestronglyMeasurable]

/-- `λ₁(μ₁) = 0`: species 1 neither grows nor decays on its own stationary law. -/
theorem lyap₁_μ₁ : p.lyap₁ p.μ₁ = 0 := by
  have := prob_π₁ hσ h₁
  obtain ⟨hi, he⟩ := mean_π₁ hσ h₁
  rw [lyap₁, integral_μ₁ hσ h₁ p.continuous_f₁]
  simp only [f₁, mul_zero, add_zero]
  rw [integral_sub (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul, he]
  have := p.β₁₁_pos
  simp only [probReal_univ, smul_eq_mul, one_mul]
  field_simp
  ring

/-- `λ₂(μ₁) = α₂ - σ₂₂/2 + (β₂₁/β₁₁)(α₁ - σ₁₁/2)`. -/
theorem lyap₂_μ₁ :
    p.lyap₂ p.μ₁ = p.α₂ - p.σ₂₂ / 2 + p.β₂₁ / p.β₁₁ * (p.α₁ - p.σ₁₁ / 2) := by
  have := prob_π₁ hσ h₁
  obtain ⟨hi, he⟩ := mean_π₁ hσ h₁
  rw [lyap₂, integral_μ₁ hσ h₁ p.continuous_f₂]
  simp only [f₂, mul_zero, sub_zero]
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul, he]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

theorem integrable_μ₁ {g : ℝ × ℝ → ℝ} (a b c : ℝ) (hg : ∀ z, g z = a + b * z.1 + c * z.2) :
    Integrable g p.μ₁ := by
  have := prob_π₁ hσ h₁
  have hgc : Continuous g := by
    have : g = fun z => a + b * z.1 + c * z.2 := funext hg
    rw [this]; fun_prop
  rw [μ₁, Measure.prod_dirac, integrable_map_measure hgc.aestronglyMeasurable (by fun_prop)]
  have : (g ∘ fun x : ℝ => (x, (0 : ℝ))) = fun x => a + b * x := funext fun x => by simp [hg]
  rw [this]
  exact (integrable_const a).add ((mean_π₁ hσ h₁).1.const_mul b)

end Exists₁

section Exists₂

variable {p} (hσ : 0 < p.σ₂₂) (h₂ : 0 < p.α₂ - p.σ₂₂ / 2)
include hσ h₂

theorem prob_π₂ : IsProbabilityMeasure p.π₂ :=
  isProbabilityMeasure_gammaMeasure ((shape_pos_iff hσ).mpr h₂) (rate_pos p.β₂₂_pos hσ)

/-- The mean of `π₂` is `(α₂ - σ₂₂/2)/β₂₂`. -/
theorem mean_π₂ : Integrable (fun x : ℝ => x) p.π₂ ∧
    ∫ x, x ∂p.π₂ = (p.α₂ - p.σ₂₂ / 2) / p.β₂₂ := by
  obtain ⟨hi, he⟩ := integral_id_gammaMeasure ((shape_pos_iff hσ).mpr h₂)
    (rate_pos p.β₂₂_pos hσ)
  refine ⟨hi, ?_⟩
  rw [π₂, he, shape, rate]
  have := p.β₂₂_pos
  field_simp

theorem integral_μ₂ {g : ℝ × ℝ → ℝ} (hg : Continuous g) :
    ∫ z, g z ∂p.μ₂ = ∫ x, g (0, x) ∂p.π₂ := by
  have := prob_π₂ hσ h₂
  rw [μ₂, Measure.dirac_prod, integral_map (by fun_prop) hg.aestronglyMeasurable]

/-- `λ₁(μ₂) = α₁ - σ₁₁/2 + (β₁₂/β₂₂)(α₂ - σ₂₂/2)`. -/
theorem lyap₁_μ₂ :
    p.lyap₁ p.μ₂ = p.α₁ - p.σ₁₁ / 2 + p.β₁₂ / p.β₂₂ * (p.α₂ - p.σ₂₂ / 2) := by
  have := prob_π₂ hσ h₂
  obtain ⟨hi, he⟩ := mean_π₂ hσ h₂
  rw [lyap₁, integral_μ₂ hσ h₂ p.continuous_f₁]
  simp only [f₁, mul_zero, sub_zero]
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul, he]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-- `λ₂(μ₂) = 0`. -/
theorem lyap₂_μ₂ : p.lyap₂ p.μ₂ = 0 := by
  have := prob_π₂ hσ h₂
  obtain ⟨hi, he⟩ := mean_π₂ hσ h₂
  rw [lyap₂, integral_μ₂ hσ h₂ p.continuous_f₂]
  simp only [f₂, mul_zero, add_zero]
  rw [integral_sub (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul, he]
  have := p.β₂₂_pos
  simp only [probReal_univ, smul_eq_mul, one_mul]
  field_simp
  ring

theorem integrable_μ₂ {g : ℝ × ℝ → ℝ} (a b c : ℝ) (hg : ∀ z, g z = a + b * z.1 + c * z.2) :
    Integrable g p.μ₂ := by
  have := prob_π₂ hσ h₂
  have hgc : Continuous g := by
    have : g = fun z => a + b * z.1 + c * z.2 := funext hg
    rw [this]; fun_prop
  rw [μ₂, Measure.dirac_prod, integrable_map_measure hgc.aestronglyMeasurable (by fun_prop)]
  have : (g ∘ Prod.mk (0 : ℝ)) = fun x => a + c * x := funext fun x => by simp [hg]
  rw [this]
  exact (integrable_const a).add ((mean_π₂ hσ h₂).1.const_mul c)

end Exists₂

/-! ### Convex combinations and Assumption 4 -/

theorem integral_mix {μ ν : Measure (ℝ × ℝ)} {g : ℝ × ℝ → ℝ} (hμ : Integrable g μ)
    (hν : Integrable g ν) {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) :
    ∫ z, g z ∂(ENNReal.ofReal q • μ + ENNReal.ofReal r • ν) = q * ∫ z, g z ∂μ + r * ∫ z, g z ∂ν := by
  rw [integral_add_measure (hμ.smul_measure ENNReal.ofReal_ne_top)
      (hν.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hq, ENNReal.toReal_ofReal hr, smul_eq_mul, smul_eq_mul]

theorem integrable_μ₀ (g : ℝ × ℝ → ℝ) : Integrable g μ₀ := by
  unfold μ₀
  exact integrable_dirac (by simp)

/-- **Assumption 4 in case C2(i).** If `λ₁(μ₀) > 0` and `λ₂(μ₁) > 0` (with `M = {μ₀, μ₁}`), then
every convex combination `μ = q₀μ₀ + q₁μ₁` has `max(λ₁(μ), λ₂(μ)) > 0`. -/
theorem assumption4_C2i (hσ : 0 < p.σ₁₁) (h10 : 0 < p.lyap₁ μ₀) (h21 : 0 < p.lyap₂ p.μ₁)
    {q₀ q₁ : ℝ} (hq₀ : 0 ≤ q₀) (hq₁ : 0 ≤ q₁) (hq : q₀ + q₁ = 1) :
    0 < max (p.lyap₁ (ENNReal.ofReal q₀ • μ₀ + ENNReal.ofReal q₁ • p.μ₁))
      (p.lyap₂ (ENNReal.ofReal q₀ • μ₀ + ENNReal.ofReal q₁ • p.μ₁)) := by
  have h₁ : 0 < p.α₁ - p.σ₁₁ / 2 := by rwa [lyap₁_μ₀] at h10
  have e₁ : p.lyap₁ (ENNReal.ofReal q₀ • μ₀ + ENNReal.ofReal q₁ • p.μ₁) =
      q₀ * p.lyap₁ μ₀ + q₁ * p.lyap₁ p.μ₁ := by
    simp only [lyap₁]
    rw [integral_mix (integrable_μ₀ _) (integrable_μ₁ hσ h₁ p.α₁ (-p.β₁₁) p.β₁₂
      (fun z => by simp [f₁]; ring)) hq₀ hq₁]
    have : q₁ = 1 - q₀ := by linarith
    subst this; ring
  have e₂ : p.lyap₂ (ENNReal.ofReal q₀ • μ₀ + ENNReal.ofReal q₁ • p.μ₁) =
      q₀ * p.lyap₂ μ₀ + q₁ * p.lyap₂ p.μ₁ := by
    simp only [lyap₂]
    rw [integral_mix (integrable_μ₀ _) (integrable_μ₁ hσ h₁ p.α₂ p.β₂₁ (-p.β₂₂)
      (fun z => by simp [f₂]; ring)) hq₀ hq₁]
    have : q₁ = 1 - q₀ := by linarith
    subst this; ring
  rw [e₁, e₂, lyap₁_μ₁ hσ h₁]
  rcases hq₀.lt_or_eq with h | h
  · exact lt_max_of_lt_left (by nlinarith)
  · subst h
    have : q₁ = 1 := by linarith
    subst this
    exact lt_max_of_lt_right (by linarith [p.lyap₂ μ₀])

/-- **Assumption 4 in case C3(i).** If `λ₂(μ₀) > 0` and `λ₁(μ₂) > 0` (with `M = {μ₀, μ₂}`), then
every convex combination `μ = q₀μ₀ + q₂μ₂` has `max(λ₁(μ), λ₂(μ)) > 0`. -/
theorem assumption4_C3i (hσ : 0 < p.σ₂₂) (h20 : 0 < p.lyap₂ μ₀) (h12 : 0 < p.lyap₁ p.μ₂)
    {q₀ q₂ : ℝ} (hq₀ : 0 ≤ q₀) (hq₂ : 0 ≤ q₂) (hq : q₀ + q₂ = 1) :
    0 < max (p.lyap₁ (ENNReal.ofReal q₀ • μ₀ + ENNReal.ofReal q₂ • p.μ₂))
      (p.lyap₂ (ENNReal.ofReal q₀ • μ₀ + ENNReal.ofReal q₂ • p.μ₂)) := by
  have h₂ : 0 < p.α₂ - p.σ₂₂ / 2 := by rwa [lyap₂_μ₀] at h20
  have e₁ : p.lyap₁ (ENNReal.ofReal q₀ • μ₀ + ENNReal.ofReal q₂ • p.μ₂) =
      q₀ * p.lyap₁ μ₀ + q₂ * p.lyap₁ p.μ₂ := by
    simp only [lyap₁]
    rw [integral_mix (integrable_μ₀ _) (integrable_μ₂ hσ h₂ p.α₁ (-p.β₁₁) p.β₁₂
      (fun z => by simp [f₁]; ring)) hq₀ hq₂]
    have : q₂ = 1 - q₀ := by linarith
    subst this; ring
  have e₂ : p.lyap₂ (ENNReal.ofReal q₀ • μ₀ + ENNReal.ofReal q₂ • p.μ₂) =
      q₀ * p.lyap₂ μ₀ + q₂ * p.lyap₂ p.μ₂ := by
    simp only [lyap₂]
    rw [integral_mix (integrable_μ₀ _) (integrable_μ₂ hσ h₂ p.α₂ p.β₂₁ (-p.β₂₂)
      (fun z => by simp [f₂]; ring)) hq₀ hq₂]
    have : q₂ = 1 - q₀ := by linarith
    subst this; ring
  rw [e₁, e₂, lyap₂_μ₂ hσ h₂]
  rcases hq₀.lt_or_eq with h | h
  · exact lt_max_of_lt_right (by nlinarith)
  · subst h
    have : q₂ = 1 := by linarith
    subst this
    exact lt_max_of_lt_left (by linarith [p.lyap₁ μ₀])

/-- **Assumption 4 in case C4(i)** ("it is straightforward that `max{λ₁(μ), λ₂(μ)} > 0`"). If all
four of `λ₁(μ₀), λ₂(μ₀), λ₁(μ₂), λ₂(μ₁)` are positive, then every convex combination
`μ = q₀μ₀ + q₁μ₁ + q₂μ₂` has `max(λ₁(μ), λ₂(μ)) > 0`. -/
theorem assumption4_C4i (hσ₁ : 0 < p.σ₁₁) (hσ₂ : 0 < p.σ₂₂) (h10 : 0 < p.lyap₁ μ₀)
    (h20 : 0 < p.lyap₂ μ₀) (h12 : 0 < p.lyap₁ p.μ₂) (h21 : 0 < p.lyap₂ p.μ₁)
    {q₀ q₁ q₂ : ℝ} (hq₀ : 0 ≤ q₀) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq : q₀ + q₁ + q₂ = 1) :
    let μ := ENNReal.ofReal q₀ • μ₀ + ENNReal.ofReal q₁ • p.μ₁ + ENNReal.ofReal q₂ • p.μ₂
    0 < max (p.lyap₁ μ) (p.lyap₂ μ) := by
  intro μ
  have h₁ : 0 < p.α₁ - p.σ₁₁ / 2 := by rwa [lyap₁_μ₀] at h10
  have h₂ : 0 < p.α₂ - p.σ₂₂ / 2 := by rwa [lyap₂_μ₀] at h20
  have hmix : ∀ {g : ℝ × ℝ → ℝ}, Integrable g p.μ₁ → Integrable g p.μ₂ →
      ∫ z, g z ∂μ = q₀ * ∫ z, g z ∂μ₀ + q₁ * ∫ z, g z ∂p.μ₁ + q₂ * ∫ z, g z ∂p.μ₂ := by
    intro g h1 h2
    have hA : Integrable g (ENNReal.ofReal q₀ • μ₀ + ENNReal.ofReal q₁ • p.μ₁) :=
      ((integrable_μ₀ g).smul_measure ENNReal.ofReal_ne_top).add_measure
        (h1.smul_measure ENNReal.ofReal_ne_top)
    simp only [μ]
    rw [integral_add_measure hA (h2.smul_measure ENNReal.ofReal_ne_top),
      integral_mix (integrable_μ₀ g) h1 hq₀ hq₁, integral_smul_measure,
      ENNReal.toReal_ofReal hq₂, smul_eq_mul]
  have e₁ : p.lyap₁ μ = q₀ * p.lyap₁ μ₀ + q₁ * p.lyap₁ p.μ₁ + q₂ * p.lyap₁ p.μ₂ := by
    simp only [lyap₁]
    rw [hmix (integrable_μ₁ hσ₁ h₁ p.α₁ (-p.β₁₁) p.β₁₂ (fun z => by simp [f₁]; ring))
      (integrable_μ₂ hσ₂ h₂ p.α₁ (-p.β₁₁) p.β₁₂ (fun z => by simp [f₁]; ring))]
    have : q₂ = 1 - q₀ - q₁ := by linarith
    subst this; ring
  have e₂ : p.lyap₂ μ = q₀ * p.lyap₂ μ₀ + q₁ * p.lyap₂ p.μ₁ + q₂ * p.lyap₂ p.μ₂ := by
    simp only [lyap₂]
    rw [hmix (integrable_μ₁ hσ₁ h₁ p.α₂ p.β₂₁ (-p.β₂₂) (fun z => by simp [f₂]; ring))
      (integrable_μ₂ hσ₂ h₂ p.α₂ p.β₂₁ (-p.β₂₂) (fun z => by simp [f₂]; ring))]
    have : q₂ = 1 - q₀ - q₁ := by linarith
    subst this; ring
  rw [e₁, e₂, lyap₁_μ₁ hσ₁ h₁, lyap₂_μ₂ hσ₂ h₂]
  by_cases h : q₀ + q₂ = 0
  · have h0 : q₀ = 0 := by linarith
    have h2 : q₂ = 0 := by linarith
    have h1 : q₁ = 1 := by linarith
    subst h0 h1 h2
    exact lt_max_of_lt_right (by linarith)
  · have : 0 < q₀ + q₂ := lt_of_le_of_ne (by linarith) (Ne.symm h)
    exact lt_max_of_lt_left (by
      rcases hq₀.lt_or_eq with h0 | h0
      · nlinarith
      · subst h0; nlinarith)

end TwoSpecies

end SgLVResilience
