/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# The four resilience measures (Section 2.4)

For `W(t) = 𝔼[YᵀY] > 0` the paper defines
* `ℛᵗ_ins = -(d/dt) ln W(t)^{1/2}` (instantaneous return rate),
* `ℛᵗ_ave = -(ln W(t)^{1/2} - ln W(0)^{1/2}) / t` (average return rate),
* `ℛ_c = -½ α(S)`, with `α(S)` the largest real part of an eigenvalue of `S` (rate of convergence),
* `ℛ_∞ = lim_{t→∞} ℛᵗ_ave` (asymptotic resilience).

We prove the closed forms `ℛᵗ_ins = -W'(t) / (2W(t))` and `ℛᵗ_ave = -(1/2t) ln(W(t)/W(0))`, their
sign interpretations, and that `ℛ_∞ = 0` whenever `W(t)` tends to a positive limit
(`rInf_eq_zero`). With noise in (2.16) the stationary second moment is positive, so this is the
situation of Section 3, where Table 2 reports small positive values of `ℛ_∞`; those are values of
`ℛᵗ_ave` at a finite time.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

open Filter Topology Real

namespace SgLVResilience

/-- The instantaneous return rate `ℛᵗ_ins = -(d/dt) ln W(t)^{1/2}`. -/
noncomputable def rIns (W : ℝ → ℝ) (t : ℝ) : ℝ := -deriv (fun s => log (√(W s))) t

/-- The average return rate `ℛᵗ_ave = -(ln W(t)^{1/2} - ln W(0)^{1/2}) / t` over `[0, t]`. -/
noncomputable def rAve (W : ℝ → ℝ) (t : ℝ) : ℝ := -(log (√(W t)) - log (√(W 0))) / t

/-- The spectral abscissa `α(S) = max Re λ(S)` of a real square matrix. -/
noncomputable def spectralAbscissa {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) :
    ℝ :=
  sSup ((fun z : ℂ => z.re) '' spectrum ℂ (S.map ((↑) : ℝ → ℂ)))

/-- The rate of convergence `ℛ_c = -½ α(S)`. -/
noncomputable def rC {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) : ℝ :=
  -spectralAbscissa S / 2

/-- The asymptotic resilience `ℛ_∞ = lim_{t→∞} ℛᵗ_ave`. -/
noncomputable def rInf (W : ℝ → ℝ) : ℝ := limUnder atTop (rAve W)

variable {W : ℝ → ℝ} {t W' : ℝ}

/-- `ℛᵗ_ins = -W'(t) / (2 W(t))`. -/
theorem rIns_eq (hW : 0 < W t) (hd : HasDerivAt W W' t) : rIns W t = -(W' / (2 * W t)) := by
  have hev : (fun s => log (√(W s))) =ᶠ[𝓝 t] fun s => log (W s) / 2 := by
    filter_upwards [hd.continuousAt.eventually (lt_mem_nhds hW)] with s hs
    exact log_sqrt hs.le
  have hd' : HasDerivAt (fun s => log (W s) / 2) (W' / W t / 2) t :=
    (hd.log hW.ne').div_const 2
  rw [rIns, hev.deriv_eq, hd'.deriv]
  field_simp

/-- `ℛᵗ_ave = -(1/2t) ln(W(t) / W(0))`. -/
theorem rAve_eq (h0 : 0 < W 0) (ht : 0 < W t) :
    rAve W t = -(1 / (2 * t)) * log (W t / W 0) := by
  rw [rAve, log_sqrt ht.le, log_sqrt h0.le, log_div ht.ne' h0.ne']
  ring

/-- `ℛᵗ_ins > 0` exactly when `W` is decreasing at `t` (`W'(t) < 0`). -/
theorem rIns_pos_iff (hW : 0 < W t) (hd : HasDerivAt W W' t) : 0 < rIns W t ↔ W' < 0 := by
  rw [rIns_eq hW hd, neg_pos, div_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · exact h
  · intro h; exact Or.inr ⟨h, by linarith⟩

/-- For `t > 0`, `ℛᵗ_ave > 0` exactly when `W(t) < W(0)`. -/
theorem rAve_pos_iff (h0 : 0 < W 0) (ht : 0 < W t) (htp : 0 < t) :
    0 < rAve W t ↔ W t < W 0 := by
  rw [rAve_eq h0 ht, neg_mul, neg_pos, mul_neg_iff]
  have hpos : 0 < 1 / (2 * t) := by positivity
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · have := (log_neg_iff (div_pos ht h0)).mp h
      rwa [div_lt_one h0] at this
    · linarith
  · intro h
    refine Or.inl ⟨hpos, ?_⟩
    exact log_neg (div_pos ht h0) ((div_lt_one h0).mpr h)

/-- If `W(t)` tends to a positive limit, then `ℛᵗ_ave → 0`. -/
theorem tendsto_rAve_zero {Winf : ℝ} (hlim : Tendsto W atTop (𝓝 Winf)) (hpos : 0 < Winf) :
    Tendsto (rAve W) atTop (𝓝 0) := by
  have hc : ContinuousAt (fun w => log (√w)) Winf :=
    (continuousAt_log (Real.sqrt_pos.mpr hpos).ne').comp Real.continuous_sqrt.continuousAt
  have hnum : Tendsto (fun s => -(log (√(W s)) - log (√(W 0)))) atTop
      (𝓝 (-(log (√Winf) - log (√(W 0))))) :=
    ((hc.tendsto.comp hlim).sub tendsto_const_nhds).neg
  exact hnum.div_atTop tendsto_id

/-- **The asymptotic resilience vanishes.** If `W(t)` tends to a positive limit (for example the
trace of a positive stationary second moment), then `ℛ_∞ = 0`. -/
theorem rInf_eq_zero {Winf : ℝ} (hlim : Tendsto W atTop (𝓝 Winf)) (hpos : 0 < Winf) :
    rInf W = 0 :=
  (tendsto_rAve_zero hlim hpos).limUnder_eq

end SgLVResilience
