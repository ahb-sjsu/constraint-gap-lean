/-
Machine check of the constraint-gap algebra in Egemen Tuncarslan's
Proposal A, Section 3.

Real inner product space E, V a subspace with orthogonal projection P,
g the loss gradient, eps the budget. "L locally linear with gradient g"
means the objective is the linear functional  x |-> inner g x.

The proposal asserts:
  optimize-then-project     step eps * P g / ||g||     gain eps * ||P g||^2 / ||g||
  optimize-under-constraint step eps * P g / ||P g||   gain eps * ||P g||
  relative gap = 1 - ||P g|| / ||g||

Theorems 1-4 confirm all of that. Theorems 5-6 are the observation the
proposal does not make.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (V : Submodule ℝ E) [V.HasOrthogonalProjection]

/-- 1. The gradient pairs with its own projection as that projection's squared
norm. Both gain formulas rest on this. -/
theorem inner_g_proj (g : E) : ⟪g, V.starProjection g⟫ = ‖V.starProjection g‖ ^ 2 := by
  have h0 : ⟪g - V.starProjection g, V.starProjection g⟫ = 0 :=
    V.starProjection_inner_eq_zero g _ (Submodule.coe_mem _)
  rw [inner_sub_left, sub_eq_zero] at h0
  rw [h0, real_inner_self_eq_norm_sq]

/-- 2. Gain of the projected unconstrained step. -/
theorem gain_project (g : E) (hg : g ≠ 0) (eps : ℝ) :
    ⟪g, (eps / ‖g‖) • V.starProjection g⟫
      = eps * ‖V.starProjection g‖ ^ 2 / ‖g‖ := by
  have h1 : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  rw [real_inner_smul_right, inner_g_proj]
  field_simp

/-- 3. Gain of the best step inside the constraint set. -/
theorem gain_constrained (g : E) (hPg : V.starProjection g ≠ 0) (eps : ℝ) :
    ⟪g, (eps / ‖V.starProjection g‖) • V.starProjection g⟫
      = eps * ‖V.starProjection g‖ := by
  have h2 : ‖V.starProjection g‖ ≠ 0 := norm_ne_zero_iff.mpr hPg
  rw [real_inner_smul_right, inner_g_proj]
  field_simp
  try ring

/-- 4. The ratio of the two gains is cos theta, so the relative gap is
1 - cos theta exactly as the proposal states. -/
theorem gain_ratio (g : E) (hg : g ≠ 0) (hPg : V.starProjection g ≠ 0)
    (eps : ℝ) (heps : eps ≠ 0) :
    (eps * ‖V.starProjection g‖ ^ 2 / ‖g‖) / (eps * ‖V.starProjection g‖)
      = ‖V.starProjection g‖ / ‖g‖ := by
  have h1 : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have h2 : ‖V.starProjection g‖ ≠ 0 := norm_ne_zero_iff.mpr hPg
  field_simp
  try ring

/-- cos theta is at most one, so the gap is nonnegative. -/
theorem cos_le_one (g : E) : ‖V.starProjection g‖ ≤ ‖g‖ :=
  V.norm_starProjection_apply_le g

/-! ## What the proposal does not say -/

/-- 5. The projected step does not use the budget. Its length is
eps * cos theta, short of eps whenever the gradient leaves V. -/
theorem projected_step_norm (g : E) (hg : g ≠ 0) (eps : ℝ) (heps : 0 ≤ eps) :
    ‖(eps / ‖g‖) • V.starProjection g‖ = eps * (‖V.starProjection g‖ / ‖g‖) := by
  have h1 : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg heps,
    abs_of_nonneg (norm_nonneg g)]
  field_simp

/-- 6. Rescaling the projected step back to the budget returns EXACTLY the
constrained optimum. So in the locally linear case the measured gap is the
cost of not renormalising, and it vanishes for any method whose step has
full budget length. -/
theorem rescaled_projection_eq_constrained (g : E) (hg : g ≠ 0)
    (hPg : V.starProjection g ≠ 0) (eps : ℝ) (heps : 0 < eps) :
    (eps / ‖(eps / ‖g‖) • V.starProjection g‖) • ((eps / ‖g‖) • V.starProjection g)
      = (eps / ‖V.starProjection g‖) • V.starProjection g := by
  have h1 : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have h2 : ‖V.starProjection g‖ ≠ 0 := norm_ne_zero_iff.mpr hPg
  rw [projected_step_norm V g hg eps (le_of_lt heps), smul_smul]
  congr 1
  field_simp
  try ring
