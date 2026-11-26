module

public import CirclePairedGDTail
import all CirclePairedGDEndpoint
import all CirclePairedOrdering
import Mathlib.Tactic

/-! Explicit horizons for the unconditional mean-square error of the slow-minus-fast
discrete network contrast. The width at grid size `N` is always `N^32`. -/

@[expose] public section
noncomputable section
namespace CirclePairedGDClocksTail

open Real Filter Topology MeasureTheory CircleEscapeBridge CirclePairedGDEndpoint
  CirclePairedCoefficient CircleFlowTracking

/-- Squared error, integrated over the full common Gaussian initialization.
The predictor multiplies the initial deficit by the specified coefficient divided by `N²`. -/
def mse (N T : ℕ) (η d : ℝ) : ℝ :=
  ∫ z, (contrast N (N^32) T η z - (d/(N:ℝ)^2)*score N (N^32) z)^2 ∂seedLaw (N^32)

/-- The logarithmic cap used for the early divergence result. -/
def logarithmicSteps (N : ℕ) : ℕ := ⌈60*log N⌉₊

/-- Number of steps of length `η` that cover the flow horizon. -/
def physicalSteps (η : ℝ) (N : ℕ) : ℕ := ⌈(horizon N:ℝ)/η⌉₊

private theorem physical_lower (η : ℝ) (hη : 0<η) :
    ∀ᶠ N : ℕ in atTop, 60*log N ≤ (physicalSteps η N:ℝ) := by
  filter_upwards [CirclePairedGDCost.horizon_lower (60*η)] with N h
  apply le_trans _ (Nat.le_ceil ((horizon N:ℝ)/η))
  exact (le_div_iff₀ hη).2 (by linarith only [h])

/-- Any deterministic sequence of at least `60 log N` steps has divergent
unscaled squared prediction error, for every eventually bounded coefficient. -/
theorem at_late_clock (N T : ℕ → ℕ) (d : ℕ → ℝ) {η : ℝ} (hη : 0<η)
    (grow : Tendsto N atTop atTop) (odd : ∀ᶠ j in atTop, Odd (N j))
    {D : ℝ} (bounded : ∀ᶠ j in atTop, |d j|≤D)
    (late : ∀ᶠ j in atTop, 60*log (N j) ≤ (T j:ℝ)) :
    Tendsto (fun j => mse (N j) (T j) η (d j)) atTop atTop := by
  obtain ⟨gt,small⟩ := CirclePairedGDCost.polynomial N T grow late
  apply CirclePairedGDTail.of_small N (fun j => N j^32) T d η hη gt _ bounded small
  filter_upwards [grow.eventually_ge_atTop 3,odd] with j hn ho
  exact ⟨hn,ho,Nat.pow_pos (by omega)⟩

/-- Same deterministic update count as in the unit-step fitting and
in-probability prediction theorem. -/
theorem at_horizon (N : ℕ → ℕ) (d : ℕ → ℝ) {η : ℝ} (hη : 0<η)
    (grow : Tendsto N atTop atTop) (odd : ∀ᶠ j in atTop, Odd (N j))
    {D : ℝ} (bounded : ∀ᶠ j in atTop, |d j|≤D) :
    Tendsto (fun j => mse (N j) (horizon (N j)) η (d j)) atTop atTop :=
  at_late_clock N _ d hη grow odd bounded (grow.eventually (CirclePairedGDCost.horizon_lower 60))

/-- Divergence holds already after the logarithmic number of updates. -/
theorem at_logarithmic (N : ℕ → ℕ) (d : ℕ → ℝ) {η : ℝ} (hη : 0<η)
    (grow : Tendsto N atTop atTop) (odd : ∀ᶠ j in atTop, Odd (N j))
    {D : ℝ} (bounded : ∀ᶠ j in atTop, |d j|≤D) :
    Tendsto (fun j => mse (N j) (logarithmicSteps (N j)) η (d j)) atTop atTop :=
  at_late_clock N _ d hη grow odd bounded (.of_forall fun j => Nat.le_ceil (60*log (N j)))

/-- Matching the elapsed flow time also produces divergence for every
fixed positive scalar step length. -/
theorem at_physical_clock (N : ℕ → ℕ) (d : ℕ → ℝ) {η : ℝ} (hη : 0<η)
    (grow : Tendsto N atTop atTop) (odd : ∀ᶠ j in atTop, Odd (N j))
    {D : ℝ} (bounded : ∀ᶠ j in atTop, |d j|≤D) :
    Tendsto (fun j => mse (N j) (physicalSteps η (N j)) η (d j)) atTop atTop :=
  at_late_clock N _ d hη grow odd bounded (grow.eventually (physical_lower η hη))

/-- At the main unit-step endpoint, both the exact finite-grid prediction
and its limiting coefficient have divergent unconditional squared error. -/
theorem horizon_predictions (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (odd : ∀ᶠ j in atTop, Odd (n j+1)) :
    Tendsto (fun j => mse (n j+1) (horizon ((n j+1 : ℕ) : ℝ)) 1 (CirclePairedOrdering.coefficient (n j)))
      atTop atTop ∧
    Tendsto (fun j => mse (n j+1) (horizon ((n j+1 : ℕ) : ℝ)) 1 (π^2/40)) atTop atTop := by
  have gn : Tendsto (fun j => n j+1) atTop atTop :=
    tendsto_atTop_mono (f:=n) (fun j => Nat.le_succ _) grow
  have lim : Tendsto (fun j => CirclePairedOrdering.coefficient (n j)) atTop (𝓝 (π^2/40)) :=
    CircleLayerRates.coefficient_limit.comp grow
  have hb : ∀ᶠ j in atTop, |CirclePairedOrdering.coefficient (n j)| ≤ |π^2/40|+1 :=
    lim.abs.eventually_le_const (lt_add_one _)
  have hc : ∀ᶠ _j : ℕ in atTop, |π^2/40| ≤ |π^2/40| := .of_forall fun _ => le_rfl
  constructor
  · exact at_horizon (fun j => n j+1) (fun j => CirclePairedOrdering.coefficient (n j))
      (η:=1) one_pos gn odd hb
  · exact at_horizon (fun j => n j+1) (fun _ => π^2/40) (η:=1) one_pos gn odd hc

end CirclePairedGDClocksTail
