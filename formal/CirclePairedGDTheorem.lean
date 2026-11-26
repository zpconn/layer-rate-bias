module

public import CirclePairedGDEndpoint
public import CirclePairedGDTypical
public import CirclePairedGDClocksTail
import Mathlib.Tactic

/-! Predictions for two discrete gradient descent runs on the same seed.
The index n denotes the grid size minus one, as in the finite-grid
coefficient. Both runs stop at the deterministic manuscript horizon. -/

@[expose] public section
noncomputable section
namespace CirclePairedGDTheorem

open MeasureTheory Real Filter Topology CircleEscapeBridge CircleFlowTracking
  CirclePairedCoefficient CirclePairedOrdering CircleWeightedDynamics CirclePairedGDEndpoint

/-- A single measurable set of seeds controls both training residuals and
the error of the predicted difference of the two population means. -/
def FitsAndTracks (n : ℕ) : Prop :=
  let N := n+1
  let m := gridWidth n
  let x := (n:ℝ)+1
  let H := horizon x
  ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ ≤ 2/√x ∧
    ∀ z ∈ E, rms (1/2) 1 N z H ≤ 1/x^3 ∧ rms 2 1 N z H ≤ 1/x^3 ∧
      |scaled n z - coefficient n * score N m z| ≤ 10/x^(33/32:ℝ)

private theorem tracks_of_fit {n : ℕ} (h : FitsAndTracks n) : Tracks n := by
  obtain ⟨E,_,bad,inside⟩ := h
  exact ⟨E,bad,fun z hz => (inside z hz).2.2⟩

/-- Unit readout steps and hidden steps one half and two. Both networks fit
and the initial grid deficit predicts the ordering, counting ties as misses. -/
theorem fit_and_order :
    ∀ᶠ n : ℕ in atTop, Odd (n+1) → FitsAndTracks n ∧
      (seedLaw (gridWidth n)).real (CirclePairedGDEndpoint.miss n) ≤
        (2+2*CircleScoreMargin.densityBound)/√((n:ℝ)+1) := by
  filter_upwards [CirclePairedGDTypical.common_event, sign_of_tracks] with n h hs ho
  have fit : FitsAndTracks n := by
    simpa only [FitsAndTracks,scaled,contrast,gridWidth,Nat.cast_add,Nat.cast_one] using h ho
  exact ⟨fit, hs (tracks_of_fit fit)⟩

/-- Along any growing sequence of odd grid sizes, the scaled prediction error
converges to zero in probability for the two actual nonlinear GD iterates. -/
theorem limiting_prediction (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (odd : ∀ᶠ i in atTop, Odd (n i+1)) (ε : ℝ) (he : 0<ε) :
    Tendsto (fun i => (seedLaw (gridWidth (n i))).real
      {z | ε ≤ |scaled (n i) z - (π^2/40)*score (n i+1) (gridWidth (n i)) z|})
      atTop (𝓝 0) := by
  refine prediction_of_tracks n grow ?_ ε he
  filter_upwards [grow.eventually fit_and_order,odd] with i h ho
  exact tracks_of_fit (h ho).1

/-- The same measured GD contrast has a reliable prediction on typical seeds
and a divergent unscaled mean-square prediction error under the entire Gaussian law.
The only design hypotheses are that the grid sizes tend to infinity and are eventually odd. -/
theorem paired_discrete_gradient_descent (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (odd : ∀ᶠ i in atTop, Odd (n i+1)) :
    (∀ᶠ i in atTop, FitsAndTracks (n i) ∧
      (seedLaw (gridWidth (n i))).real (CirclePairedGDEndpoint.miss (n i)) ≤
        (2+2*CircleScoreMargin.densityBound)/√((n i:ℝ)+1)) ∧
    (∀ ε : ℝ, 0<ε → Tendsto (fun i => (seedLaw (gridWidth (n i))).real
      {z | ε ≤ |scaled (n i) z - (π^2/40)*score (n i+1) (gridWidth (n i)) z|})
      atTop (𝓝 0)) ∧
    Tendsto (fun i => CirclePairedGDClocksTail.mse (n i+1) (horizon ((n i+1:ℕ):ℝ))
      1 (coefficient (n i))) atTop atTop ∧
    Tendsto (fun i => CirclePairedGDClocksTail.mse (n i+1) (horizon ((n i+1:ℕ):ℝ))
      1 (π^2/40)) atTop atTop := by
  refine ⟨?_,limiting_prediction n grow odd,CirclePairedGDClocksTail.horizon_predictions n grow odd⟩
  filter_upwards [grow.eventually fit_and_order,odd] with i h ho
  exact h ho

end CirclePairedGDTheorem
