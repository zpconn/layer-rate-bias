module
public import CircleFlowMoments
public import CircleActualTracking
import all CircleFlowMoments
import all CircleEscape
import all CircleEscapeBridge
import all CircleFlowPath
import Mathlib.Tactic

/-! A posteriori population error from an arbitrary computed endpoint used
as the starting state of an exact continuation. -/
public section
noncomputable section
namespace CircleContinuationBound
open Real CircleFlowPath CircleFlowMoments CircleEscapeBridge
variable {m N : ℕ}
private theorem block_sq (z : State m) (j : Fin m) :
    neuronLength z j ^ 2= |(initial z).a j|^2+‖(initial z).w j‖^2 := by
  rw [neuron_length_sq,Fin.sum_univ_three,hidden_sq,sq_abs]
  change _ = z (j,0)^2+(z (j,1)^2+z (j,2)^2)
  ring

theorem mean_movement (z q : State m) :
    |mean q-mean z| ≤ (1/sqrt m)/π *
      (sqrt (squared (q-z)) * sqrt (squared z)+squared (q-z)/2) := by
  let δ := q-z
  have each (j : Fin m) :
      |(initial q).a j*‖(initial q).w j‖-(initial z).a j*‖(initial z).w j‖| ≤
      neuronLength δ j*neuronLength z j+neuronLength δ j^2/2 := by
    let a := (initial z).a j
    let d := (initial δ).a j
    let w := (initial z).w j
    let u := (initial δ).w j
    have ea : (initial q).a j=a+d := by dsimp [initial,a,d,δ];ring
    have ew : (initial q).w j=w+u := by apply Complex.ext <;> dsimp [initial,w,u,δ] <;> ring
    have h1 : neuronLength z j^2=|a|^2+‖w‖^2 := block_sq z j
    have h2 : neuronLength δ j^2=|d|^2+‖u‖^2 := block_sq δ j
    have cs : |a| *‖u‖+|d| *‖w‖≤neuronLength δ j*neuronLength z j := by
      apply (sq_le_sq₀ (by positivity) (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))).mp
      change (|a| *‖u‖+|d| *‖w‖)^2≤(neuronLength δ j*neuronLength z j)^2
      rw [mul_pow,h1,h2]
      nlinarith only [sq_nonneg (|a| *|d|-‖u‖*‖w‖)]
    rw [ea,ew]
    change |(a+d)*‖w+u‖-a*‖w‖|≤_
    rw [show (a+d)*‖w+u‖-a*‖w‖=a*(‖w+u‖-‖w‖)+d*‖w+u‖ by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_norm]
    have hv : |‖w+u‖-‖w‖|≤‖u‖ := (abs_norm_sub_norm_le _ _).trans_eq (by simp)
    nlinarith only [cs,h2,sq_nonneg (|d|-‖u‖),mul_le_mul_of_nonneg_left hv (abs_nonneg a),
      mul_le_mul_of_nonneg_left (norm_add_le w u) (abs_nonneg d)]
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (s:=Finset.univ) fun j _ => each j)
  rw [Finset.sum_add_distrib,←Finset.sum_div,sum_length_sq] at hs
  have cs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (neuronLength δ) (neuronLength z)
  simp only [sum_length_sq] at cs
  rw [mean,mean,CircleEscape.populationMean,CircleEscape.populationMean,←mul_sub,←Finset.sum_sub_distrib,abs_mul,
    abs_of_nonneg (by positivity : 0≤(1/sqrt (m:ℝ))/π)]
  exact mul_le_mul_of_nonneg_left (hs.trans (add_le_add_left cs _)) (by positivity)

theorem continuation {z : ℝ→State m} {τ T : ℝ} (hτ : 0<τ) (hT : 0≤T)
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z) :
    let d := ‖CircleActualTracking.gridR N (z 0)‖*sqrt (max 1 τ*T/2)
    |mean (z T)-mean (z 0)| ≤ d*(sqrt (squared (z 0))+d/2)/(π*sqrt m) := by
  intro d
  let Δ := z T-z 0
  let L := loss (residual (circleInput N) (circleLabel N) (1/sqrt m) (z 0))
  have hmax : 0≤max 1 τ := le_trans zero_le_one (le_max_left _ _)
  have sq : squared Δ ≤ max 1 τ*kinetic τ Δ := by
    rw [squared,kinetic,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    rw [←mul_div_assoc,le_div_iff₀ (rate_pos hτ p)]
    exact mul_le_mul_of_nonneg_left (show rate τ p≤max 1 τ by unfold rate; split <;> simp) (sq_nonneg _) |>.trans_eq (by ring)
  have hw := weighted_displacement hτ hT F
  have hl : 0≤loss (residual (circleInput N) (circleLabel N) (1/sqrt m) (z T)) := by unfold loss;positivity
  have wl : kinetic τ Δ ≤ T*L := by apply hw.trans; exact mul_le_mul_of_nonneg_left (sub_le_self _ hl) hT
  have hb := sq.trans (mul_le_mul_of_nonneg_left wl hmax)
  have dsq : d^2=max 1 τ*(T*L) := by
    dsimp [d]
    rw [mul_pow,sq_sqrt (by positivity),CircleActualTracking.gridR_sq]
    dsimp [L];ring
  have hdelta : 0≤squared Δ := by unfold squared; positivity
  have dp : 0≤d := mul_nonneg (norm_nonneg _) (sqrt_nonneg _)
  have dis : sqrt (squared Δ) ≤ d := (sqrt_le_iff).mpr ⟨dp,dsq.symm ▸ hb⟩
  have cap := mean_movement (z 0) (z T)
  apply cap.trans
  change (1/sqrt m)/π*(sqrt (squared Δ)*sqrt (squared (z 0))+squared Δ/2)≤_
  calc
    _ ≤ (1/sqrt m)/π*(d*sqrt (squared (z 0))+d^2/2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_right dis (sqrt_nonneg _)) (div_le_div_of_nonneg_right (dsq.symm ▸ hb) (by norm_num))
    _ = _ := by ring
end CircleContinuationBound
