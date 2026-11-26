module
public import CircleActualTracking
import all CircleActualTracking
import all CircleTangentDrift
import all CircleFlowPath
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-! The Euclidean speed of each neuron in an actual unit-rate flow with arbitrary admissible gates. -/
@[expose] public section
noncomputable section
namespace CircleActiveSpeed
open Real CircleActualTracking CircleTangentDrift CircleFlowPath
variable {N m : ℕ}
abbrev block (z : State m) (j : Fin m) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun k => z (j,k))

private theorem row_length (z : State m) (g : Fin N→Fin m→ℝ) (hg : gridGates z g)
    (i : Fin N) (j : Fin m) :
    length (row (1/sqrt m) z (circleInput N i) (g i)) j ≤
      (1/sqrt m)*length z j := by
  let x := circleInput N i
  let w := pre z j x
  have hx : x.1^2+x.2^2 ≤ 1 := grid_unit i
  have proj : w^2 ≤ z (j,1)^2+z (j,2)^2 := by
    dsimp [w,pre]
    nlinarith [sq_nonneg (x.1*z (j,2)-x.2*z (j,1)),
      mul_nonneg (sub_nonneg.mpr hx) (add_nonneg (sq_nonneg (z (j,1))) (sq_nonneg (z (j,2))))]
  have gate := hg i j
  have gs : (g i j)^2 ≤ 1 := by nlinarith [mul_nonneg gate.1 (sub_nonneg.mpr gate.2.1)]
  have feat : (max w 0)^2 ≤ z (j,1)^2+z (j,2)^2 := by
    rcases le_total 0 w with h|h
    · rwa [max_eq_left h]
    · rw [max_eq_right h,zero_pow (by decide : 2 ≠ 0)]; exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs : (max w 0)^2 + (z (j,0)*g i j*x.1)^2+
      (z (j,0)*g i j*x.2)^2 ≤ z (j,0)^2+z (j,1)^2+z (j,2)^2 := by
    have a := mul_le_mul_of_nonneg_left hx (sq_nonneg (z (j,0)*g i j))
    have b := mul_le_mul_of_nonneg_left gs (sq_nonneg (z (j,0)))
    nlinarith only [a,b,feat]
  apply (sq_le_sq₀ (sqrt_nonneg _) (mul_nonneg (by positivity) (sqrt_nonneg _))).mp
  change length _ j ^ 2 ≤ ((1/sqrt m)*length z j)^2
  rw [length_sq,mul_pow,length_sq]
  change ((1/sqrt m)*max w 0)^2+((1/sqrt m)*(z (j,0)*g i j*x.1))^2+
    ((1/sqrt m)*(z (j,0)*g i j*x.2))^2 ≤ _
  convert mul_le_mul_of_nonneg_left hs (sq_nonneg (1/sqrt (m:ℝ))) using 1; ring

/-- For the exact grid residual, the Euclidean norm of a neuron velocity block
is controlled with constant one including at a ReLU kink. -/
theorem velocity_le (hn : 0<N) (z : State m) (g : Fin N→Fin m→ℝ) (hg : gridGates z g)
    (j : Fin m) :
    length (velocity 1 (fun i => row (1/sqrt m) z (circleInput N i) (g i))
      (residual (circleInput N) (circleLabel N) (1/sqrt m) z)) j ≤
      (‖gridR N z‖ / sqrt m)*length z j := by
  let a := residual (circleInput N) (circleLabel N) (1/sqrt m) z
  let J (i : Fin N) := row (1/sqrt m) z (circleInput N i) (g i)
  have form : block (velocity 1 J a) j =
      (-(1/(N:ℝ))) • ∑ i, a i • block (J i) j := by
    ext k
    simp [block,velocity,rate,gradient,J,a,PiLp.smul_apply]
  have mean : (∑ i, |a i|)/(N:ℝ) ≤ ‖gridR N z‖ := by
    have hp : (0:ℝ)<N := by exact_mod_cast hn
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [gridR,rmsCoordinates_norm_sq,div_pow]
    change (∑ i, |a i|)^2 / (N:ℝ)^2 ≤ (∑ i, a i^2)/(N:ℝ)
    rw [div_le_div_iff₀ (sq_pos_of_pos hp) hp]
    have h := sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun i => |a i|)
    simp only [Finset.card_univ,Fintype.card_fin,sq_abs] at h
    nlinarith only [mul_le_mul_of_nonneg_right h hp.le]
  have nn : 0≤(1/sqrt (m:ℝ))*length z j := mul_nonneg (by positivity) (sqrt_nonneg _)
  rw [CircleActualTracking.length_entity]
  change ‖block (velocity 1 J a) j‖ ≤ _
  rw [form,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (1/(N:ℝ)) * ∑ i, ‖a i • block (J i) j‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (1/(N:ℝ)) * ∑ i, |a i| *((1/sqrt m)*length z j) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (CircleActualTracking.length_entity (J i) j ▸ row_length z g hg i j) (abs_nonneg _)
    _ = ((∑ i, |a i|)/(N:ℝ))*((1/sqrt m)*length z j) := by rw [←Finset.sum_mul];ring
    _ ≤ ‖gridR N z‖*((1/sqrt m)*length z j) := mul_le_mul_of_nonneg_right mean nn
    _ = _ := by ring

/-- Every scalar projection onto a test vector in the unit ball has the same bound. -/
theorem projection_le (hn : 0<N) (z : State m) (g : Fin N→Fin m→ℝ) (hg : gridGates z g)
    (j : Fin m) (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖≤1) :
    |inner ℝ v (block (velocity 1 (fun i => row (1/sqrt m) z (circleInput N i) (g i))
      (residual (circleInput N) (circleLabel N) (1/sqrt m) z)) j)|≤
        (‖gridR N z‖ / sqrt m)*length z j := by
  have h := velocity_le hn z g hg j
  rw [CircleActualTracking.length_entity] at h
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hv).trans h)

end CircleActiveSpeed
