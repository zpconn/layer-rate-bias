module

public import CircleWeightedStep
public import CircleGridMargin
import all CircleWeightedStep
import all CircleFlowPath
import all CircleTangentDrift
import all CircleGridMargin
import all CircleSynchronizedEscape
import all CircleEscape
import Mathlib.Tactic

/-! The axial symmetric state and the two half-grid averages in its exact GD update. -/
@[expose] public section
noncomputable section
namespace CirclePairedGDGeometry

open Real CircleFlowPath CircleWeightedStep CircleTangentDrift

def center (m : ℕ) (a w : ℝ) : State m := fun p => ![a,w,0] p.2

@[simp] theorem center_zero (m : ℕ) (a w : ℝ) (j : Fin m) : center m a w (j,0) = a := rfl
@[simp] theorem center_one (m : ℕ) (a w : ℝ) (j : Fin m) : center m a w (j,1) = w := rfl
@[simp] theorem center_two (m : ℕ) (a w : ℝ) (j : Fin m) : center m a w (j,2) = 0 := rfl

@[simp] theorem pre_center (m : ℕ) (a w : ℝ) (j : Fin m) (x : ℝ × ℝ) :
    pre (center m a w) j x = w*x.1 := by simp [pre, mul_comm]

def h (N : ℕ) (s : ℝ) (i : Fin N) := max (s*(circleInput N i).1) 0

def q (N : ℕ) (s : ℝ) := (∑ i, h N s i ^ 2) / N

def b (N : ℕ) (s : ℝ) := (∑ i, circleLabel N i * h N s i) / N

theorem q_lower (N : ℕ) (hN : 3 ≤ N) (s : ℝ) (hs : |s|=1) : 1/16 ≤ q N s := by
  have a := (CircleGridMargin.grid_relu_mean_bounds N hN (s:ℂ)).2
  have he (i : Fin N) : CircleEscape.feature (s:ℂ) (CircleEscape.gridPoint N i) = h N s i := by
    simp [CircleEscape.feature, Complex.inner, h, circleInput, mul_comm]
  simpa only [he,q,Complex.norm_real,Real.norm_eq_abs,hs,one_pow] using a

theorem b_nonneg (N : ℕ) (s : ℝ) : 0 ≤ b N s := by
  unfold b
  refine div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg ?_ (le_max_right ..)) (Nat.cast_nonneg _)
  change 0 ≤ 1 + cos _
  linarith [neg_one_le_cos ((2*π/N)*(i:ℕ))]

theorem b_upper (N : ℕ) (s : ℝ) (hs : |s| = 1) : b N s ≤ 2 := by
  by_cases hn : N=0
  · simp [b,hn]
  have np : (0:ℝ) < N := by positivity
  apply (div_le_iff₀ np).2
  calc
    ∑ i : Fin N, circleLabel N i * h N s i ≤ ∑ _i : Fin N, (2:ℝ) := by
      apply Finset.sum_le_sum; intro i _
      have u : |(circleInput N i).1|≤1 := abs_cos_le_one _
      have l : circleLabel N i≤2 := by unfold circleLabel;linarith [(le_abs_self _).trans u]
      have hh : h N s i ≤ 1 := max_le ((le_abs_self _).trans (by simpa only [abs_mul,hs,one_mul] using u)) (by norm_num)
      exact (mul_le_mul l hh (le_max_right ..) (by norm_num)).trans_eq (by ring)
    _ = 2*(N:ℝ) := by simp [mul_comm]

/-- For odd N, the grid avoids the two zeros of the axial preactivation.
Multiplying the angle by N makes the sine of its complementary angle have
unit magnitude, while the triangle inequality costs at most N. -/
theorem gate_clearance (N : ℕ) (hN : 3 ≤ N) (odd : Odd N) (i : Fin N) :
    1/(N:ℝ) ≤ |(circleInput N i).1| := by
  let θ := 2*π/(N:ℝ)*(i:ℕ)
  have np : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have id : (N:ℝ)*(π/2-θ) = (N:ℝ)*π/2 - (i.val:ℝ)*(2*π) := by dsimp [θ];field_simp
  obtain ⟨k,hk⟩ := odd
  have halves : (N:ℝ)*π/2 = π/2+(k:ℝ)*π := by rw [hk]; push_cast; ring
  have unitSin : |sin ((N:ℝ)*(π/2-θ))| = 1 := by
    rw [id,sin_sub_nat_mul_two_pi,halves,sin_add_nat_mul_pi,sin_pi_div_two,mul_one,abs_pow]
    norm_num
  have a := abs_sin_sum_le (Finset.univ : Finset (Fin N)) (fun _ => π/2-θ)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,unitSin,sin_pi_div_two_sub] at a
  apply (div_le_iff₀ np).2
  change 1 ≤ |cos θ| * N
  simpa only [mul_comm] using a

theorem center_output (m : ℕ) (hm : 0<m) (a w : ℝ) (x : ℝ × ℝ) :
    output (1/sqrt m) (center m a w) x = sqrt m * a * max (w*x.1) 0 := by
  have hp : (0:ℝ)<m := by exact_mod_cast hm
  have sp := sqrt_pos.mpr hp
  simp only [output,center_zero,pre_center,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  linear_combination -(a * max (w * x.1) 0) * Real.sq_sqrt hp.le


private theorem scaled_pre (N : ℕ) (s W : ℝ) (hW : 0<W) (i : Fin N) :
    max ((s*W)*(circleInput N i).1) 0 = W*h N s i := by
  let x := (circleInput N i).1
  change max ((s*W)*x) 0 = W*max (s*x) 0
  rw [show s*W*x = W*(s*x) by ring]
  by_cases p : 0≤s*x
  · rw [max_eq_left p,max_eq_left (mul_nonneg hW.le p)]
  · rw [max_eq_right (le_of_not_ge p),max_eq_right (mul_nonpos_of_nonneg_of_nonpos hW.le (le_of_not_ge p)),mul_zero]

private theorem center_gate_proj (N : ℕ) (s W : ℝ) (hs : |s|=1) (hW : 0<W) (i : Fin N) :
    actualGate ((s*W)*(circleInput N i).1)*(circleInput N i).1 = s*h N s i := by
  let x := (circleInput N i).1
  change actualGate ((s*W)*x)*x = s*max (s*x) 0
  have sq : s^2=1 := by rw [←sq_abs,hs]; norm_num
  rw [show s*W*x = W*(s*x) by ring]
  by_cases p : 0<s*x
  · simp only [actualGate,ite_eq_left (mul_pos hW p),one_mul,max_eq_left p.le]
    linear_combination -x*sq
  · simp only [actualGate,ite_eq_right (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hW.le (le_of_not_gt p))),
      zero_mul,max_eq_right (le_of_not_gt p),mul_zero]

/-- The generated network's simultaneous update leaves the horizontal axis
invariant. Both parameters are updated from the old weights and residual. -/
theorem center_segment (N m : ℕ) (hN : 0 < N) (hm : 0 < m)
    (η τ σ s A W : ℝ) (hσ : |σ| = 1) (hs : |s| = 1) (hW : 0 < W) :
    segment τ N (center m (σ*A) (s*W)) η =
      center m (σ*A - η*(σ*q N s*A*W^2-b N s*W/sqrt m))
               (s*W - η*τ*s*(q N s*A^2*W-σ*b N s*A/sqrt m)) := by
  let _ : NeZero N := ⟨hN.ne'⟩
  have np : (0:ℝ)<N := by exact_mod_cast hN
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have sp := sqrt_pos.mpr mp
  let r (i : Fin N) := sqrt m*(σ*A)*W*h N s i - circleLabel N i
  let g (i : Fin N) := actualGate ((s*W)*(circleInput N i).1)
  have resid (i : Fin N) :
      residual (circleInput N) (circleLabel N) (1/sqrt m) (center m (σ*A) (s*W)) i = r i := by
    rw [CircleFlowPath.residual,center_output m hm,scaled_pre N s W hW]
    dsimp only [r]
    ring
  have drive : (1/((N:ℝ)*sqrt m))*∑ i, r i*h N s i =
      σ*A*W*q N s-b N s/sqrt m := by
    have splitRow (i : Fin N) : r i*h N s i =
        (sqrt m*(σ*A)*W)*h N s i^2-circleLabel N i*h N s i := by dsimp [r];ring
    simp_rw [splitRow]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,b,q]
    field_simp
  have flux0 (j : Fin m) (i : Fin N) :
      r i * row (1/sqrt m) (center m (σ*A) (s*W)) (circleInput N i)
          (startGates (center m (σ*A) (s*W)) i) (j,0)
        = (W/sqrt m) * (r i*h N s i) := by
    change r i * ((1/sqrt m)*max (pre _ j _) 0) = _
    rw [pre_center,scaled_pre N s W hW]
    ring
  have flux1 (j : Fin m) (i : Fin N) :
      r i * row (1/sqrt m) (center m (σ*A) (s*W)) (circleInput N i)
          (startGates (center m (σ*A) (s*W)) i) (j,1)
        = (σ*A*s/sqrt m) * (r i*h N s i) := by
    change r i*((1/sqrt m)*((σ*A)*actualGate (pre _ j _)*(circleInput N i).1)) = _
    rw [pre_center,mul_assoc (σ*A),center_gate_proj N s W hs hW]
    ring
  have flux2 (j : Fin m) (i : Fin N) :
      r i * row (1/sqrt m) (center m (σ*A) (s*W)) (circleInput N i)
          (startGates (center m (σ*A) (s*W)) i) (j,2)
        = ((σ*A)/sqrt m)*((r i*g i)*(circleInput N i).2) := by
    change r i*((1/sqrt m)*((σ*A)*actualGate (pre _ j _)*(circleInput N i).2)) = _
    rw [pre_center]; dsimp only [g];ring
  have evenG (i : Fin N) : r (-i)*g (-i) = r i*g i := by
    have cx : (circleInput N (-i)).1=(circleInput N i).1 := (CircleSynchronizedEscape.grid_reflect N i).1
    simp only [r,g,h,circleLabel,cx]
  have orth : ∑ i, (r i*g i)*(circleInput N i).2 = 0 :=
    CircleSynchronizedEscape.sum_imag_zero N _ evenG
  have sqσ : σ^2=1 := by rw [←sq_abs,hσ]; norm_num
  funext p
  obtain ⟨j,k⟩ := p
  fin_cases k
  · change CircleWeightedStep.segment _ _ _ _ (j,(0:Fin 3)) = center _ _ _ (j,0)
    simp only [CircleWeightedStep.segment,direction,velocity,rate,ite_true,neg_mul,one_mul,gradient,resid,flux0,
      ←Finset.mul_sum,center_zero]
    linear_combination -η*W*drive
  · change CircleWeightedStep.segment _ _ _ _ (j,(1:Fin 3)) = center _ _ _ (j,1)
    simp only [CircleWeightedStep.segment,direction,velocity,rate,show (1:Fin 3)≠0 by decide,ite_false,gradient,resid,flux1,
      ←Finset.mul_sum,center_one]
    linear_combination -η*τ*σ*A*s*drive - η*τ*s*A^2*W*q N s*sqσ
  · change CircleWeightedStep.segment _ _ _ _ (j,(2:Fin 3)) = center _ _ _ (j,2)
    simp only [CircleWeightedStep.segment,direction,velocity,rate,show (2:Fin 3)≠0 by decide,ite_false,gradient,resid,flux2,
      ←Finset.mul_sum,orth,center_two,mul_zero,add_zero]

end CirclePairedGDGeometry
