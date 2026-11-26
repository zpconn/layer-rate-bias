module

public import CircleFiniteWidth
public import CirclePositiveSpectrum
import all CircleFiniteDynamics
import all CircleFiniteWidth
import all CircleGaussianTracking
import all CircleProjectedStep
import all CircleWidthTracking
import all CircleRateTrajectory
import all CircleKernelGD
import all CircleActualTracking
import all CircleTangentDrift
import all CircleDiscreteTracking
import all CircleSignedRow
import Mathlib.Tactic

/-! The full-matrix alternative to the signed-row estimate and the separately
discounted terminal constant mode of the trained nonlinear network. -/
@[expose] public section
noncomputable section
namespace CircleFiniteComparison
open Real CircleFlowPath CircleEscapeBridge CircleActualTracking CircleTangentDrift CircleDiscreteTracking
  CircleProjectedStep CircleGridSpectrum CircleSpectrum CircleFiniteDynamics CircleWidthTracking
  CircleRateTrajectory CircleKernelGD CircleFiniteConfidence
variable {N m : ℕ}

/-- Bounding the population and grid rows separately costs j_N+b h_N. -/
theorem full_row (n : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m) {z : Seed m}
    {g u : ℝ} (gram : ∀ i j : Fin (n+1), |gridGram 1 z (startGates z) i j-sampledMatrix 1 i j|≤g)
    (pop : ∀ i : Fin (n+1), |populationRow 1 z (startGates z) i-k0 1|≤u) (j : Fin (n+1)) :
    |CircleSignedRow.mixedRow (n+1) (weight 1 n) z z (CircleEscape.gridPoint _ j)|≤u+weight 1 n*g := by
  let N := n+1
  let b := weight 1 n
  let H (i : Fin N) := gridGram 1 z (startGates z) i j
  let K (i : Fin N) := sampledMatrix 1 i j
  let y := populationRow 1 z (startGates z) j
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have bp : 0≤b := (CircleGaussianTracking.weight_bounds n (by norm_num : (0:ℝ)≤1)).1
  have d : |((∑ i,H i)-(∑ i,K i))/(N:ℝ)|≤g := by
    rw [abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_pos np,div_le_iff₀ np,←Finset.sum_sub_distrib]
    exact ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => gram i j))).trans_eq (by simp [N];ring)
  have eq : b*((∑ i,K i)/N)=k0 1 := CirclePositiveSpectrum.weighted_column n hn odd 1 (by norm_num) j
  rw [CircleSignedRow.mixedRow_eq _ _ hm]
  change |y-b*((∑ i,H i)/N)|≤_
  rw [show y-b*((∑ i,H i)/N)=(y-k0 1)-b*(((∑ i,H i)-(∑ i,K i))/N) by rw [←eq];ring]
  apply (abs_sub ..).trans (add_le_add (pop j) ?_)
  rw [abs_mul,abs_of_nonneg bp]
  exact mul_le_mul_of_nonneg_left d bp

/-- Formula (5), with the instantaneous measured RMS retained in the
terminal term. The standing width assumption and confinement are the same
as for the signed-row telescope. -/
theorem full_matrix (n : ℕ) (hn : 3≤n+1) (hm : 0<m) (odd : Odd (n+1)) (z : Seed m)
    {η ρ R g u v k : ℝ} (hη : 0<η) (hc : η≤1) (hρ : 0≤ρ) (hr : ρ≤1) (hg : 0≤g) (hu : 0≤u)
    (hk : 0<k) (hk1 : k≤1) (G : Bounds (n+1) (weight 1 n) ρ R g v z)
    (pop : ∀ j : Fin (n+1), |populationRow 1 z (startGates z) j-k0 1|≤u)
    (cash : 2/sqrt m*R≤ρ*k) (gap : 36*ρ+g≤1/(π*((n+1:ℕ):ℝ))^2-k) (t : ℕ) :
    let N := n+1
    let b := weight 1 n
    |learnerMean η N z t-reference N m b z|≤b*rms η N z t+(u+b*g+(1+b)*36*ρ)*(R/k) := by
  intro N b
  have bp : 0≤b := (CircleGaussianTracking.weight_bounds n (by norm_num : (0:ℝ)≤1)).1
  have H : Bounds N b ρ R g (u+b*g) z :=
    ⟨G.residual,G.energy,G.gridMargin,G.angular,G.gram,fun j => full_row n hn odd hm G.gram pop j⟩
  exact ((CircleFiniteDynamics.trajectory hn hm odd z hη hc bp hρ hr hg (by positivity) hk hk1 H cash gap).1 t).2.2

/-- Residual forcing passed through the fast constant mode. -/
def discount (a q : ℝ) (t : ℕ) := ∑ j ∈ Finset.range t, a^(t-1-j)*q^j

private theorem discount_succ (a q : ℝ) (t : ℕ) :
    discount a q (t+1)=a*discount a q t+q^t := by
  simp only [discount,Finset.sum_range_succ,Nat.add_sub_cancel,Nat.sub_self,pow_zero,one_mul,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have lt := Finset.mem_range.mp hi
  rw [show t-i=t-1-i+1 by omega,pow_succ']
  ring

/-- Formula for the separately discounted terminal projection. It also
bounds its leakage by b e R/γ, independently of the slowest mode. -/
theorem constant_mode [NeZero N] (hn : 3≤N) (hm : 0<m) (odd : Odd N) (z : Seed m)
    {η b ρ R g v k : ℝ} (hη : 0<η) (hc : η≤1) (hb : 0≤b) (hρ : 0≤ρ) (hr : ρ≤1)
    (hg : 0≤g) (hk : 0<k) (hk1 : k≤1) (G : Bounds N b ρ R g v z)
    (cash : 2/sqrt m*R≤ρ*k) (gap : 36*ρ+g≤1/(π*(N:ℝ))^2-k) (T : ℕ) :
    let a := 1-η*gamma N
    let q := 1-η*k
    let e := 36*ρ+g
    let leak := η*b*e*R*discount a q T
    |rowOp (fun _ : Fin N => b) (gridR N (iterateAt N η z T))|≤b*R*a^T+leak ∧ leak≤b*e*R/gamma N := by
  intro a q e leak
  let w := iterateAt N η z
  let p := rowOp (fun _ : Fin N => b)
  let r := fun t => gridR N (w t)
  let S := η*b*e*R
  have path := CircleFiniteDynamics.bootstrap hn hm odd z hη hc hρ hr hg hk hk1 G cash gap
  have rp := (norm_nonneg _).trans G.residual
  have gp : 0<gamma N := (show 0<(3:ℝ)/π^2 by positivity).trans_le (gamma_bounds (N:=N)).1
  have ap : 0≤a := sub_nonneg.mpr ((mul_le_of_le_one_left gp.le hc).trans gamma_bounds.2)
  have qp : 0≤q := sub_nonneg.mpr ((mul_le_of_le_one_left hk.le hc).trans hk1)
  have ep : 0≤e := by dsimp [e];positivity
  have one : q≤1 := sub_le_self _ (mul_nonneg hη.le hk.le)
  have pbound (x : EuclideanSpace ℝ (Fin N)) : |p x|≤b*‖x‖ := (p.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (rowOp_norm (by omega : 0<N) hb (fun _ => (abs_of_nonneg hb).le)) (norm_nonneg _))
  have bound (t : ℕ) : |p (r t)|≤b*R*a^t+S*discount a q t := by
    induction t with
    | zero => simpa only [r,w,iterateAt,pow_zero,mul_one,discount,Finset.range_zero,Finset.sum_empty,mul_zero,add_zero]
        using (pbound _).trans (mul_le_mul_of_nonneg_left G.residual hb)
    | succ t ih =>
      let U := r t-η • gramOp (sampledMatrix 1) (r t)
      have defect : ‖r (t+1)-U‖≤η*e*‖r t‖ := by
        apply grid_defect hη.le (by omega : 0<N) _ ep
        intro i s hs j
        exact (abs_sub_le _ _ _).trans (add_le_add
          (CircleFiniteDynamics.grid_motion hm hρ hr G (path t).2.1 s ((path t).2.2 s hs) i j) (G.gram i j))
      have d := (pbound (r (t+1)-U)).trans (mul_le_mul_of_nonneg_left defect hb)
      have eq := gramOp_eigenrow (N:=N) 1 b (by norm_num) (by norm_num) (r t)
      change p (gramOp (sampledMatrix 1) (r t)) = gamma N*p (r t) at eq
      have peq : p U=a*p (r t) := by dsimp only [U,a];rw [map_sub,map_smul,smul_eq_mul,eq];ring
      rw [map_sub,peq] at d
      have tri := abs_sub_le (p (r (t+1))) (a*p (r t)) 0
      simp only [sub_zero,abs_mul,abs_of_nonneg ap] at tri
      have size := mul_le_mul_of_nonneg_left (path t).1 (mul_nonneg hb (mul_nonneg hη.le ep))
      change b*(η*e)*‖r t‖≤b*(η*e)*(q^t*R) at size
      rw [discount_succ,pow_succ]
      exact tri.trans ((add_le_add (d.trans ((by ring : b*(η*e*‖r t‖)=b*(η*e)*‖r t‖).le.trans size))
        (mul_le_mul_of_nonneg_left ih ap)).trans_eq (by dsimp only [S];ring))
  have mass (t : ℕ) : η*gamma N*discount a q t≤1 := by
    induction t with
    | zero => simp [discount]
    | succ t ih =>
      rw [discount_succ]
      have p := pow_le_one₀ qp one (n:=t)
      nlinarith only [mul_le_mul_of_nonneg_left ih ap,mul_le_mul_of_nonneg_left p (mul_nonneg hη.le gp.le),
        show a=1-η*gamma N from rfl]
  refine ⟨bound T,(le_div_iff₀ gp).mpr ?_⟩
  have h := mul_le_mul_of_nonneg_right (mass T) (mul_nonneg (mul_nonneg hb ep) rp)
  dsimp only [leak]
  linarith only [h]

end CircleFiniteComparison
