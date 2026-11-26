module

public import CircleWidthUpper
public import CircleWidthAsymptotics
import all CircleWidthUpper
import all CircleShortGDTails
import all CircleWidthMoment
import Mathlib.Tactic

/-! The sufficient leading width exponent for unrestricted circle GD. -/
@[expose] public section
noncomputable section
namespace CircleWidthThreshold
open Real MeasureTheory Filter Set CircleWidthAsymptotics CircleWidthUpper CircleWidthTracking CircleWidthMoment
open scoped Topology

private def u (a x : ℝ) := exp (-a*x)
private def r (a x : ℝ) := exp (-(a/2)*x)

private theorem scales (m T : ℕ) (a x : ℝ) (mg : (m:ℝ)=exp x) (xp : 0≤x) (ha : 0≤a) (hc : a≤1/2)
    (budget : 132*T*r a x≤1) :
    FitsBudget m T (r a x) (u a x) ∧
    errorBound m T (r a x) (u a x) ≤ 1188*T*exp ((1/2-3*a/2)*x) := by
  have sp : sqrt (m:ℝ)=exp (x/2) := by
    rw [mg,show exp x=(exp (x/2))^2 by rw [← exp_nat_mul]; congr 1;ring,sqrt_sq (exp_pos _).le]
  have rp : 0≤r a x := exp_nonneg _
  have up : 0≤u a x := exp_nonneg _
  have ur : u a x≤r a x := exp_le_exp.mpr (by nlinarith [mul_nonneg ha xp])
  have r1 : r a x≤1 := exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha xp])
  have ue : r a x*r a x=u a x := by rw [r,← exp_add,u];congr 1;ring
  have aone : 1≤exp (x/2)*u a x := by
    rw [u,← exp_add];apply one_le_exp_iff.mpr; nlinarith [mul_nonneg (sub_nonneg.mpr hc) xp]
  have R : 2+sqrt m*u a x ≤ 3*(sqrt m*u a x) := by rw [sp];linarith
  have drift : (T:ℝ)*(16/sqrt m*(2+sqrt m*u a x))≤r a x := by
    have hp : 0<sqrt (m:ℝ) := sp ▸ exp_pos _
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left R (show 0≤16/sqrt (m:ℝ) by positivity)) (Nat.cast_nonneg T)
    have eq : (T:ℝ)*(16/sqrt m*(3*(sqrt m*u a x)))=48*T*u a x := by field_simp;ring
    apply h.trans;rw [eq,←ue]
    nlinarith only [mul_le_mul_of_nonneg_right budget rp,mul_nonneg (Nat.cast_nonneg T) (mul_nonneg rp rp)]
  have e : 2*(30*r a x+3*u a x)≤66*r a x := by linarith
  refine ⟨⟨rp,r1,up,ur.trans r1,drift,?_⟩,?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_left e (Nat.cast_nonneg T),budget]
  · unfold errorBound
    have h := mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left e (by norm_num : (0:ℝ)≤6))
      R (by positivity) (by positivity)) (Nat.cast_nonneg T)
    apply h.trans_eq
    rw [sp,r,u]
    rw [show 6*(66*exp (-(a/2)*x))*(3*(exp (x/2)*exp (-a*x)))*(T:ℝ) =
      1188*T*(exp (-(a/2)*x)*exp (x/2)*exp (-a*x)) by ring,←exp_add,←exp_add]
    congr 2; ring

private theorem failure_exp (N m : ℕ) (a x D : ℝ) (mg : (m:ℝ)=exp x) (nx : (N:ℝ)≤exp (D*x))
    (Dx : 0≤D*x) (one : 1≤x) :
    failureBound N m (u a x) ≤ exp ((4+2*D)*x-exp ((1-2*a)*x)/36864) := by
  have ge : 1≤exp (D*x) := one_le_exp_iff.mpr Dx
  have nn : (N:ℝ)+1≤2*exp (D*x) := by linarith
  have e32 : (32:ℝ)≤exp (4*x) := by
    have low := Real.exp_one_gt_d9
    have bound := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤(27/10)) (show 27/10≤exp 1 by linarith) 4
    rw [←exp_nat_mul] at bound; norm_num at bound
    exact (by linarith : 32≤exp 4).trans (exp_le_exp.mpr (by linarith))
  have μ : (m:ℝ)*(u a x)^2=exp ((1-2*a)*x) := by
    rw [mg,u,←exp_nat_mul,←exp_add];congr 1;ring
  rw [failureBound,neg_mul,μ,exp_sub]
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) nn 2)
    (by norm_num : (0:ℝ)≤8)) (exp_nonneg _)).trans
  rw [show 8*(2*exp (D*x))^2=32*(exp (D*x))^2 by ring,←exp_nat_mul,neg_div,exp_neg,←div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ (exp_nonneg _)
  exact (mul_le_mul_of_nonneg_right e32 (exp_nonneg _)).trans_eq (by rw [←exp_add]; congr 1;ring)

/-- Logarithm of the all-seed fourth envelope under the single width inequality. -/
private theorem fourth_exp (m T : ℕ) (b x : ℝ) (mx : (m:ℝ)=exp x) (one : 1≤x)
    (bp : 0≤b) (bc : b≤1) (pwr : (3:ℝ)^T≤exp (b*x)) :
    CircleShortGDTails.fourthBound m T ≤ exp (160*x*exp (b*x)) := by
  let p := CircleShortGDTails.momentDegree T
  have pe : (p:ℝ)≤8*exp (b*x) := by
    dsimp [p,CircleShortGDTails.momentDegree];push_cast;linarith
  have bx : 0≤b*x := mul_nonneg bp (by linarith)
  have bx' : b*x≤x := by nlinarith [mul_le_mul_of_nonneg_right bc (show 0≤x by linarith)]
  have ge : 1≤exp (b*x) := one_le_exp_iff.mpr bx
  have xe : 1≤exp x := one_le_exp_iff.mpr (by linarith)
  have eight : (8:ℝ)≤exp (3*x) := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) Real.exp_one_gt_two.le 3
    rw [←exp_nat_mul] at h; norm_num at h
    exact h.trans (exp_le_exp.mpr (by linarith))
  have pre : (5:ℝ)*m≤exp (4*x) ∧ (6:ℝ)*m≤exp (4*x) := by
    rw [mx,show 4*x=3*x+x by ring,exp_add]
    constructor <;> exact mul_le_mul_of_nonneg_right (by linarith) (exp_nonneg _)
  have c128 : (128:ℝ)≤exp (7*x) := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) Real.exp_one_gt_two.le 7
    rw [←exp_nat_mul] at h; norm_num at h
    exact h.trans (exp_le_exp.mpr (by linarith))
  have base : 4*(1+3*(m:ℝ))*(p:ℝ)≤exp (9*x) := by
    have w : 4*(1+3*(m:ℝ))≤16*exp x := by rw [mx];linarith
    have e := mul_le_mul w pe (Nat.cast_nonneg p) (by positivity)
    apply e.trans
    rw [show 16*exp x*(8*exp (b*x))=128*(exp x*exp (b*x)) by ring,←exp_add]
    apply (mul_le_mul_of_nonneg_right c128 (exp_nonneg _)).trans
    rw [←exp_add];apply exp_le_exp.mpr;linarith
  change (5*(m:ℝ))^4*(4*(1+3*(m:ℝ))*(p:ℝ))^p*exp 9*(6*m) ≤ _
  have e := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul
    (pow_le_pow_left₀ (by positivity) pre.1 4) (pow_le_pow_left₀ (by positivity) base p) (by positivity) (by positivity))
    (exp_nonneg 9)) pre.2 (by positivity) (by positivity)
  apply e.trans
  rw [←exp_nat_mul,←exp_nat_mul,←exp_add,←exp_add,←exp_add]
  apply exp_le_exp.mpr
  push_cast
  nlinarith only [mul_le_mul_of_nonneg_right pe (show 0≤x by linarith),
    mul_le_mul_of_nonneg_left ge (show 0≤x by linarith),one]


/-- For any deterministic admissible step (even one varying with the design),
the actual same-seed stopped-reference MSE tends to zero for every width rate
strictly above log 3 and every grid size of at most exponential growth. -/
theorem convergence_above_log_three (n m T : ℕ → ℕ) (η : ℕ → ℝ)
    (grow : Tendsto T atTop atTop)
    (valid : ∀ᶠ j in atTop, 3≤n j+1 ∧ Odd (n j+1) ∧ 0<m j ∧ 0≤η j ∧ η j≤1)
    {c K : ℝ} (hc : log 3<c) (grid : ∀ᶠ j in atTop, log ((n j:ℝ)+1)≤K*(T j:ℝ))
    (width : ∀ᶠ j in atTop, c*(T j:ℝ)≤log (m j)) :
    Tendsto (fun j => ∫ z, (rawError (n j+1) (m j) (T j) (η j)
      (stoppedCoefficient (n j) (T j) (η j)) z)^2 ∂CircleEscapeBridge.seedLaw (m j)) atTop (𝓝 0) := by
  let x := fun j => log (m j)
  let b := log 3/c
  let a := (1-b)/4
  let D := |K|/c
  let Q := 4+2*D
  have lp : 0<log (3:ℝ) := log_pos (by norm_num)
  have cp := lp.trans hc
  have bp : 0<b := div_pos lp cp
  have bc : b<1 := (div_lt_one cp).mpr hc
  have ap : 0<a := by dsimp [a];linarith
  have ac : a≤1/2 := by dsimp [a];linarith
  have qg : b<1-2*a := by dsimp [a];linarith
  have qp : 0<1-2*a := bp.trans qg
  have Dp : 0≤D := div_nonneg (abs_nonneg _) cp.le
  have Qp : 0≤Q := by dsimp [Q];linarith
  have tg := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow
  have xg : Tendsto x atTop atTop := tendsto_atTop_mono' atTop width (tg.const_mul_atTop cp)
  have tx : ∀ᶠ j in atTop, (T j:ℝ)≤x j/c := width.mono fun j h =>
    (le_div_iff₀ cp).mpr (by change c*(T j:ℝ)≤x j at h;linarith)
  have sm (l : ℝ) (hp : 0<l) (C : ℝ) :
      Tendsto (fun j => C*x j*exp (-l*x j)) atTop (𝓝 0) := by
    simpa [mul_assoc,Function.comp_def] using ((linear_times_decay hp).comp xg).const_mul C
  have budget (l : ℝ) (h : 0<l) : ∀ᶠ j in atTop, 132*(T j:ℝ)*r l (x j)≤1 := by
    have ev := (sm (l/2) (by positivity) (132/c)).eventually_le_const (by norm_num : (0:ℝ)<1)
    filter_upwards [ev,tx] with j he ht
    apply le_trans _ he
    apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
    have ge := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤132)
    linarith only [ge,show 132*(x j/c)=(132/c)*x j by ring]
  let front j := (1188/c)*x j*exp (-(1/16)*x j)
  let middle j := exp ((2+Q)*x j-exp ((1/4)*x j)/36864)
  let tail j := sqrt (exp ((160+Q)*x j*exp (b*x j)-exp ((1-2*a)*x j)/36864))
  have f0 : Tendsto front atTop (𝓝 0) := sm _ (by norm_num) _
  have m0 : Tendsto middle atTop (𝓝 0) := (simple_cost_decay (by norm_num : (0:ℝ)<1/4) (2+Q)).comp xg
  have v0 : Tendsto tail atTop (𝓝 0) := by
    simpa only [tail, Function.comp_apply, sqrt_zero] using (((cost_decay qp qg (160+Q)).comp xg).sqrt)
  have re := ((f0.pow 2).add m0).add v0
  simp only [zero_pow (by decide : 2≠0),zero_add] at re
  apply squeeze_zero' (Eventually.of_forall fun j => integral_nonneg fun _ => sq_nonneg _) _ re
  have smC := (sm (1/2) (by norm_num) (1188/c)).eventually_le_const (by norm_num : (0:ℝ)<1)
  filter_upwards [valid,grid,tx,budget a ap,budget (3/8) (by norm_num),xg.eventually_ge_atTop 1,smC] with j v g t h1 h2 x1 hs
  have mx : (m j:ℝ)=exp (x j) := (exp_log (Nat.cast_pos.mpr v.2.2.1)).symm
  have xp : 0≤x j := by linarith
  have nn : ((n j+1:ℕ):ℝ)≤exp (D*x j) := by
    rw [Nat.cast_add_one,← log_le_iff_le_exp (by positivity)]
    apply g.trans
    have h := (mul_le_mul_of_nonneg_right (le_abs_self K) (Nat.cast_nonneg (T j))).trans (mul_le_mul_of_nonneg_left t (abs_nonneg K))
    exact h.trans_eq (by dsimp [D];ring)
  have three : (3:ℝ)^(T j)≤exp (b*x j) := by
    conv_lhs => rw [←exp_log (by norm_num : 0<(3:ℝ))]
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right t lp.le
    dsimp [b]
    linarith only [h,show x j/c*log 3=log 3/c*x j by ring]
  have fin := mse_bound (n j) (m j) (T j) v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2
    (scales _ _ (3/8) _ mx xp (by norm_num) (by norm_num) h2).1 (scales _ _ a _ mx xp ap.le ac h1).1
  apply fin.trans
  apply add_le_add (add_le_add ?_ ?_) ?_
  · have h := (scales _ _ (3/8) _ mx xp (by norm_num) (by norm_num) h2).2
    norm_num at h
    apply pow_le_pow_left₀ (by unfold errorBound; exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by dsimp [r,u];positivity)) (by dsimp [u];positivity)) (Nat.cast_nonneg _))
    apply h.trans
    dsimp [front]
    rw [neg_mul]
    apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
    exact (mul_le_mul_of_nonneg_left t (by norm_num : (0:ℝ)≤1188)).trans_eq (by ring)
  · have h := (scales _ _ a _ mx xp ap.le ac h1).2
    have hE : errorBound (m j) (T j) (r a (x j)) (u a (x j))≤exp (x j) := by
      apply h.trans
      have split : exp (x j) = exp (x j/2)*exp (x j/2) := by rw [←exp_add];congr 1;ring
      have bound := mul_le_mul_of_nonneg_right hs (exp_nonneg (x j/2))
      have can : (1188/c)*x j*exp (-(1/2)*x j)*exp (x j/2)=(1188/c)*x j := by
        rw [mul_assoc,←exp_add,show -(1/2)*x j+x j/2=0 by ring,exp_zero,mul_one]
      rw [can,one_mul] at bound
      rw [split]
      apply mul_le_mul _ (exp_le_exp.mpr (by nlinarith only [mul_nonneg ap.le xp])) (exp_nonneg _) (exp_nonneg _)
      exact ((mul_le_mul_of_nonneg_left t (by norm_num : (0:ℝ)≤1188)).trans_eq (by ring : 1188*(x j/c)=1188/c*x j)).trans bound
    have hf := failure_exp (n j+1) (m j) (3/8) (x j) D mx nn (mul_nonneg Dp xp) x1
    have errp : 0≤errorBound (m j) (T j) (r a (x j)) (u a (x j)) := by unfold errorBound r u;positivity
    have h := mul_le_mul (pow_le_pow_left₀ errp hE 2) hf (by unfold failureBound; positivity) (sq_nonneg _)
    apply h.trans_eq
    dsimp [middle,Q];rw [←exp_nat_mul,←exp_add];congr 1;ring_nf
  · have four := fourth_exp (m j) (T j) b (x j) mx x1 bp.le bc.le three
    have ff := failure_exp (n j+1) (m j) a (x j) D mx nn (mul_nonneg Dp xp) x1
    rw [← sqrt_mul (by unfold CircleShortGDTails.fourthBound; positivity)]
    apply sqrt_le_sqrt
    apply (mul_le_mul four ff (by unfold failureBound;positivity) (exp_nonneg _)).trans
    rw [←exp_add]
    apply exp_le_exp.mpr
    have xe : 1≤exp (b*x j) := one_le_exp_iff.mpr (mul_nonneg bp.le xp)
    have h := mul_le_mul_of_nonneg_left xe (mul_nonneg Qp xp)
    dsimp [Q] at *
    linarith only [h]

end CircleWidthThreshold
