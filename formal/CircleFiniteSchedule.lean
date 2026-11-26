module

public import CircleFiniteWidth
import all CircleFiniteWidth
import all CircleGaussianTracking
import all CircleKernelGD
import all CircleFiniteConfidence
import Mathlib.Tactic

/-! An explicit polynomial width and training-time schedule for the confidence
theorem at δ=ε=1/N. All constants are deliberately rounded upwards. -/
@[expose] public section
noncomputable section
namespace CircleFiniteSchedule
open Real Filter Topology MeasureTheory CircleEscapeBridge CircleSpectrum CircleActualTracking
  CircleFiniteWidth CircleFiniteConfidence CircleRateTrajectory CircleWidthTracking CircleFlowPath

def designWidth (N : ℕ) := (100000000*N^8)^2

/-- A square width avoids any rounding loss in the five width inequalities. -/
theorem width_bound (n : ℕ) (hn : 3≤n+1) :
    width n (1/((n+1:ℕ):ℝ)) (1/((n+1:ℕ):ℝ)) ≤ sqrt (designWidth (n+1):ℝ) := by
  let N := n+1
  let x : ℝ := N
  let u := sqrt x
  let δ := 1/x
  let b := weight 1 n
  have x3 : 3≤x := by dsimp only [x];exact_mod_cast hn
  have xp : 0<x := by linarith
  have x1 : 1≤x := by linarith
  have up : 0<u := sqrt_pos.mpr xp
  have us : u^2=x := sq_sqrt xp.le
  have u1 : 1≤u := by nlinarith only [us,up,x1]
  have dp : 0<δ := by dsimp [δ];positivity
  have wb := CircleGaussianTracking.weight_bounds n (by norm_num : (0:ℝ)≤1)
  change 0≤b ∧ b≤1 at wb
  have grow {i j : ℕ} (h : i≤j) : u^i≤u^j := pow_le_pow_right₀ u1 h
  have square12 : R δ^2=12*x := by unfold R;rw [sq_sqrt (by positivity)];dsimp only [δ];simp
  have r : R δ≤4*u := by
    apply (sq_le_sq₀ (show 0≤R δ from sqrt_nonneg _) (by positivity)).mp
    rw [square12]
    nlinarith only [us,xp]
  have r1 : 1≤R δ := by
    apply (sq_le_sq₀ zero_le_one (show 0≤R δ from sqrt_nonneg _)).mp
    rw [square12];linarith only [x3]
  have spec : (π*x)^2≤16*u^4 := by
    have a := pow_le_pow_left₀ pi_pos.le pi_le_four 2
    calc
      (π*x)^2 = π^2*x^2 := mul_pow .. 
      _ ≤ 4^2*x^2 := mul_le_mul_of_nonneg_right a (sq_nonneg _)
      _ = _ := by rw [←us];ring
  have deq : D N δ=2*R δ*(π*x)^2 := by simp [D,gap,x]
  have d : D N δ≤128*u^5 := by
    rw [deq]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left r (by norm_num : (0:ℝ)≤2)) spec (sq_nonneg _) (by positivity)).trans_eq (by ring)
  have a : A N δ≤256*u^5 := (mul_le_mul_of_nonneg_left d (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)
  have gp : 0<gap N := by unfold gap;change 0<1/(π*x)^2;positivity
  have g1 := CircleKernelGD.gap_le_one hn
  change gap N≤1 at g1
  have a1 : 1≤A N δ := by
    change 1≤2*(2*R δ/gap N)
    have z : 1≤2*R δ/gap N := (le_div_iff₀ gp).mpr (by linarith only [g1,r1])
    linarith
  have hs : sqrt (90/δ)≤10*u := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt (by positivity)]
    dsimp only [δ]
    rw [div_div_eq_mul_div,div_one]
    nlinarith only [us,xp]
  have hg : gridScale N δ≤10*u^5 := by
    change x*sqrt (90/δ)≤_
    exact (mul_le_mul_of_nonneg_left hs xp.le).trans ((show x*(10*u)=10*u^3 by rw [←us];ring).le.trans
      (mul_le_mul_of_nonneg_left (grow (by decide : 3≤5)) (by norm_num)))
  have jr : rowScale N δ≤10*u^2 := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    change sqrt (90*x/δ)^2≤_
    rw [sq_sqrt (by positivity)]
    dsimp only [δ]
    rw [div_div_eq_mul_div,div_one,←us]
    nlinarith only [sq_nonneg (u^2)]
  have v : signedScale N b δ≤30*u^5 := by
    have factor : 6/x+1-b≤3 := by
      have h : 6/x≤2 := (div_le_iff₀ xp).mpr (by linarith only [x3])
      linarith only [h,wb.1]
    exact (mul_le_mul factor jr (sqrt_nonneg _) (by norm_num : (0:ℝ)≤3)).trans
      ((show (3:ℝ)*(10*u^2)=30*u^2 by ring).le.trans (mul_le_mul_of_nonneg_left (grow (by decide : 2≤5)) (by norm_num)))
  have en : sqrt (36/δ)≤10*u := (sqrt_le_sqrt (div_le_div_of_nonneg_right (by norm_num : (36:ℝ)≤90) dp.le)).trans hs
  have mrg : 10*(x+1)/(δ*A N δ)≤20*u^4 := by
    have h : 10*(x+1)/(δ*A N δ)≤10*(x+1)/δ := div_le_div_of_nonneg_left (by positivity) dp
      ((mul_le_mul_of_nonneg_left a1 dp.le).trans_eq' (mul_one δ))
    apply h.trans
    dsimp only [δ]
    rw [div_div_eq_mul_div,div_one]
    change 10*(x+1)*x≤_
    rw [←us] at x1 ⊢
    nlinarith only [mul_nonneg (sub_nonneg.mpr x1) (sq_nonneg u)]
  have grid : 2*(gridScale N δ+36*A N δ)/gap N ≤ 300000*u^9 := by
    have h : 2*(gridScale N δ+36*A N δ)≤18452*u^5 := by linarith only [hg,a]
    change 2*(gridScale N δ+36*A N δ)/(1/(π*x)^2)≤_
    rw [div_div_eq_mul_div,div_one]
    exact (mul_le_mul h spec (sq_nonneg _) (by positivity)).trans (by nlinarith only [pow_nonneg up.le 9])
  have signed : (2*x^2*D N δ/δ)*(signedScale N b δ+(1+b)*36*A N δ)≤100000000*u^16 := by
    have both := mul_le_mul (by linarith only [wb.2] : 1+b≤2) a (by unfold A D R;positivity) (by norm_num : (0:ℝ)≤2)
    have term : signedScale N b δ+(1+b)*36*A N δ ≤ 18462*u^5 := by linarith only [v,both]
    have first : 2*x^2*D N δ/δ≤256*u^11 := by
      calc
        _ = 2*(u^2)^2*D N δ*u^2 := by rw [us];change _/(1/x)=_;simp
        _ ≤ 2*(u^2)^2*(128*u^5)*u^2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left d (by positivity)) (sq_nonneg _)
        _ = _ := by ring
    have sn : 0≤signedScale N b δ := mul_nonneg (by change 0≤6/x+1-b;linarith only [wb.2,div_nonneg (by norm_num : (0:ℝ)≤6) xp.le]) (sqrt_nonneg _)
    have ell : 0≤signedScale N b δ+(1+b)*36*A N δ := by
      have ap : 0≤A N δ := by linarith only [a1]
      have bp := wb.1
      positivity
    exact (mul_le_mul first term ell (by positivity)).trans (by nlinarith only [pow_nonneg up.le 16])
  have target : sqrt (designWidth N:ℝ)=100000000*u^16 := by
    unfold designWidth
    push_cast
    rw [Real.sqrt_sq (by positivity)]
    change 100000000*x^8=_
    rw [←us];ring
  rw [target]
  change max _ (max _ (max _ (max _ _)))≤_
  simp only [max_le_iff]
  refine ⟨a.trans ?_,en.trans ?_,mrg.trans ?_,grid.trans ?_,signed⟩
  · exact mul_le_mul (by norm_num : (256:ℝ)≤100000000) (grow (by decide : 5≤16)) (by positivity) (by norm_num)
  · exact mul_le_mul (by norm_num : (10:ℝ)≤100000000) (by simpa using grow (by decide : 1≤16)) up.le (by norm_num)
  · exact mul_le_mul (by norm_num : (20:ℝ)≤100000000) (grow (by decide : 4≤16)) (by positivity) (by norm_num)
  · exact mul_le_mul (by norm_num : (300000:ℝ)≤100000000) (grow (by decide : 9≤16)) (by positivity) (by norm_num)


/-- At unit inverse-grid confidence and accuracy the cap grows as
N² log N for each fixed positive physical learning rate. -/
theorem cap_bound (N : ℕ) (hN : 3≤N) {η : ℝ} (hη : 0<η) :
    cap N η (1/(N:ℝ)) (1/(N:ℝ))≤⌈(192/η)*(N:ℝ)^2*log N⌉₊ := by
  let x : ℝ := N
  let δ := 1/x
  have x3 : 3≤x := by dsimp only [x];exact_mod_cast hN
  have xp : 0<x := by linarith
  have dp : 0<δ := by dsimp [δ];positivity
  have small : tol N δ=1/(2*x^3) := by
    change min (1/x^3) ((1/x)/(2*x^2))=_
    rw [min_eq_right (by field_simp;norm_num)]
    ring
  have r : R δ≤4*x := by
    apply (sq_le_sq₀ (show 0≤R δ from sqrt_nonneg _) (by positivity)).mp
    rw [R,sq_sqrt (by positivity)]
    dsimp only [δ];rw [div_div_eq_mul_div,div_one]
    nlinarith only [mul_nonneg (by linarith only [x3] : 0≤x-1) xp.le,xp]
  have ratio : R δ/tol N δ≤x^6 := by
    rw [small,div_div_eq_mul_div,div_one]
    have x2 : 8≤x^2 := by nlinarith only [x3,sq_nonneg (x-3)]
    exact (mul_le_mul_of_nonneg_right r (by positivity)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right x2 (pow_nonneg xp.le 4)])
  have logr : log (R δ/tol N δ)≤6*log x := by
    have rp : 0<R δ := by unfold R;positivity
    have h := Real.log_le_log (div_pos rp (by rw [small];positivity)) ratio
    simpa only [log_pow,Nat.cast_ofNat] using h
  have spec : 2/(η*gap N)≤32*x^2/η := by
    change 2/(η*(1/(π*x)^2))≤_
    have pi2 := pow_le_pow_left₀ pi_pos.le pi_le_four 2
    field_simp
    nlinarith only [pi2]
  apply Nat.ceil_mono
  change 2/(η*gap N)*log (R δ/tol N δ)≤_
  exact (mul_le_mul_of_nonneg_left logr (by unfold gap;positivity)).trans
    ((mul_le_mul_of_nonneg_right spec (mul_nonneg (by norm_num) (log_nonneg (by linarith only [x3])))).trans_eq (by dsimp only [x];ring))

/-- An explicit sequence at which the scaled paired error vanishes in
probability, with thresholds 1/N and exceptional probabilities 1/N. -/
theorem schedule (n : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) {η : ℝ} (hη : 0<η) (hc : η≤1) :
    let N := n+1
    let m := designWidth N
    let T := cap N η (1/(N:ℝ)) (1/(N:ℝ))
    T≤⌈(192/η)*(N:ℝ)^2*log N⌉₊ ∧
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤1/(N:ℝ) ∧ ∀ z∈E,
      rms η N z T≤1/(N:ℝ)^3 ∧
      (N:ℝ)^2*|learnerMean η N z T-reference N m (weight 1 n) z|≤1/(N:ℝ) ∧
      ∃ w : State m, Tendsto (iterateAt N η z) atTop (𝓝 w) ∧ ‖gridR N w‖=0 := by
  intro N m T
  have big : (3:ℝ)≤N := by exact_mod_cast hn
  have x : (0:ℝ)<N := by linarith only [big]
  have d : 0<1/(N:ℝ) := by positivity
  have small : 1/(N:ℝ)<1 := (div_lt_one x).mpr (by linarith only [big])
  obtain ⟨E,meas,prob,he⟩ := finite_width n m hn odd hη hc d small d (width_bound n hn)
  refine ⟨cap_bound N hn hη,E,meas,prob,?_⟩
  intro z hz
  obtain ⟨fit,err,_,lim⟩ := he z hz
  exact ⟨fit,((mul_comm _ _).le.trans ((le_div_iff₀ (sq_pos_of_pos x)).mp err)),lim⟩

end CircleFiniteSchedule
