module

public import CircleGaussianTracking
public import CircleKernelGD
import all CircleFlowMoments
import all CircleFlowTracking
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Uniform-in-width arithmetic for the two stopping times of the circle flow. -/
@[expose] public section
noncomputable section
namespace CircleVariableFlowSchedule
open Real MeasureTheory CircleFlowMoments CircleFlowTracking

def d (x : ℝ) := 128*log x
def R (x : ℝ) := 2+sqrt (8*d x)
def gap (x : ℝ) := 1/(π*x)^2
def U (x : ℝ) := R x / gap x
def u (x y : ℝ) := 64*sqrt (d x/y)
def rho (x y : ℝ) := 32*U x/sqrt y
def error (x y : ℝ) := 2*(30*rho x y+3*u x y)
def bad (x : ℝ) := 8*(x+1)^2*exp (-d x)
def fourth (T y : ℝ) := 7/2+3*sqrt (2*T)*gaussianSquareNorm+(1+sqrt (2*T)+2*T/sqrt y)*lossConstant
def constant : ℝ := 4000000000+3*(7/2+150*gaussianSquareNorm+821*lossConstant)
def long (x : ℝ) := 2*π^2*x^2*log (2*sqrt (12*x)*x^3)

private theorem eight {x y : ℝ} (_hx : 1≤x) (hy : x^16≤y) : x^8≤sqrt y := by
  have w : (x^8)^2 ≤ y := by simpa only [←pow_mul] using hy
  exact le_sqrt_of_sq_le w

private theorem log_one {x : ℝ} (hx : 65536≤x) : 1≤log x :=
  (le_log_iff_exp_le (by linarith)).mpr (by linarith [exp_one_lt_d9])

private theorem envelopes {x y : ℝ} (hx : 65536≤x) (hy : x^16≤y) :
    R x≤34*sqrt (log x) ∧ U x≤544*x^2*sqrt (log x) ∧
    rho x y≤17408*x^2*sqrt (log x)/sqrt y ∧ u x y≤768*sqrt (log x)/sqrt y ∧
    error x y≤1050000*x^2*sqrt (log x)/sqrt y := by
  have x1 : 1≤x := by linarith
  have xp : 0<x := by linarith
  have l := log_one hx
  have sl : 1≤sqrt (log x) := one_le_sqrt.mpr l
  have yn : 0≤y := (pow_nonneg xp.le 16).trans hy
  have sy : 0<sqrt y := lt_of_lt_of_le (pow_pos xp 8) (eight x1 hy)
  have r : R x ≤34*sqrt (log x) := by
    have eq : 8*d x=32^2*log x := by unfold d;ring
    rw [R,eq,sqrt_mul (by norm_num),sqrt_sq (by norm_num : (0:ℝ)≤32)]
    linarith
  have p16 : π^2≤16 := by nlinarith [sq_nonneg (4-π),mul_self_le_mul_self pi_pos.le pi_le_four]
  have pu : U x≤544*x^2*sqrt (log x) := by
    rw [U,gap,div_div_eq_mul_div,div_one,mul_pow]
    have c := mul_le_mul r p16 (sq_nonneg π) (show 0≤34*sqrt (log x) by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right c (sq_nonneg x)]
  have pr : rho x y≤17408*x^2*sqrt (log x)/sqrt y := by
    apply div_le_div_of_nonneg_right _ sy.le
    nlinarith only [pu]
  have v : u x y≤768*sqrt (log x)/sqrt y := by
    unfold u d
    rw [sqrt_div (by positivity),sqrt_mul (by norm_num : (0:ℝ)≤128)]
    have eq := sqrt_le_sqrt (by norm_num : (128:ℝ)≤12^2)
    rw [sqrt_sq (by norm_num : (0:ℝ)≤12)] at eq
    apply (le_div_iff₀ sy).mpr
    field_simp; linarith only [eq]
  have v2 : u x y≤768*x^2*sqrt (log x)/sqrt y := v.trans (div_le_div_of_nonneg_right
    (by nlinarith only [mul_le_mul_of_nonneg_right (one_le_pow₀ (n:=2) x1) (sqrt_nonneg (log x))]) sy.le)
  refine ⟨r,pu,pr,v,?_⟩
  unfold error
  have h := add_le_add (mul_le_mul_of_nonneg_left pr (by norm_num : (0:ℝ)≤30))
    (mul_le_mul_of_nonneg_left v2 (by norm_num : (0:ℝ)≤3))
  have non : 0≤x^2*sqrt (log x)/sqrt y := by positivity
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤2)).trans
  calc
    _ = 1049088*(x^2*sqrt (log x)/sqrt y) := by ring
    _ ≤ 1050000*(x^2*sqrt (log x)/sqrt y) := mul_le_mul_of_nonneg_right (by norm_num) non
    _ = _ := by ring

/-- All tube and exponential concentration hypotheses, uniformly for m≥N^16. -/
theorem conditions {N m : ℕ} (hn : 65536≤N) (hm : N^16≤m) :
    1≤d N ∧ d N≤m ∧ rho N m≤1 ∧ u N m≤1 ∧ 2*error N m≤gap N := by
  let x : ℝ := N
  let y : ℝ := m
  have hx : 65536≤x := by dsimp [x];exact_mod_cast hn
  have hy : x^16≤y := by dsimp [x,y];exact_mod_cast hm
  have xp : 0<x := by linarith
  have x1 : 1≤x := by linarith
  have l := log_one hx
  have lx : log x≤x := by linarith [log_le_sub_one_of_pos xp]
  have sy := eight x1 hy
  have yp : 0<sqrt y := (pow_pos xp 8).trans_le sy
  have sl : sqrt (log x)≤x := sqrt_le_iff.mpr ⟨xp.le,lx.trans (by nlinarith [mul_le_mul_of_nonneg_right x1 xp.le])⟩
  have e := envelopes hx hy
  have x3 : (65536:ℝ)^3≤x^3 := pow_le_pow_left₀ (by norm_num) hx 3
  have groe {i j : ℕ} (ij : i≤j) : x^i≤x^j := pow_le_pow_right₀ x1 ij
  have big : 33600000*x^5≤sqrt y := by
    apply le_trans _ sy
    rw [show x^8=x^3*x^5 by ring];apply mul_le_mul_of_nonneg_right _ (pow_nonneg xp.le 5)
    norm_num at x3;linarith only [x3]
  have t (k : ℝ) (hk : 0≤k) (hK : k≤33600000) : k*x^2*sqrt (log x)≤sqrt y := by
    apply le_trans _ big
    have h := mul_le_mul_of_nonneg_left sl (mul_nonneg hk (sq_nonneg x))
    nlinarith only [h,mul_le_mul_of_nonneg_right hK (pow_nonneg xp.le 3),groe (by decide : 3≤5)]
  refine ⟨by change 1≤128*log x;linarith,?_,?_,?_,?_⟩
  · change 128*log x≤y
    apply le_trans _ hy
    have h := mul_le_mul_of_nonneg_right hx xp.le
    nlinarith only [lx,h,groe (by decide : 2≤16)]
  · exact e.2.2.1.trans ((div_le_one yp).mpr (t _ (by norm_num) (by norm_num)))
  · apply e.2.2.2.1.trans ((div_le_one yp).mpr _)
    have z := t 768 (by norm_num) (by norm_num)
    nlinarith only [z,mul_le_mul_of_nonneg_right (one_le_pow₀ (n:=2) x1) (sqrt_nonneg (log x))]
  · change 2*error x y ≤ 1/(π*x)^2
    apply (mul_le_mul_of_nonneg_left e.2.2.2.2 (by norm_num : (0:ℝ)≤2)).trans
    rw [le_div_iff₀ (sq_pos_of_pos (mul_pos pi_pos xp))]
    rw [show 2*(1050000*x^2*sqrt (log x)/sqrt y)*(π*x)^2 =
      (2100000*π^2*x^4*sqrt (log x))/sqrt y by ring,div_le_one yp]
    have p := mul_self_le_mul_self pi_pos.le pi_le_four
    nlinarith only [big,mul_le_mul_of_nonneg_left sl (show 0≤2100000*π^2*x^4 by positivity),
      mul_le_mul_of_nonneg_right p (pow_nonneg xp.le 5)]

private theorem exp_minus {x : ℝ} (hx : 0<x) (k : ℕ) : exp (-((k:ℝ)*log x))=1/x^k := by
  rw [←log_pow,exp_neg,exp_log (pow_pos hx k),one_div]

theorem failure {x : ℝ} (hx : 1≤x) : bad x≤32/x^126 := by
  have xp : 0<x := by linarith
  have e := exp_minus xp 128
  norm_num only [Nat.cast_ofNat] at e
  rw [bad,d,e,mul_one_div,div_le_div_iff₀ (pow_pos xp _) (pow_pos xp _)]
  have s := pow_le_pow_left₀ (by linarith : 0≤x+1) (by linarith : x+1≤2*x) 2
  nlinarith only [mul_le_mul_of_nonneg_right s (pow_nonneg xp.le 126)]

theorem failure_root {x : ℝ} (hx : 1≤x) : (bad x)^((1:ℝ)/4) ≤ 3*sqrt x/x^32 := by
  have xp : 0<x := by linarith
  have bs : 0≤bad x := by unfold bad;positivity
  have s := failure hx
  have sq := sq_sqrt xp.le
  have root : ((bad x)^((1:ℝ)/4))^4=bad x := by simpa only [one_div,Nat.cast_ofNat] using Real.rpow_inv_natCast_pow bs (by decide : 4≠0)
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg bs _) (by positivity : 0≤3*sqrt x/x^32) (by decide : 4≠0)).mp
  rw [root,div_pow,mul_pow,show sqrt x^4=x^2 by rw [show (4:ℕ)=2*2 by decide,pow_mul,sq]]
  apply s.trans
  rw [div_le_div_iff₀ (pow_pos xp _) (pow_pos (pow_pos xp _) _)]
  nlinarith only [pow_nonneg xp.le 128]

private theorem fourth_bound {x y T : ℝ} (hx : 65536≤x) (hy : x^16≤y)
    (hT : T≤(horizon x:ℝ)) :
    fourth T y ≤ (7/2+150*gaussianSquareNorm+821*lossConstant)*x*sqrt (log x) := by
  have xp : 0<x := by linarith
  have x1 : 1≤x := by linarith
  have l := log_one hx
  have sl1 : 1≤sqrt (log x) := one_le_sqrt.mpr l
  have nsl : 1≤x*sqrt (log x) := one_le_mul_of_one_le_of_one_le x1 sl1
  have ly := eight x1 hy
  have yp : 0<sqrt y := (pow_pos xp 8).trans_le ly
  have hl := CircleGaussianTracking.horizon_log_upper x1
  rw [log_mul (by norm_num) xp.ne'] at hl
  have l8 : log 8≤7 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)]
  have upper : T≤1250*x^2*log x := by
    apply hT.trans (hl.trans _)
    nlinarith only [mul_le_mul_of_nonneg_left (by linarith only [l8,l] : 1+128*(log 8+log x)≤1250*log x) (sq_nonneg x)]
  have rs : sqrt (2*T)≤50*x*sqrt (log x) := sqrt_le_iff.mpr ⟨by positivity,by
    rw [mul_pow,sq_sqrt (by linarith : 0≤log x)];nlinarith only [upper]⟩
  have tt : 2*T/sqrt y≤770 := by
    apply (div_le_iff₀ yp).mpr
    have c := hT.trans (CircleGaussianTracking.horizon_le_cubic x1)
    have g := (pow_le_pow_right₀ x1 (by decide : 3≤8)).trans ly
    linarith
  have gn : 0≤gaussianSquareNorm := lpNorm_nonneg
  have ln : 0≤lossConstant := by unfold lossConstant;positivity
  have b : 1+sqrt (2*T)+2*T/sqrt y≤821*(x*sqrt (log x)) := by linarith
  unfold fourth
  nlinarith only [mul_le_mul_of_nonneg_right rs gn,mul_le_mul_of_nonneg_right b ln,nsl]

/-- Width-dependent arithmetic error, with a separate exceptional-seed term,
at every nonnegative time through the ceiling of the long horizon. -/
theorem all_times {N m : ℕ} (hn : 65536≤N) (hm : N^16≤m) {T : ℝ} (ht : T≤(horizon N:ℝ)) :
    6*error N m*U N + fourth T m*(bad N)^((1:ℝ)/4) ≤
      constant*((N:ℝ)^4*log N/sqrt m + sqrt (N:ℝ)*sqrt (log N)/(N:ℝ)^31) := by
  let x : ℝ := N
  have hx : 65536≤x := by dsimp [x];exact_mod_cast hn
  have hy : x^16≤(m:ℝ) := by dsimp [x];exact_mod_cast hm
  have xp : 0<x := by linarith
  have x1 : 1≤x := by linarith
  have ln := (log_nonneg x1)
  have e := envelopes hx hy
  have pn : 0≤U x := by unfold U R gap; positivity
  have sn : 0≤(bad x)^((1:ℝ)/4) := Real.rpow_nonneg (by unfold bad;positivity) _
  have p1 : 6*error x m*U x ≤ 4000000000*(x^4*log x/sqrt m) := by
    have c := mul_le_mul e.2.2.2.2 e.2.1 pn (by positivity)
    have eq : (1050000*x^2*sqrt (log x)/sqrt m)*(544*x^2*sqrt (log x))=
        571200000*(x^4*log x/sqrt m) := by
      conv_rhs => rw [←sq_sqrt ln];
      ring
    rw [eq] at c
    nlinarith only [c,show 0≤x^4*log x/sqrt m by positivity]
  let C := 7/2+150*gaussianSquareNorm+821*lossConstant
  have cp : 0≤C := by
    have l : 0≤lossConstant := by unfold lossConstant;positivity
    have g : 0≤gaussianSquareNorm := lpNorm_nonneg
    unfold C;positivity
  have c := mul_le_mul (fourth_bound hx hy ht) (failure_root x1) sn
    (show 0≤C*x*sqrt (log x) by positivity)
  have eq : (C*x*sqrt (log x))*(3*sqrt x/x^32)=3*C*(sqrt x*sqrt (log x)/x^31) := by field_simp
  change _ ≤ (C*x*sqrt (log x))*(3*sqrt x/x^32) at c
  rw [eq] at c
  change _ ≤ (4000000000+3*C)*(x^4*log x/sqrt m+sqrt x*sqrt (log x)/x^31)
  nlinarith only [p1,c,mul_nonneg cp (show 0≤x^4*log x/sqrt m by positivity),
    show 0≤sqrt x*sqrt (log x)/x^31 by positivity]

private theorem constant_nonneg : 0≤constant := by
  have a : 0≤gaussianSquareNorm := lpNorm_nonneg
  have b : 0≤lossConstant := by unfold lossConstant;positivity
  unfold constant;positivity

/-- A width supporting the exponent k gives the corresponding uniform
accuracy contribution, before adding the deterministic transient. -/
theorem polynomial {N m k : ℕ} (hn : 65536≤N) (hm : N^16≤m) (size : (N:ℝ)^(k+4)≤sqrt (m:ℝ))
    (hk : k≤30) {T : ℝ} (ht : T≤(horizon N:ℝ)) :
    6*error N m*U N + fourth T m*(bad N)^((1:ℝ)/4) ≤ 2*constant*log N/(N:ℝ)^k := by
  let x : ℝ := N
  have hx : 65536≤x := by dsimp [x];exact_mod_cast hn
  have xp : 0<x := by linarith
  have x1 : 1≤x := by linarith
  have l := log_one hx
  have lp : 0≤log x := by linarith
  have sy : 0<sqrt (m:ℝ) := (pow_pos xp (k+4)).trans_le size
  have wid : x^4*log x/sqrt m ≤ log x/x^k := by
    rw [div_le_div_iff₀ sy (pow_pos xp k)]
    have z := mul_le_mul_of_nonneg_left size lp
    simpa only [pow_add,x] using le_trans (by rw [pow_add];apply le_of_eq;ring : (N:ℝ)^4*log N*(N:ℝ)^k≤log N*(N:ℝ)^(k+4)) z
  have sqx : sqrt x≤x := sqrt_le_iff.mpr ⟨xp.le,by nlinarith [mul_le_mul_of_nonneg_right x1 xp.le]⟩
  have sql : sqrt (log x)≤log x := sqrt_le_iff.mpr ⟨lp,by nlinarith [mul_le_mul_of_nonneg_right l lp]⟩
  have f : sqrt x*sqrt (log x)/x^31 ≤ log x/x^k := by
    rw [div_le_div_iff₀ (pow_pos xp _) (pow_pos xp _)]
    have q := mul_le_mul_of_nonneg_right (mul_le_mul sqx sql (sqrt_nonneg _) xp.le) (pow_nonneg xp.le k)
    have a := pow_le_pow_right₀ x1 (show k+1≤31 by omega)
    rw [pow_succ] at a
    nlinarith only [q,mul_le_mul_of_nonneg_left a lp]
  exact (all_times hn hm ht).trans ((mul_le_mul_of_nonneg_left (add_le_add wid f) constant_nonneg).trans_eq (by ring))

/-- Physical and rounded deadlines have the same one-sided clock bounds. -/
theorem clocks {N : ℕ} [NeZero N] (hn : 3≤N) :
    3*log N ≤ CircleKernelGD.gamma N*(π^2*log N) ∧
    18*log N ≤ CircleKernelGD.gamma N*(60*log N) ∧
    60*log N ≤ long N ∧ long N≤(horizon N:ℝ) := by
  let x : ℝ := N
  have x3 : 3≤x := by dsimp [x];exact_mod_cast hn
  have x1 : 1≤x := by linarith
  have xp : 0<x := by linarith
  have l := log_nonneg x1
  have gl := (CircleKernelGD.gamma_bounds (N:=N)).1
  have pp := sq_pos_of_pos pi_pos
  have p10 : π^2≤10 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_lt_d2.le) (show 0≤3.15+π by positivity)]
  have lower : (3:ℝ)/10≤CircleKernelGD.gamma N :=
    (div_le_div_of_nonneg_left (by norm_num) pp p10).trans gl
  have scale : x≤2*sqrt (12*x)*x^3 := by
    have s := one_le_sqrt.mpr (show 1≤12*x by linarith)
    have p : x≤x^3 := by simpa using pow_le_pow_right₀ x1 (by decide : 1≤3)
    nlinarith only [p,mul_le_mul_of_nonneg_right s (pow_nonneg xp.le 3),pow_nonneg xp.le 3]
  have lg := log_le_log xp scale
  have asq : 3^2≤x^2 := pow_le_pow_left₀ (by norm_num) x3 2
  have psq : (3:ℝ)^2≤π^2 := pow_le_pow_left₀ (by norm_num) pi_gt_three.le 2
  have sc : 60≤2*π^2*x^2 := by nlinarith only [mul_le_mul psq asq (by norm_num) (sq_nonneg π)]
  refine ⟨?_,?_,?_,Nat.le_ceil _⟩
  · have g := (div_le_iff₀ pp).mp gl
    nlinarith only [mul_le_mul_of_nonneg_right g l]
  · nlinarith only [mul_le_mul_of_nonneg_right lower l]
  · change 60*log x≤2*π^2*x^2*log (2*sqrt (12*x)*x^3)
    nlinarith only [mul_le_mul sc lg l (by positivity : 0≤2*π^2*x^2)]

theorem stopped {N m k p : ℕ} [NeZero N] (hn : 65536≤N) (hm : N^16≤m)
    (size : (N:ℝ)^(k+4)≤sqrt (m:ℝ)) (hk : k≤30) {T : ℝ} (ht : 0≤T) (hT : T≤(horizon N:ℝ))
    (clock : (p:ℝ)*log N≤CircleKernelGD.gamma N*T) :
    6*error N m*U N + fourth T m*(min 1 (bad N))^((1:ℝ)/4) + sqrt 2*exp (-(CircleKernelGD.gamma N*T))
      ≤ 2*constant*log N/(N:ℝ)^k + sqrt 2/(N:ℝ)^p := by
  have xp : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have dp : 0≤bad N := by unfold bad;positivity
  have kz : 0≤fourth T m := by
    have a : 0≤gaussianSquareNorm := lpNorm_nonneg
    have b : 0≤lossConstant := by unfold lossConstant;positivity
    unfold fourth;positivity
  have cmp := Real.rpow_le_rpow (le_min zero_le_one dp) (min_le_right (1:ℝ) (bad N)) (by norm_num : (0:ℝ)≤1/4)
  have st := exp_le_exp.mpr (neg_le_neg clock)
  rw [exp_minus xp p] at st
  exact add_le_add ((add_le_add le_rfl (mul_le_mul_of_nonneg_left cmp kz)).trans (polynomial hn hm size hk hT))
    ((mul_le_mul_of_nonneg_left st (sqrt_nonneg _)).trans_eq (by ring))

/-- Error budget in the finite trained-flow comparison. -/
def bound (N m : ℕ) [NeZero N] (T : ℝ) :=
  6*error N m*U N+fourth T m*(min 1 (bad N))^((1:ℝ)/4)+sqrt 2*exp (-(CircleKernelGD.gamma N*T))

private theorem medium_bound {N m k : ℕ} [NeZero N] (hn : 65536≤N) (hm : N^16≤m)
    (size : (N:ℝ)^(k+4)≤sqrt (m:ℝ)) (hk : k≤18) {T : ℝ} (late : 60*log N≤T) (hT : T≤(horizon N:ℝ)) :
    bound N m T ≤ (2*constant+sqrt 2)*log N/(N:ℝ)^k := by
  let x : ℝ := N
  have hx : 65536≤x := by dsimp [x];exact_mod_cast hn
  have xp : 0<x := by linarith
  have x1 : 1≤x := by linarith
  have l := log_one hx
  have t : 0≤T := (show 0≤60*log x by linarith).trans late
  have cg := (clocks (N:=N) (by omega)).2.1
  have g : 0≤CircleKernelGD.gamma N := (by positivity : (0:ℝ)≤3/π^2).trans CircleKernelGD.gamma_bounds.1
  have clock : (k:ℝ)*log N≤CircleKernelGD.gamma N*T := by
    apply le_trans _ (cg.trans (mul_le_mul_of_nonneg_left late g))
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (log_nonneg x1)
  have h := stopped hn hm size (show k≤30 by omega) t hT clock
  apply h.trans
  change _ ≤ (2*constant+sqrt 2)*log x/x^k
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ (pow_nonneg xp.le k)
  nlinarith only [mul_le_mul_of_nonneg_left l (sqrt_nonneg (2:ℝ))]

/-- All widths m≥N^16, including both physical and rounded long horizons. -/
theorem long_bounds {N m : ℕ} [NeZero N] (hn : 65536≤N) (hm : N^16≤m) {T : ℝ}
    (late : 60*log N≤T) (hT : T≤(horizon N:ℝ)) :
    bound N m T≤(2*constant+sqrt 2)*log N/(N:ℝ)^4 := by
  have h : (N:ℝ)^16≤m := by exact_mod_cast hm
  exact medium_bound hn hm (eight (by exact_mod_cast (show 1≤N by omega)) h) (by decide) late hT

/-- The common comparison width m=N^32 also gives the N^-12 rate throughout the
time window from 60 log N through the rounded long horizon. -/
theorem wide_bounds {N m : ℕ} [NeZero N] (hn : 65536≤N) (hm : N^32≤m) {T : ℝ}
    (late : 60*log N≤T) (hT : T≤(horizon N:ℝ)) :
    bound N m T≤(2*constant+sqrt 2)*log N/(N:ℝ)^12 := by
  have g : N^16≤m := (Nat.pow_le_pow_right (by omega : 0<N) (by decide : 16≤32)).trans hm
  have h : (N:ℝ)^32≤m := by exact_mod_cast hm
  have sz := le_sqrt_of_sq_le (show ((N:ℝ)^16)^2≤m by simpa only [←pow_mul] using h)
  exact medium_bound hn g sz (by decide) late hT

/-- At the first stopping time the deterministic constant-mode transient
is exactly of the order needed, even at the smallest claimed width. -/
theorem short_bounds {N m : ℕ} [NeZero N] (hn : 65536≤N) (hm : N^16≤m) {T : ℝ}
    (start : π^2*log N≤T) (hT : T≤(horizon N:ℝ)) :
    bound N m T≤(2*constant+sqrt 2)/(N:ℝ)^3 := by
  let x : ℝ := N
  have xp : 0<x := Nat.cast_pos.mpr (by omega)
  have x1 : 1≤x := by dsimp [x];exact_mod_cast (show 1≤N by omega)
  have w : x^16≤(m:ℝ) := by dsimp [x];exact_mod_cast hm
  have t : 0≤T := (mul_nonneg (sq_nonneg π) (log_nonneg x1)).trans start
  have g : 0≤CircleKernelGD.gamma N := (by positivity : (0:ℝ)≤3/π^2).trans CircleKernelGD.gamma_bounds.1
  have c := (clocks (N:=N) (by omega)).1.trans (mul_le_mul_of_nonneg_left start g)
  have hh := stopped (k:=4) (p:=3) hn hm (eight x1 w) (by decide) t hT (by simpa using c)
  apply hh.trans
  change 2*constant*log x/x^4+sqrt 2/x^3 ≤ (2*constant+sqrt 2)/x^3
  rw [add_div]
  apply add_le_add_left
  have lx : log x≤x := by linarith [log_le_sub_one_of_pos xp]
  calc
    _ ≤ 2*constant*x/x^4 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left lx (mul_nonneg (by norm_num) constant_nonneg)) (pow_nonneg xp.le 4)
    _ = _ := by field_simp

/-- The long-time good-seed residual transient also suffices before rounding. -/
theorem fit_clock {x T : ℝ} (hx : 65536≤x) (late : long x≤T) :
    R x*exp (-(gap x/2*T)) ≤ 1/x^3 := by
  have xp : 0<x := by linarith
  have gr : 0<gap x/2 := by dsimp [gap];positivity
  have h := mul_le_mul_of_nonneg_left late gr.le
  have clock : log (2*sqrt (12*x)*x^3)≤gap x/2*T := by
    apply le_trans _ h;apply le_of_eq;unfold gap long;field_simp
  have e := exp_le_exp.mpr (neg_le_neg clock)
  rw [exp_neg (log _),exp_log (by positivity : 0<2*sqrt (12*x)*x^3)] at e
  apply (mul_le_mul (radius_for_horizon hx) e (exp_nonneg _) (by positivity)).trans_eq
  field_simp

end CircleVariableFlowSchedule
