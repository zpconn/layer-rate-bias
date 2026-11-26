module

public import CircleEarlyStopping
public import CircleEarlyWidth
import all CircleEarlyWidth
import all CircleFiniteConfidence
import all CircleKernelGD
import all CircleGaussianTracking
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Integer short-horizon design size at confidence and accuracy 1/N. -/
@[expose] public section
noncomputable section
namespace CircleEarlySchedule
open Real Filter Asymptotics CircleEarlyWidth CircleFiniteConfidence

def delta (n : ℕ) : ℝ := 1/(n+1:ℝ)
def steps (η : ℝ) (n : ℕ) := cap (n+1) η (delta n) (delta n)
def neurons (η : ℝ) (n : ℕ) := ⌈(width n η (delta n) (delta n))^2⌉₊

theorem sufficient (η : ℝ) (n : ℕ) : width n η (delta n) (delta n) ≤ √(neurons η n) :=
  Real.le_sqrt_of_sq_le (Nat.le_ceil _)

private theorem gamma_sixth (N : ℕ) [NeZero N] : 1/6 ≤ CircleKernelGD.gamma N := by
  apply le_trans _ (CircleKernelGD.gamma_bounds (N:=N)).1
  apply (le_div_iff₀ (sq_pos_of_pos pi_pos)).2
  nlinarith [sq_le_sq₀ pi_pos.le (by norm_num : (0:ℝ)≤4) |>.mpr pi_lt_four.le]

private theorem xR (n : ℕ) :
    R (delta n)=sqrt 12*sqrt (n+1:ℝ) := by simp [R,delta,Real.sqrt_mul (by norm_num : (0:ℝ)≤12)]

def tscale (η : ℝ) := 42/η+1

theorem step_bound {η : ℝ} (hp : 0<η) {n : ℕ} (hn : 3≤n) :
    1≤steps η n ∧ (steps η n:ℝ) ≤ tscale η * log (n+1:ℝ) := by
  let x := (n+1:ℝ)
  let γ := CircleKernelGD.gamma (n+1)
  have a : 4≤x := by dsimp [x];exact_mod_cast (show 4≤n+1 by omega)
  have pos : 0<x := by linarith
  have s := sqrt_nonneg x
  have s₁ : 1≤sqrt x := one_le_sqrt.mpr (by linarith)
  have x₂ := sq_sqrt pos.le
  have sr : sqrt x≤x := by nlinarith [sq_nonneg (sqrt x-1)]
  have y : 1≤log x := (le_log_iff_exp_le pos).mpr (by linarith [exp_one_lt_three])
  have gp : (0:ℝ)<γ := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/6) (gamma_sixth _)
  have id : 2*R (delta n)*(↑(n+1):ℝ)^2/delta n=2*(sqrt 12*sqrt x)*x^3 := by
    rw [xR];simp only [delta,Nat.cast_add,Nat.cast_one,x,one_div,div_inv_eq_mul];ring
  let L := log (2*(sqrt 12*sqrt x)*x^3)
  have root : 1≤sqrt (12:ℝ) := by norm_num
  have arg : 1<2*(sqrt 12*sqrt x)*x^3 := by
    have z : 1≤x^3 := one_le_pow₀ (by linarith : 1≤x)
    nlinarith only [mul_le_mul root s₁ zero_le_one (sqrt_nonneg 12),
      mul_le_mul (mul_le_mul root s₁ zero_le_one (sqrt_nonneg 12)) z zero_le_one (by positivity : 0≤sqrt 12*sqrt x)]
  have lp : 0<L := log_pos arg
  have lu : L≤7*log x := by
    dsimp [L];rw [show 7*log x = log (x^(7:ℕ)) by rw [log_pow];norm_num]
    apply Real.log_le_log (by positivity)
    have four : sqrt (12:ℝ) ≤ 4 := (sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
    have e := mul_le_mul four sr s (by norm_num : (0:ℝ)≤4)
    have ge : 8≤x^3 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by linarith : 2≤x) 3
      norm_num at this;exact this
    nlinarith only [mul_le_mul_of_nonneg_right e (by positivity : 0≤x^3),
      mul_le_mul_of_nonneg_right ge (pow_nonneg pos.le 4)]
  have eq : steps η n=⌈L/(η*γ)⌉₊ := by unfold steps cap;rw [id]
  rw [eq]
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (div_pos lp (mul_pos hp gp))).ne'
  · have frac : L/(η*γ) ≤ (42/η)*log x := by
      apply (div_le_iff₀ (mul_pos hp gp)).2
      apply lu.trans
      have h := mul_le_mul_of_nonneg_right (gamma_sixth (n+1)) (mul_nonneg (by norm_num : (0:ℝ)≤42) (log_nonneg (by linarith : 1≤x)))
      field_simp [hp.ne'];dsimp [γ] at *;nlinarith
    exact (Nat.ceil_lt_add_one (div_nonneg lp.le (mul_pos hp gp).le)).le.trans
      (by dsimp [tscale];change _ ≤ (42/η+1)*log x;linarith)

theorem logarithmic_cap {η : ℝ} (hp : 0<η) :
    (fun n => (steps η n:ℝ)) =O[atTop] fun n => log (n+1:ℝ) := by
  apply Asymptotics.IsBigO.of_bound (tscale η)
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n] : 1≤(n+1:ℝ)))]
  exact (step_bound hp hn).2


private theorem width_bound {η : ℝ} (hp : 0<η) (hu : η≤1) : ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 3≤n →
    width n η (delta n) (delta n) ≤ C*(n+1:ℝ)^5 := by
  let K := 2*tscale η
  let d := 8*K
  let a := 2*d
  let e := 10+36*a
  let v := 70+72*a
  let C := a+6+20/η+K*e/log 2+2*(48*e+d*v)
  have kp : 0<K := by dsimp [K,tscale];positivity
  have dp : 0<d := by dsimp [d];positivity
  have ap : 0<a := by dsimp [a];positivity
  have ep : 0<e := by dsimp [e];positivity
  have vp : 0<v := by dsimp [v];positivity
  have hl : (0:ℝ)<log 2 := log_pos (by norm_num)
  have bp : 0<20/η := by positivity
  have cp : 0<K*e/log 2 := by positivity
  have cs : 0<2*(48*e+d*v) := by positivity
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro n hn
  let N := n+1
  let x := (n+1:ℝ)
  let S := sqrt x
  let δ := delta n
  let T := (steps η n:ℝ)
  let r := R δ
  let D₀ := D N η δ δ
  let A₀ := A N η δ δ
  let h := gridScale N δ
  let b := CircleSpectrum.weight 1 n
  let γ := CircleKernelGD.gamma N
  have cast : (N:ℝ)=x := by dsimp [N,x];push_cast;rfl
  have x1 : 1≤x := by dsimp [x];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have xp := lt_of_lt_of_le zero_lt_one x1
  have sp : 0≤S := sqrt_nonneg _
  have s1 : 1≤S := one_le_sqrt.mpr x1
  have sqr : S^2=x := sq_sqrt xp.le
  have sl : S≤x := by nlinarith [sq_nonneg (S-1)]
  have del : δ=1/x := rfl
  have dp' : 0<δ := by rw [del];positivity
  have rp : 1≤r := by
    change 1≤R (delta n);rw [xR]
    simpa only [one_mul] using mul_le_mul (by norm_num : 1≤sqrt (12:ℝ)) s1 zero_le_one (sqrt_nonneg 12)
  have ru : r≤4*S := by
    change R (delta n)≤4*S;rw [xR]
    exact mul_le_mul_of_nonneg_right ((sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩) sp
  have t1 : 1≤T := by dsimp only [T];exact_mod_cast (step_bound hp hn).1
  have tu : T≤K*S := by
    apply (step_bound hp hn).2.trans
    have logcap : log x ≤ 2*S := by
      rw [←sqr,log_pow];norm_num; linarith [log_le_sub_one_of_pos (by linarith : 0<S)]
    exact (mul_le_mul_of_nonneg_left logcap (by dsimp [tscale];positivity)).trans_eq (by dsimp [K];ring)
  have du : D₀≤d*x := by
    change 2*η*T*r ≤ _
    calc
      _ ≤ 2*1*(K*S)*(4*S) := by gcongr
      _ = _ := by dsimp [d];rw [←sqr];ring
  have au : A₀≤a*x := by
    change 2*D₀≤_;apply (mul_le_mul_of_nonneg_left du (by norm_num : (0:ℝ)≤2)).trans_eq;dsimp [a];ring
  have lo : η≤A₀ := by
    change η ≤ 2*(2*η*T*r)
    have := mul_le_mul t1 rp zero_le_one (by linarith : 0≤T)
    nlinarith only [mul_le_mul_of_nonneg_left this hp.le,hp]
  have al := hp.trans_le lo
  have br := CircleGaussianTracking.weight_bounds n (by norm_num : 0≤(1:ℝ))
  have hu' : h≤10*(S*x) := by
    have bound : sqrt (90:ℝ)≤10 := sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    dsimp only [h,gridScale];rw [cast,del,one_div,div_inv_eq_mul,sqrt_mul (by norm_num : (0:ℝ)≤90)]
    change x*(sqrt 90*S)≤_
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right bound sp) xp.le).trans_eq (by ring)
  have sx : x≤S*x := by simpa using mul_le_mul_of_nonneg_right s1 xp.le
  have eu : h+36*A₀≤e*(S*x) := by
    have H := au.trans (mul_le_mul_of_nonneg_left sx ap.le)
    dsimp [e];linarith
  have vu : signedScale N b δ ≤ 70*x := by
    have z : 6/x≤6 := (div_le_iff₀ xp).mpr (by linarith)
    have cap' : rowScale N δ≤10*x := by
      unfold rowScale
      rw [cast,del,one_div,div_inv_eq_mul]
      apply sqrt_le_iff.mpr ⟨by positivity,?_⟩
      nlinarith only [sq_nonneg x]
    change (6/(N:ℝ)+1-b)*rowScale N δ≤_;rw [cast]
    apply (mul_le_mul (show 6/x+1-b≤7 by dsimp [b];linarith [br.1]) cap' (sqrt_nonneg _) (by norm_num : (0:ℝ)≤7)).trans_eq
    ring
  have vu' : signedScale N b δ+36*(1+b)*A₀≤v*x := by
    have bh : 36*(1+b)≤72 := by dsimp [b];linarith [br.2]
    dsimp [v];linarith only [vu,mul_le_mul bh au al.le (by norm_num : (0:ℝ)≤72)]
  have x2 : x^2≤x^5 := pow_le_pow_right₀ x1 (by decide)
  have x5 : x≤x^5 := by simpa only [pow_one] using pow_le_pow_right₀ x1 (by decide : 1≤5)
  have coeff : a≤C ∧ 6≤C ∧ 20/η≤C ∧ K*e/log 2≤C ∧ 2*(48*e+d*v)≤C := by
    dsimp only [C];refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith only [ap,bp,cp,cs]
  change max A₀ (max (sqrt (36/δ)) (max (10*((N:ℝ)+1)/(δ*A₀))
    (max (η*T*(h+36*A₀)/log 2)
      (2*(N:ℝ)^2/δ*(2*b*r*(h+36*A₀)/γ+D₀*(signedScale N b δ+36*(1+b)*A₀)))))) ≤ C*x^5
  simp only [max_le_iff]
  refine ⟨au.trans (mul_le_mul coeff.1 x5 xp.le (ap.le.trans coeff.1)),?_,?_,?_,?_⟩
  · rw [del,one_div,div_inv_eq_mul,sqrt_mul (by norm_num : (0:ℝ)≤36)]
    norm_num
    exact mul_le_mul coeff.2.1 (sl.trans x5) sp (by linarith [coeff.2.1])
  · rw [cast,del]
    have H : 10*(x+1)/((1/x)*A₀) ≤ (20/η)*x^2 := by
      have id : 10*(x+1)/((1/x)*A₀) = (10*(x+1)*x)/A₀ := by field_simp
      rw [id]
      apply (div_le_iff₀ al).2
      have q := mul_le_mul_of_nonneg_left lo (by positivity : 0≤(20/η)*x^2)
      have f : (20/η)*x^2*η=20*x^2 := by field_simp
      rw [f] at q
      nlinarith only [q,mul_le_mul_of_nonneg_right x1 xp.le]
    exact H.trans (mul_le_mul coeff.2.2.1 x2 (sq_nonneg x) (bp.le.trans coeff.2.2.1))
  · have H : η*T*(h+36*A₀)/log 2 ≤ K*e/log 2*x^2 := by
      apply (div_le_div_of_nonneg_right (mul_le_mul (mul_le_mul hu tu (by linarith) zero_le_one)
        eu (by dsimp only [h,gridScale];positivity) (by positivity : 0≤1*(K*S))) hl.le).trans_eq
      rw [←sqr];ring
    exact H.trans (mul_le_mul coeff.2.2.2.1 x2 (sq_nonneg x) (cp.le.trans coeff.2.2.2.1))
  · have gp : 0<γ := (by norm_num : (0:ℝ)<1/6).trans_le (gamma_sixth N)
    have drift : 2*b*r*(h+36*A₀)/γ≤48*e*x^2 := by
      apply (div_le_iff₀ gp).2
      have small : 2*b*r*(h+36*A₀) ≤ 2*1*(4*S)*(e*(S*x)) := by
        have hb : b≤1 := br.2
        have hh : 0≤h := by dsimp only [h,gridScale];positivity
        gcongr
      have id : 2*1*(4*S)*(e*(S*x))=8*e*x^2 := by rw [←sqr];ring
      rw [id] at small
      apply small.trans
      have q := mul_le_mul_of_nonneg_left (gamma_sixth N) (by positivity : 0≤48*e*x^2)
      dsimp only [γ];linarith only [q]
    have dvu := mul_le_mul du vu' (show 0≤signedScale N b δ+36*(1+b)*A₀ by
      dsimp only [signedScale]; apply add_nonneg
      · apply mul_nonneg _ (sqrt_nonneg _);linarith [br.2,show 0≤6/(N:ℝ) by positivity]
      · have bpos : 0≤b := br.1;positivity) (by positivity : 0≤d*x)
    have H : 2*(N:ℝ)^2/δ*(2*b*r*(h+36*A₀)/γ+D₀*(signedScale N b δ+36*(1+b)*A₀)) ≤
        2*(48*e+d*v)*x^5 := by
      rw [show 2*(N:ℝ)^2/δ=2*x^2*x by rw [cast,del,one_div,div_inv_eq_mul]]
      apply (mul_le_mul_of_nonneg_left (add_le_add drift dvu) (by positivity : 0≤2*x^2*x)).trans_eq
      ring
    exact H.trans (mul_le_mul_of_nonneg_right coeff.2.2.2.2 (by positivity))

/-- Rounding the square of the published sufficient width to an integer preserves
its tenth-order growth in N. -/
theorem polynomial_width {η : ℝ} (hp : 0<η) (hu : η≤1) :
    (fun n => (neurons η n:ℝ)) =O[atTop] fun n => (n+1:ℝ)^10 := by
  obtain ⟨C,hC,H⟩ := width_bound hp hu
  apply IsBigO.of_bound (C^2+1)
  filter_upwards [eventually_ge_atTop 3] with n hn
  let w := width n η (delta n) (delta n)
  have wp : 0≤w := by
    change 0≤max _ _
    apply le_trans _ (le_max_right _ _)
    apply (sqrt_nonneg _).trans (le_max_left _ _)
  have q := pow_le_pow_left₀ wp (H n hn) 2
  have powid : ((n+1:ℝ)^5)^2=(n+1:ℝ)^10 := by ring
  rw [mul_pow,powid] at q
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (by positivity : 0≤(n+1:ℝ)^10)]
  apply (Nat.ceil_lt_add_one (sq_nonneg w)).le.trans
  have big : 1≤(n+1:ℝ)^10 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  linarith

open MeasureTheory CircleEscapeBridge CircleSpectrum

/-- The discrete integer schedule realizes the advertised high-probability precision. -/
theorem joint_schedule {η : ℝ} (hp : 0<η) (hu : η≤1) (n : ℕ)
    (hn : 3≤n+1) (odd : Odd (n+1)) :
    ∃ E : Set (Seed (neurons η n)), MeasurableSet E ∧
      (seedLaw (neurons η n)).real Eᶜ ≤ 1/(n+1:ℝ) ∧ ∀ z∈E,
      |trainedMean (CircleSeedIntegrability.path (n+1) (neurons η n) η) (steps η n) z -
        reference (n+1) (neurons η n) (weight 1 n) z| ≤ 1/(n+1:ℝ)^3 := by
  have x1 : 1<(n+1:ℝ) := by exact_mod_cast (show 1<n+1 by omega)
  have dp : 0<delta n := by dsimp [delta];positivity
  have du : delta n<1 := (div_lt_one (by linarith : 0<(n+1:ℝ))).mpr x1
  have w := sufficient η n
  have size : sqrt (36/delta n) ≤ sqrt (neurons η n) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans w)
  have nm : 0<neurons η n := by
    by_contra! hn'
    have := Nat.eq_zero_of_le_zero hn'
    rw [this,Nat.cast_zero,sqrt_zero] at size
    exact (sqrt_pos.mpr (by positivity : 0<36/delta n)).not_ge size
  obtain ⟨E,me,fail,good⟩ := CircleEarlyStopping.probability n (neurons η n) hn odd nm hp hu dp du dp du w
  refine ⟨E,me,fail,?_⟩
  intro z hz
  apply (good z hz).trans_eq
  simp only [delta,Nat.cast_add,Nat.cast_one];field_simp

end CircleEarlySchedule
