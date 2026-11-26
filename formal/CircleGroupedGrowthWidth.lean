module

public import CircleGroupedWidth
import all CircleGroupedWidth
import all CircleFiniteWidth
import all CircleFiniteConfidence
import all CircleGroupedDynamics
import all CircleSignedRates
import all CircleSignedAngular
import all CircleMajorityFold
import all CircleGaussianTracking
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Sufficient integer width for the grouped path-length estimate. -/
@[expose] public section
noncomputable section
namespace CircleGroupedGrowthWidth
open Real CircleFiniteWidth CircleFiniteConfidence Filter Asymptotics

def movement (K : ℝ) (N : ℕ) (δ : ℝ) := K*sqrt (N:ℝ)*sqrt (1/δ)
def neurons (K : ℝ) (n : ℕ) (δ ε : ℝ) :=
  ⌈(CircleGroupedWidth.width n (movement K (n+1) δ) δ ε)^2⌉₊

theorem sufficient (K : ℝ) (n : ℕ) (δ ε : ℝ) :
    CircleGroupedWidth.width n (movement K (n+1) δ) δ ε ≤ sqrt (neurons K n δ ε) :=
  Real.le_sqrt_of_sq_le (Nat.le_ceil _)

theorem drift_le {N : ℕ} (hn : 3≤N) {b : ℝ} (hb : 0≤b) (hu : b≤1) : CircleGroupedDynamics.drift N b ≤ 100 := by
  let q := CircleMajorityFold.halfCell N
  have np : (3:ℝ)≤N := by exact_mod_cast hn
  have q0 : 0≤q := (CircleSignedAngular.half_range hn).1.le
  have q1 : q ≤ 2/3 := by
    unfold q CircleMajorityFold.halfCell
    apply (div_le_iff₀ (show 0<2*(N:ℝ) by linarith)).mpr
    linarith [pi_lt_four]
  have ub := CircleSignedRates.finite_bounds hn hb hu
  have B : CircleSignedAngular.B N b≤2 := ub.1.trans (by change 1-b+2*q^2≤2;nlinarith [pow_le_pow_left₀ q0 q1 2])
  have G : CircleSignedAngular.G N b≤3 := ub.2.trans (by change 1-b+2*q^2+q≤3;nlinarith [pow_le_pow_left₀ q0 q1 2])
  unfold CircleGroupedDynamics.drift
  linarith

set_option maxHeartbeats 1000000 in
theorem sqrt_width (n : ℕ) (hn : 3≤n+1) {K δ ε : ℝ} (hK : 1≤K) (hδ : 0<δ) (hδ1 : δ≤1) (hε : 0<ε) (hε1 : ε≤1) :
    CircleGroupedWidth.width n (movement K (n+1) δ) δ ε ≤ 4000*K^2*(n+1:ℝ)^3/(δ*ε) := by
  let N := n+1
  let x := (n+1:ℝ)
  let s := sqrt x
  let u := sqrt (1/δ)
  let a := 2*movement K N δ
  let b := CircleSpectrum.weight 1 n
  let F := K^2*x^3*u^2
  have cast : (N:ℝ)=x := by dsimp [N,x];push_cast;rfl
  have x3 : (3:ℝ)≤x := by dsimp [x];exact_mod_cast hn
  have x1 : 1≤x := by linarith
  have xp : 0<x := by linarith
  have s1 : 1≤s := one_le_sqrt.mpr x1
  have sp := zero_lt_one.trans_le s1
  have u1 : 1≤u := one_le_sqrt.mpr ((one_le_div hδ).mpr hδ1)
  have up := zero_lt_one.trans_le u1
  have k0 := zero_lt_one.trans_le hK
  have us : u^2=1/δ := sq_sqrt (by positivity)
  have ss : s^2=x := sq_sqrt xp.le
  have mp : movement K N δ=K*(s*u) := by dsimp [movement];rw [cast];ring
  have unit : 1≤s*u := one_le_mul_of_one_le_of_one_le s1 u1
  have ap : 1≤a := by dsimp [a];rw [mp];linarith [one_le_mul_of_one_le_of_one_le hK unit]
  have a0 := zero_lt_one.trans_le ap
  have wb := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  have xs : s≤x := by nlinarith only [ss,mul_nonneg (sub_nonneg.mpr s1) sp.le]
  have x3g : x≤x^3 := by simpa only [pow_one] using pow_le_pow_right₀ x1 (by decide : 1≤3)
  have k2 : K≤K^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hK) k0.le]
  have u2 : u≤u^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr u1) up.le]
  have aux : K*x*u≤F := mul_le_mul (mul_le_mul k2 x3g xp.le (sq_nonneg _)) u2 up.le (by positivity)
  have capA : a≤2*(K*x*u) := by
    dsimp only [a];rw [mp]
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right xs up.le) k0.le]
  have Fp : 0≤F := by dsimp [F];positivity
  have room : 4000*F≤4000*F/ε := le_div_self (by positivity) hε hε1
  have pay : 4000*F/ε=4000*K^2*x^3/(δ*ε) := by dsimp [F];rw [us];ring
  have capR : sqrt (36/δ) ≤ 6*u := by
    apply sqrt_le_iff.mpr ⟨by positivity,?_⟩
    rw [mul_pow,us];exact le_of_eq (by ring)
  have hu : gridScale N δ ≤ 10*x*u := by
    have z : sqrt (90/δ)≤10*u := sqrt_le_iff.mpr ⟨by positivity,by rw [mul_pow,us,show 90/δ=90*(1/δ) by ring];nlinarith only [one_div_pos.mpr hδ]⟩
    unfold gridScale
    rw [cast];exact (mul_le_mul_of_nonneg_left z xp.le).trans_eq (by ring)
  have ex : x*u≤K*x*u := by apply mul_le_mul_of_nonneg_right _ up.le;exact le_mul_of_one_le_left xp.le hK
  have uF : u≤F := (le_mul_of_one_le_left up.le x1).trans (ex.trans aux)
  have g : gridScale N δ+36*a ≤ 82*(K*x*u) := by linarith only [hu,ex,capA]
  have margin : 135*(x+1)/(δ*a) ≤ 270*F := by
    apply (div_le_iff₀ (mul_pos hδ a0)).mpr
    have xF : x*u^2≤F := by
      dsimp [F];gcongr
      exact x3g.trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hK))
    have red : x≤F*δ := by
      apply (div_le_iff₀ hδ).mp
      simpa only [us,div_eq_mul_inv,one_mul] using xF
    have t := le_mul_of_one_le_right (show 0≤F*δ by positivity) ap
    nlinarith only [x1,red,t]
  have kp : (π*x)^2 ≤ 16*x^2 := by rw [mul_pow];gcongr;nlinarith [pi_lt_four,pi_pos]
  have op : 2*(gridScale N δ+36*a)/gap N≤2624*F := by
    rw [gap,cast,div_div_eq_mul_div,div_one]
    have hh := mul_le_mul (show 2*(gridScale N δ+36*a)≤164*(K*x*u) by linarith only [g]) kp (sq_nonneg _) (by positivity)
    apply hh.trans
    have g' := mul_le_mul k2 u2 up.le (sq_nonneg _)
    dsimp only [F]
    nlinarith only [mul_le_mul_of_nonneg_right g' (show 0≤x^3 by positivity)]
  have row : rowScale N δ≤10*(s*u) := by
    unfold rowScale;rw [cast]
    apply sqrt_le_iff.mpr ⟨by positivity,?_⟩
    rw [mul_pow,mul_pow,ss,us]
    rw [show 90*x/δ=90*(x*(1/δ)) by ring];nlinarith only [mul_nonneg xp.le (one_div_pos.mpr hδ).le]
  have signed : signedScale N b δ ≤ 70*(s*u) := by
    unfold signedScale
    have c : 6/(N:ℝ)+1-b≤7 := by rw [cast]; dsimp [b];linarith [(div_le_iff₀ xp).mpr (show 6≤6*x by linarith)]
    exact (mul_le_mul c row (sqrt_nonneg _) (by norm_num)).trans_eq (by ring)
  have bracket : signedScale N b δ+CircleGroupedDynamics.drift N b*a ≤270*(K*(s*u)) := by
    have t := mul_le_mul_of_nonneg_right (drift_le hn wb.1 wb.2) a0.le
    have t' := le_mul_of_one_le_left (mul_nonneg sp.le up.le) hK
    change CircleGroupedDynamics.drift N b*a≤100*a at t
    have ea : a=2*(K*(s*u)) := by dsimp only [a];rw [mp]
    linarith only [t,t',signed,ea]
  have final : 2*x^2*movement K N δ/ε*(signedScale N b δ+CircleGroupedDynamics.drift N b*a)≤4000*F/ε := by
    rw [mp]
    have h := mul_le_mul_of_nonneg_left bracket (show 0≤2*x^2*(K*(s*u))/ε by positivity)
    apply h.trans
    have eq : 2*x^2*(K*(s*u))/ε*(270*(K*(s*u)))=540*F/ε := by dsimp [F];rw [←ss];ring
    rw [eq];gcongr;nlinarith
  unfold CircleGroupedWidth.width
  change max a (max (sqrt (36/δ)) (max (135*((N:ℝ)+1)/(δ*a)) (max (2*(gridScale N δ+36*a)/gap N) (2*(N:ℝ)^2*movement K N δ/ε*(signedScale N b δ+CircleGroupedDynamics.drift N b*a)))))≤_
  apply le_trans _ pay.le
  refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))
  · exact (by linarith only [capA,aux,Fp] : a≤4000*F).trans room
  · exact (by linarith only [capR,uF,Fp] : sqrt (36/δ)≤4000*F).trans room
  · rw [cast];exact (by linarith only [margin,Fp] : 135*(x+1)/(δ*a)≤4000*F).trans room
  · exact (by linarith only [op,Fp] : 2*(gridScale N δ+36*a)/gap N≤4000*F).trans room
  · simpa only [cast] using final

/-- The ceiling of the squared threshold is sufficient and admits a bound
uniform in both confidence and accuracy. -/
theorem width_bound (n : ℕ) (hn : 3≤n+1) {K δ ε : ℝ} (hK : 1≤K) (hδ : 0<δ) (hδ1 : δ≤1) (hε : 0<ε) (hε1 : ε≤1) :
    (neurons K n δ ε:ℝ) ≤ ((4000*K^2)^2+1)*(n+1:ℝ)^6/(δ^2*ε^2) := by
  let w := CircleGroupedWidth.width n (movement K (n+1) δ) δ ε
  have x1 : 1≤(n+1:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have wp : 0≤w := by
    apply (show 0≤2*movement K (n+1) δ by dsimp [movement];positivity).trans
    exact le_max_left _ _
  have a := pow_le_pow_left₀ wp (sqrt_width n hn hK hδ hδ1 hε hε1) 2
  have eq : (4000*K^2*(n+1:ℝ)^3/(δ*ε))^2=(4000*K^2)^2*((n+1:ℝ)^6/(δ^2*ε^2)) := by ring
  rw [eq] at a
  have one : 1≤(n+1:ℝ)^6/(δ^2*ε^2) := by
    apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hδ) (sq_pos_of_pos hε))).mpr
    rw [one_mul]
    exact ((mul_le_mul (pow_le_one₀ hδ.le hδ1) (pow_le_one₀ hε.le hε1) (sq_nonneg _) zero_le_one).trans_eq (one_mul _)).trans (one_le_pow₀ x1)
  exact (Nat.ceil_lt_add_one (sq_nonneg w)).le.trans ((add_le_add a one).trans_eq (by ring))

/-- At confidence and accuracy 1/N, the sufficient integer width is O(N¹⁰). -/
theorem inverse_schedule {K : ℝ} (hK : 1≤K) :
    (fun n : ℕ => (neurons K n (1/(n+1:ℝ)) (1/(n+1:ℝ)):ℝ)) =O[atTop] fun n => (n+1:ℝ)^10 := by
  apply IsBigO.of_bound ((4000*K^2)^2+1)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hp : 0<(n+1:ℝ) := by positivity
  have h1 : 1/(n+1:ℝ)≤1 := (div_le_one hp).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have b := width_bound n (by omega) hK (one_div_pos.mpr hp) h1 (one_div_pos.mpr hp) h1
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (pow_nonneg hp.le 10)]
  apply b.trans_eq
  field_simp

end CircleGroupedGrowthWidth
