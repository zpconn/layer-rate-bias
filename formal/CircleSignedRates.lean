module

public import CircleSignedAngular
import all CircleSignedAngular
import all CircleMajorityFold
import all CircleGaussianTracking
import Mathlib.Tactic

/-! Finite angular error bounds and their joint-grid rates. -/
@[expose] public section
noncomputable section
namespace CircleSignedRates
open Real Filter CircleSignedAngular CircleMajorityFold Asymptotics
open scoped Topology

private theorem amplitude_approx {N : ℕ} (hn : 3≤N) :
    let q := halfCell N
    1/π≤amplitude N ∧ amplitude N-1/π≤q^2/π ∧ amplitude N≤1 := by
  intro q
  have qp := (CircleSignedAngular.half_range hn).1
  have n3 : (3:ℝ)≤N := by exact_mod_cast hn
  have np : (0:ℝ)<N := by linarith
  have q1 : q≤1 := by dsimp [q,halfCell];apply (div_le_one (by positivity)).mpr; linarith [pi_lt_four]
  have q0 : 0<q := qp
  have sqp : 0<sin q := sin_pos_of_pos_of_lt_pi qp (by linarith [pi_gt_three])
  have sc := sin_ge_sub_cube q0.le
  have sh : q/2≤sin q := by nlinarith only [sc,mul_le_mul_of_nonneg_right (pow_le_one₀ q0.le q1 (n:=2)) q0.le,q0]
  have eq : amplitude N = q/sin q/π := by dsimp [amplitude,q,halfCell];field_simp
  rw [eq]
  have ratio : 1≤q/sin q := (one_le_div sqp).mpr (sin_le q0.le)
  have hi : q/sin q ≤ 1+q^2 := by
    apply (div_le_iff₀ sqp).mpr
    nlinarith only [sc,mul_le_mul_of_nonneg_left sh (sq_nonneg q),pow_nonneg q0.le 3]
  refine ⟨div_le_div_of_nonneg_right ratio pi_pos.le,?_,(div_le_one pi_pos).mpr (hi.trans (by
    nlinarith only [pow_le_one₀ q0.le q1 (n:=2),pi_gt_three]))⟩
  rw [←sub_div];exact div_le_div_of_nonneg_right (by linarith) pi_pos.le

theorem finite_bounds {N : ℕ} (hn : 3≤N) {b : ℝ} (hb : 0≤b) (h1 : b≤1) :
    let q := halfCell N
    B N b≤(1-b)+2*q^2 ∧ G N b≤(1-b)+2*q^2+q := by
  intro q
  have ⟨_,ap,a1⟩ := amplitude_approx hn
  have a0 := (amplitude_pos hn).le
  have q0 := (CircleSignedAngular.half_range hn).1.le
  change 0≤q at q0
  have e1 : |1/π-b*amplitude N|≤(1-b)+q^2 := by
    have wb := mul_le_mul_of_nonneg_left a1 (sub_nonneg.mpr h1)
    have pe := (div_le_self (sq_nonneg q) (by linarith [pi_gt_three] : 1≤π))
    have lo := (amplitude_approx hn).1
    change amplitude N-1/π≤q^2/π at ap
    apply abs_le.mpr
    constructor <;> nlinarith only [ap,pe,lo,wb,mul_nonneg (sub_nonneg.mpr h1) a0,sub_nonneg.mpr h1,sq_nonneg q]
  have ce : 0≤1-cos q := sub_nonneg.mpr (cos_le_one _)
  have c : 1-cos q≤q^2/2 := by linarith only [one_sub_sq_div_two_le_cos (x:=q)]
  have ba : 0≤b*amplitude N := mul_nonneg hb a0
  have ba1 := (mul_le_of_le_one_left a0 h1).trans a1
  have ca : b*amplitude N*(1-cos q)≤q^2/2 := (mul_le_of_le_one_left ce ba1).trans c
  refine ⟨max_le (e1.trans (by nlinarith only [sq_nonneg q])) ?_,?_⟩
  · rw [show 1/π-b*amplitude N*cos (halfCell N)=(1/π-b*amplitude N)+(b*amplitude N*(1-cos q)) by dsimp [q];ring]
    have a := abs_add_le (1/π-b*amplitude N) (b*amplitude N*(1-cos q))
    rw [abs_of_nonneg (mul_nonneg ba ce)] at a
    linarith only [a,e1,ca,sq_nonneg q]
  · have non : 0≤1-b+q^2 := add_nonneg (sub_nonneg.mpr h1) (sq_nonneg _)
    have aux : 2*b*amplitude N*(1-cos q)/π≤q^2 := by
      apply (div_le_self (by positivity) (by linarith [pi_gt_three] : 1≤π)).trans
      linarith only [ca]
    have e₂ := pow_le_pow_left₀ (abs_nonneg _) e1 2
    rw [sq_abs] at e₂
    apply (sqrt_le_iff).mpr
    refine ⟨by nlinarith only [non,sq_nonneg q,q0],?_⟩
    change (1/π-b*amplitude N)^2+2*b*amplitude N*(1-cos q)/π≤_
    calc
      _≤(1-b+q^2+q)^2 := by nlinarith only [e₂,aux,mul_nonneg non q0]
      _≤_ := pow_le_pow_left₀ (add_nonneg non q0) (by nlinarith [sq_nonneg q]) 2

/-- The rates refer to the true equal-rate interpolation coefficient b_N. -/
theorem rates :
    (fun n : ℕ => B (n+1) (CircleSpectrum.weight 1 n)) =O[atTop] (fun n : ℕ => 1/((n:ℝ)+1)^2) ∧
    (fun n : ℕ => G (n+1) (CircleSpectrum.weight 1 n)) =O[atTop] (fun n : ℕ => 1/((n:ℝ)+1)) := by
  let c := π^2/(12*(2+1))+1
  have lim := CircleSpectrum.bias_limit 1 (by norm_num)
  have he := lim.eventually_le_const (show π^2*1/(12*(2+1))<c by dsimp [c];linarith)
  have bound : ∀ᶠ n : ℕ in atTop,
      B (n+1) (CircleSpectrum.weight 1 n)≤(c+π^2)/((n:ℝ)+1)^2 ∧
      G (n+1) (CircleSpectrum.weight 1 n)≤(c+π^2+π)/((n:ℝ)+1) := by
    filter_upwards [he,eventually_ge_atTop 2] with n h hn
    have wb := CircleGaussianTracking.weight_bounds n (by norm_num : (0:ℝ)≤1)
    have ⟨B₀,G₀⟩ := finite_bounds (N:=n+1) (by omega) wb.1 wb.2
    let s := (n:ℝ)+1
    have sp : 0<s := by dsimp [s];positivity
    have s1 : 1≤s := by dsimp [s];linarith [Nat.cast_nonneg (α:=ℝ) n]
    have q : halfCell (n+1)=π/(2*s) := by simp [halfCell,s]
    change s^2*(1-CircleSpectrum.weight 1 n)≤c at h
    rw [q] at B₀ G₀
    have H : (1-CircleSpectrum.weight 1 n)+2*(π/(2*s))^2 ≤ (c+π^2)/s^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos sp)).mpr
      field_simp
      nlinarith only [h,sq_nonneg π]
    refine ⟨B₀.trans H,G₀.trans ?_⟩
    change _≤(c+π^2+π)/s
    have cp : 0≤c+π^2 := by dsimp [c];positivity
    have p1 : s≤s^2 := by nlinarith only [mul_le_mul_of_nonneg_right s1 sp.le]
    have H' := H.trans (div_le_div_of_nonneg_left cp sp p1)
    apply (add_le_add_left H' _).trans
    field_simp; nlinarith [pi_pos]
  constructor
  · refine isBigO_iff.mpr ⟨c+π^2,bound.mono fun n h => ?_⟩
    rw [Real.norm_eq_abs,abs_of_nonneg ((abs_nonneg _).trans (le_max_left ..)),Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact h.1.trans_eq (by ring)
  · refine isBigO_iff.mpr ⟨c+π^2+π,bound.mono fun n h => ?_⟩
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤G (n+1) (CircleSpectrum.weight 1 n) from sqrt_nonneg _),Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact h.2.trans_eq (by ring)

/-- A single signed tangent-row summand is bounded by the manuscript's
d_N times the neuron's initial squared length. -/
theorem summand_bound {N : ℕ} (hn : 3≤N) (ho : Odd N) {b : ℝ} (hb : 0≤b) (h1 : b≤1)
    (w v : ℂ) (a : ℝ) (unit : ‖v‖≤1) :
    |signedFeature N b w*CircleEscape.feature w v +
      a^2*CircleEscape.gate w v*inner ℝ (signedGate N b w) v|≤(6/N+1-b)*(a^2+‖w‖^2) := by
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have n3 : (3:ℝ)≤N := by exact_mod_cast hn
  have qlo := (CircleSignedAngular.half_range hn).1.le
  have qhi : halfCell N≤2/N := by
    dsimp [halfCell]; rw [div_le_div_iff₀ (by positivity) np]; nlinarith [mul_le_mul_of_nonneg_right pi_lt_four.le np.le]
  have q1 : halfCell N≤1 := qhi.trans ((div_le_one np).mpr (by linarith))
  have qcap : 2*(halfCell N)^2+halfCell N≤6/N := by
    nlinarith only [mul_le_mul_of_nonneg_left q1 qlo,qhi,show (6:ℝ)/N=3*(2/N) by ring]
  have h := finite_bounds hn hb h1
  have bb := h.1.trans (by linarith only [qcap,qlo] : _≤6/N+1-b)
  have gg := h.2.trans (by linarith only [qcap] : _≤6/N+1-b)
  have d0 : 0≤6/(N:ℝ)+1-b := by linarith [div_nonneg (by norm_num : (0:ℝ)≤6) np.le]
  have sf := (feature_bound hn ho hb w).trans (mul_le_mul_of_nonneg_right bb (norm_nonneg _))
  have fe : |CircleEscape.feature w v|≤‖w‖ := by
    rw [CircleEscape.feature,abs_of_nonneg (le_max_right ..)]
    exact max_le ((real_inner_le_norm w v).trans (mul_le_of_le_one_right (norm_nonneg _) unit)) (norm_nonneg _)
  have gh : |CircleEscape.gate w v|≤1 := by unfold CircleEscape.gate;split <;> norm_num
  have ig := (abs_real_inner_le_norm (signedGate N b w) v).trans ((mul_le_of_le_one_right (norm_nonneg _) unit).trans ((gate_bound hn ho hb w).trans gg))
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (sq_nonneg a)]
  have t₁ := mul_le_mul sf fe (abs_nonneg _) (mul_nonneg d0 (norm_nonneg _))
  have t₂ := mul_le_mul (mul_le_of_le_one_right (sq_nonneg a) gh) ig (abs_nonneg _) (sq_nonneg a)
  exact (add_le_add t₁ t₂).trans_eq (by ring)

end CircleSignedRates
