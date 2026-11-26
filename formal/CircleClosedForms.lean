module

public import CircleFiniteCoefficient
public import CircleGridSpectrum
import all CircleGridSpectrum
import all CircleFiniteCoefficient
import all CircleSpectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-! Closed trigonometric forms for the two actual constant-mode grid spectra. -/
@[expose] public section
noncomputable section
namespace CircleClosedForms
set_option maxHeartbeats 600000
open Real Filter Topology CircleSpectrum CircleFiniteCoefficient

private def f (j : ℕ) (x : ℝ) := 2*x^2/(((j:ℝ)+1)^2-x^2)
private def df (j : ℕ) (x : ℝ) := 4*x*((j:ℝ)+1)^2/(((j:ℝ)+1)^2-x^2)^2

private theorem noninteger {x : ℝ} (h : x∈Set.Ioo 0 (1:ℝ)) :
    (x:ℂ)∈Complex.integerComplement := by
  rintro ⟨i,hi⟩
  have e : (i:ℝ)=x := by exact_mod_cast hi
  have ip : (0:ℤ) < i := by exact_mod_cast (h.1.trans_eq e.symm)
  have il : i < (1:ℤ) := by exact_mod_cast e.trans_lt h.2
  omega

private theorem partial_fraction {x : ℝ} (hx : x∈Set.Ioo 0 (1:ℝ)) :
    (∑' j, f j x) = 1-(π*x)*cot (π*x) := by
  have series := cot_series_rep' (noninteger hx)
  have eq : π*cot (π*x)-1/x = ∑' j : ℕ, (1/(x-((j:ℝ)+1))+1/(x+((j:ℝ)+1))) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_cot,Complex.ofReal_div,
      Complex.ofReal_one,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_tsum] using series
  have p : ∀ j : ℕ, f j x = (-x)*(1/(x-((j:ℝ)+1))+1/(x+((j:ℝ)+1))) := by
    intro j
    have a : x< (j:ℝ)+1 := by linarith [hx.2,Nat.cast_nonneg (α:=ℝ) j]
    have b : 0<x+((j:ℝ)+1) := by linarith [hx.1,Nat.cast_nonneg (α:=ℝ) j]
    have k : ((j:ℝ)+1)^2-x^2 ≠ 0 := by nlinarith [mul_pos (sub_pos.mpr a) b]
    unfold f
    field_simp [k,ne_of_lt (sub_neg.mpr a),b.ne'];ring
  simp_rw [p]
  rw [tsum_mul_left,←eq]
  field_simp [hx.1.ne'];ring

private theorem bounds {x : ℝ} (h : x∈Set.Ioo 0 (3/4:ℝ)) (j : ℕ) :
    let k := (j:ℝ)+1
    k^2/4 ≤ k^2-x^2 ∧ 0<k^2-x^2 := by
  dsimp only
  have a : (1:ℝ)≤(j:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) j]
  have b := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) a 2
  have d := pow_le_pow_left₀ h.1.le h.2.le 2
  constructor <;> nlinarith

private theorem derivative {x : ℝ} (hx : x∈Set.Ioo 0 (3/4:ℝ)) :
    (∑' j, df j x) = -π*cot (π*x)+ x*π^2/(sin (π*x))^2 := by
  let I := Set.Ioo (0:ℝ) (3/4)
  have dr (j : ℕ) (z : ℝ) (hz : z∈I) : HasDerivAt (f j) (df j z) z := by
    have num := ((hasDerivAt_id z).pow 2).const_mul 2
    have den := (hasDerivAt_const z (((j:ℝ)+1)^2)).sub ((hasDerivAt_id z).pow 2)
    apply (num.div den (bounds hz j).2.ne').congr_deriv
    simp only [Pi.pow_apply,Pi.sub_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,zero_sub,df]
    ring
  have db (j : ℕ) (z : ℝ) (hz : z∈I) : ‖df j z‖≤64*rp 2 j := by
    obtain ⟨h,d⟩ := bounds hz j
    have k : 0<((j:ℝ)+1)^2 := by positivity
    have q := pow_le_pow_left₀ (by positivity : 0≤((j:ℝ)+1)^2/4) h 2
    have w := mul_le_mul_of_nonneg_right (show 4*z ≤4 by linarith [hz.2]) k.le
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0≤df j z by unfold df; positivity [hz.1])]
    unfold df rp
    calc
      _ ≤ 4*((j:ℝ)+1)^2/((((j:ℝ)+1)^2)/4)^2 := div_le_div₀ (by positivity) w (by positivity) q
      _ = _ := by field_simp;norm_num
  have sm (z : ℝ) (hz : z∈I) : Summable (fun j => f j z) := by
    refine (rp_two_sum.summable.mul_left 8).of_nonneg_of_le (fun j => div_nonneg (by positivity) (bounds hz j).2.le) ?_
    intro j
    obtain ⟨d,dpos⟩ := bounds hz j
    have k : 0<((j:ℝ)+1)^2 := by positivity
    have z1 : z^2 ≤ 1 := by nlinarith only [pow_le_pow_left₀ hz.1.le hz.2.le 2]
    unfold f rp
    calc
      _ ≤ 2/((((j:ℝ)+1)^2)/4) := div_le_div₀ (by norm_num) (by linarith only [z1]) (by positivity) d
      _ = _ := by field_simp;norm_num
  have h := hasDerivAt_tsum_of_isPreconnected (rp_two_sum.summable.mul_left 64)
    isOpen_Ioo (isPreconnected_Ioo (a:=(0:ℝ)) (b:=3/4)) dr db hx (sm x hx) hx
  have dπ := (hasDerivAt_id x).const_mul π
  have hsin : sin (π*x)≠0 := (sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hx.1)
    (by nlinarith [mul_lt_mul_of_pos_left hx.2 pi_pos,pi_pos])).ne'
  have cotd := (dπ.cos.div dπ.sin hsin)
  have hform := (hasDerivAt_const x (1:ℝ)).sub (dπ.mul cotd)
  have eq : (fun z => ∑' j, f j z) =ᶠ[𝓝 x] (fun z => 1-(π*z)*(cos (π*z)/sin (π*z))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    exact (partial_fraction ⟨hz.1,by linarith [hz.2]⟩).trans (by rw [cot_eq_cos_div_sin])
  have e := h.unique (hform.congr_of_eventuallyEq eq)
  rw [e,cot_eq_cos_div_sin]
  dsimp
  field_simp [hsin]
  nlinarith only [congrArg (fun y : ℝ => y*(x*π^2)) (Real.sin_sq_add_cos_sq (π*x))]


/-- The half grid spacing in angular units, N=n+1. -/
def angle (n : ℕ) := π/(2*((n:ℝ)+1))

def T₁ (q : ℝ) := -q*cot q
def T₂ (q : ℝ) := (q*cot q+q^2/(sin q)^2)/2

private def point (n : ℕ) := 1/(2*((n:ℝ)+1))

private theorem point_mem (n : ℕ) : point n ∈ Set.Ioo 0 (3/4:ℝ) := by
  have h : 0<2*((n:ℝ)+1) := by positivity
  refine ⟨one_div_pos.mpr h,(div_lt_iff₀ h).mpr ?_⟩
  linarith [Nat.cast_nonneg (α:=ℝ) n]

private theorem angle_eq (n : ℕ) : angle n=π*point n := by unfold angle point; ring

private theorem term_split (x k : ℝ) (hk : k≠0) (hd : k^2-x^2≠0) :
    2*(x^2/k^2)/(1-x^2/k^2)^2 = (x/2)*(4*x*k^2/(k^2-x^2)^2) ∧
    2*(x^2/k^2)/(1-x^2/k^2)^2-2*(x^2/k^2)^2/(1-x^2/k^2)^2 = 2*x^2/(k^2-x^2) := by
  rw [show 1-x^2/k^2 = (k^2-x^2)/k^2 by field_simp]
  constructor <;> field_simp [hk,hd];ring

/-- Closed forms for the two positive-index two-sided alias sums. -/
theorem alias_closed_forms (n : ℕ) :
    aliasA n = T₂ (angle n)-1 ∧ aliasB n = T₁ (angle n)+T₂ (angle n) := by
  let x := point n
  have hx : x ∈ Set.Ioo (0:ℝ) (3/4) := point_mem n
  have terms (j : ℕ) : aliasBTerm n j=x/2*df j x ∧ aliasBTerm n j-aliasATerm n j=f j x := by
    have off : offset n j=x^2/((j:ℝ)+1)^2 := by dsimp [x,point,offset,rp];field_simp;ring
    rw [aliasBTerm,aliasATerm,off]
    exact term_split x ((j:ℝ)+1) (by positivity) (bounds hx j).2.ne'
  have B : aliasB n=x/2*(∑' j, df j x) := by
    rw [aliasB,←tsum_mul_left]
    exact tsum_congr fun j => (terms j).1
  have D : aliasB n-aliasA n=∑' j, f j x := by
    rw [aliasB,aliasA,←(aliasB_summable n).tsum_sub (aliasA_summable n)]
    exact tsum_congr fun j => (terms j).2
  rw [derivative hx] at B
  rw [partial_fraction ⟨hx.1,by linarith [hx.2]⟩] at D
  rw [angle_eq]
  change aliasA n=T₂ (π*x)-1 ∧ aliasB n=T₁ (π*x)+T₂ (π*x)
  unfold T₁ T₂
  have aeq : aliasA n=aliasB n-(1-(π*x)*cot (π*x)) := by linarith only [D]
  rw [aeq,B]
  constructor <;> ring

/-- The covariance alias is exactly the spherical-feature alias with its
Fourier normalization. -/
theorem covariance_alias (n : ℕ) : S n=2*aliasA n/π^2 := by
  have eq : S n=U 0 n := by
    rw [S_eq_alias_sum,U_eq_alias_sum]
    apply tsum_congr
    intro j
    simp [ntkEven,covEven]
  rw [eq,tangent_alias_split]
  ring

/-- The full constant-mode covariance and weighted tangent eigenvalues,
including their frequency-zero terms. For odd N≥3 these sums are the actual
constant-mode circle grid eigenvalues. -/
theorem constant_mode_closed_forms (n : ℕ) (τ : ℝ) :
    c0+S n = 2*T₂ (angle n)/π^2 ∧
    k0 τ+U τ n = ((2+2*τ)*T₂ (angle n)+τ*T₁ (angle n))/π^2 := by
  have ab := alias_closed_forms n
  rw [covariance_alias,tangent_alias_split,ab.1,ab.2,c0,k0]
  constructor <;> ring

/-- On the benchmark odd grids these are exactly the discrete Fourier
zero-mode aliases of the covariance and layer-weighted tangent kernels. -/
theorem grid_zero_mode (n : ℕ) (hn : 3 ≤ n+1) (ho : Odd (n+1))
    (τ : ℝ) (hτ : 0 ≤ τ) (h₂ : τ ≤ 2) :
    CircleGridSpectrum.aliasValue (CircleGridSpectrum.tangentCoeff 0) (0:ZMod (n+1)) =
      2*T₂ (angle n)/π^2 ∧
    CircleGridSpectrum.aliasValue (CircleGridSpectrum.tangentCoeff τ) (0:ZMod (n+1)) =
      ((2+2*τ)*T₂ (angle n)+τ*T₁ (angle n))/π^2 := by
  have id (r : ℝ) (hr : 0≤r) (hr' : r≤2) :
      CircleGridSpectrum.aliasValue (CircleGridSpectrum.tangentCoeff r) (0:ZMod (n+1)) = k0 r+U r n := by
    rw [CircleGridSpectrum.constant_alias_eq hn ho r hr hr',U_eq_alias_sum]
    push_cast
    rfl
  rw [id 0 (by norm_num) (by norm_num),id τ hτ h₂]
  refine ⟨?_,(constant_mode_closed_forms n τ).2⟩
  simpa using (constant_mode_closed_forms n 0).2

end CircleClosedForms
