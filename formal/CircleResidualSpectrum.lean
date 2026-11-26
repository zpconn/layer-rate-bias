module

public import CircleSharpInitialization
import all CircleSharpInitialization
public import CircleReferenceMoments
import all CircleReferenceMoments
import all CircleGridSpectrum
import all CircleKernelIdentification
import all CircleSpectrum
import all CircleAngularGeometry
import all CircleEscapeBridge
import all CircleEscape
import Mathlib.Tactic

/-! Sampled Fourier modes of the actual initial residual. -/

public section
noncomputable section
namespace CircleResidualSpectrum
open CircleGridSpectrum CircleKernelIdentification CircleSpectrum CircleAngularGeometry
  CircleEscape CircleEscapeBridge MeasureTheory ProbabilityTheory Filter Finset Real
open scoped ComplexConjugate

def initialCoeff (N m : ℕ) [NeZero N] (r : ZMod N) (z : Seed m) : ℂ :=
  ZMod.dft (fun i => ((output (1/√(m:ℝ)) (initial z) (gridPoint N ((ZMod.finEquiv N).symm i)) -
    (1+(gridPoint N ((ZMod.finEquiv N).symm i)).re):ℝ):ℂ)) r / (N:ℂ)

private local instance period_pos : Fact (0<π- -π) := ⟨by linarith [pi_pos]⟩
private def wave : C(AddCircle (π- -π), ℂ) where
  toFun := AddCircle.liftIoc (π- -π) (-π) (fun t => (halfWave t:ℂ))
  continuous_toFun := by
    apply AddCircle.liftIoc_continuous
    · simp [halfWave]
    · apply Continuous.continuousOn
      unfold halfWave
      fun_prop

private theorem wave_coe (u : ℝ) : wave (u:AddCircle (π- -π)) = (halfWave u:ℂ) := by
  have h : Function.Periodic halfWave (π- -π) := by
    intro t; rw [show t+(π- -π)=t+2*π by ring]; simp [halfWave]
  let z := AddCircle.equivIoc (π- -π) (-π) (u:AddCircle (π- -π))
  have hz : ((z:ℝ):AddCircle (π- -π))=(u:AddCircle (π- -π)) := AddCircle.coe_equivIoc
  rw [←hz]
  change (AddCircle.liftIoc (π- -π) (-π) (fun t => (halfWave t:ℂ)) (z:ℝ)) = _
  rw [AddCircle.liftIoc_coe_apply z.property]
  exact congrArg Complex.ofReal (show halfWave z=halfWave u from congrArg h.lift hz)

private theorem wave_coeff (k : ℤ) : fourierCoeff wave k=(halfWaveCoeff (k:ℝ):ℂ) := by
  have he := fourier_even_profile halfWave (by unfold halfWave; fun_prop) k
  have hc : kernelCoeff halfWave k=halfWaveCoeff (k:ℝ) := by
    unfold kernelCoeff halfWaveCoeff
    let f := fun x : ℝ => halfWave x*cos (k*x)
    have hf : Continuous f := by unfold f halfWave; fun_prop
    have h1 : (∫ x in (0:ℝ)..π/2, f x) = ∫ x in (0:ℝ)..π/2, cos x*cos (k*x) := by
      apply intervalIntegral.integral_congr
      rw [Set.uIcc_of_le (by positivity)]
      intro x hx
      simp only [f,halfWave,max_eq_left (cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hx.1,pi_pos]) hx.2)]
    have h2 : (∫ x in π/2..π, f x) = 0 := by
      rw [←intervalIntegral.integral_zero (a:=π/2) (b:=π) (E:=ℝ)]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith [pi_pos])] at hx
      simp only [f,halfWave,max_eq_right (cos_nonpos_of_pi_div_two_le_of_le hx.1 (by linarith [hx.2,pi_pos])),zero_mul]
    change (1/π)*(∫ x in 0..π, f x)=_
    rw [←intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 (π/2)) (hf.intervalIntegrable (π/2) π),h1,h2]
    ring
  rw [hc] at he
  have wh : (fun x : ℝ => (halfWave |x|:ℂ))=(fun x => (halfWave x:ℂ)) := by ext x; simp [halfWave]
  rw [wh] at he
  exact he

private theorem halfWaveCoeff_abs (k : ℤ) : halfWaveCoeff (k:ℝ)=halfWaveCoeff (k.natAbs:ℝ) := by
  have h : ∀ x : ℝ, cos ((k:ℝ)*x)=cos ((k.natAbs:ℝ)*x) := by
    intro x
    cases k with
    | ofNat n => rfl
    | negSucc n =>
      simp only [Int.cast_negSucc,Int.natAbs_negSucc,Nat.cast_succ]
      rw [show (-((n:ℝ)+1))*x = -(((n:ℝ)+1)*x) by ring,cos_neg]
  simp_rw [halfWaveCoeff,h]

private theorem halfWaveCoeff_high {k : ℤ} (hk : 2≤k.natAbs) :
    |halfWaveCoeff (k:ℝ)| ≤ 2/(k:ℝ)^2 := by
  have hc : (2:ℝ)≤k.natAbs := by exact_mod_cast hk
  have h : 4≤(k.natAbs:ℝ)^2 := by nlinarith [sq_nonneg ((k.natAbs:ℝ)-2)]
  have heq : (k.natAbs:ℝ)=|(k:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  rw [halfWaveCoeff_abs,←sq_abs (k:ℝ),←heq]
  by_cases he : Even k.natAbs
  · obtain ⟨j,hj⟩ := he
    have hj' : (k.natAbs:ℝ)=2*(j:ℝ) := by exact_mod_cast (by omega : k.natAbs=2*j)
    rw [hj',halfWaveCoeff_even,abs_div,abs_pow,abs_neg,abs_one,one_pow,abs_mul,abs_of_pos pi_pos]
    have hz : 1-(2*(j:ℝ))^2<0 := by rw [←hj']; simpa using (show 1-(k.natAbs:ℝ)^2<0 by linarith)
    rw [abs_of_neg hz]
    have hp := Real.pi_gt_three
    apply (div_le_div_iff₀ (mul_pos pi_pos (neg_pos.mpr hz)) (by linarith : 0<(2*(j:ℝ))^2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hp.le (show 0≤ -(1-(2*(j:ℝ))^2) by linarith)]
  · obtain ⟨j,hj⟩ := Nat.not_even_iff_odd.mp he
    have h1 : 0<j := by omega
    obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero h1.ne'
    have hn : (k.natAbs:ℝ)=2*(l:ℝ)+3 := by exact_mod_cast (by omega : k.natAbs=2*l+3)
    rw [hn,halfWaveCoeff_odd_high,abs_zero]
    positivity

private theorem halfWaveCoeff_zero {k : ℤ} (h : ¬Even k) (hu : k.natAbs ≠ 1) : halfWaveCoeff (k:ℝ)=0 := by
  have hn : ¬Even k.natAbs := by simpa using h
  obtain ⟨j,hj⟩ := Nat.not_even_iff_odd.mp hn
  have hp : j≠0 := by omega
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero hp
  rw [halfWaveCoeff_abs,show (k.natAbs:ℝ)=2*(i:ℝ)+3 by exact_mod_cast (by omega : k.natAbs=2*i+3)]
  exact halfWaveCoeff_odd_high _

private theorem coeff_summable : Summable (fun k : ℤ => |halfWaveCoeff (k:ℝ)|) := by
  apply ((Real.summable_one_div_int_pow.mpr (by decide : 1<2)).mul_left 2).of_norm_bounded_eventually
  filter_upwards [(Finset.Icc (-1:ℤ) 1).finite_toSet.compl_mem_cofinite] with k hk
  have h : ¬(-1≤k ∧ k≤1) := by simpa using hk
  simpa [Real.norm_eq_abs,div_eq_mul_inv] using halfWaveCoeff_high (k:=k) (by omega)

private def shiftCoeff (θ : ℝ) (k : ℤ) : ℂ := (halfWaveCoeff (k:ℝ):ℝ) * fourier k ((-θ:ℝ):AddCircle (π- -π))
private theorem shift_norm (θ : ℝ) (k : ℤ) : ‖shiftCoeff θ k‖=|halfWaveCoeff (k:ℝ)| := by
  have h : ‖fourier k ((-θ:ℝ):AddCircle (π- -π))‖ = 1 := Circle.norm_coe _
  simp only [shiftCoeff,norm_mul,h,mul_one,Complex.norm_real,Real.norm_eq_abs]
private theorem shift_summable (θ : ℝ) : Summable (fun k => ‖shiftCoeff θ k‖) := by simpa only [shift_norm] using coeff_summable

private theorem wave_series {N : ℕ} [NeZero N] (w : ℂ) (i : ZMod N) :
    (feature w (gridPoint N ((ZMod.finEquiv N).symm i)):ℂ) = (‖w‖:ℝ)*series (shiftCoeff w.arg) i := by
  let j := (ZMod.finEquiv N).symm i
  let x := physicalAngle j
  let z : AddCircle (π- -π) := ((x-w.arg:ℝ):AddCircle (π- -π))
  have hcoeff : Summable (fourierCoeff wave) :=
    (Complex.ofRealCLM.summable coeff_summable.of_norm).congr (fun k => (wave_coeff k).symm)
  have hs := (has_pointwise_sum_fourier_series_of_summable hcoeff z).tsum_eq
  have hp : feature w (gridPoint N j)=‖w‖*halfWave (x-w.arg) := CircleAngularGeometry.feature_eq w x
  rw [show (feature w (gridPoint N ((ZMod.finEquiv N).symm i)):ℂ) = (‖w‖:ℝ)*(halfWave (x-w.arg):ℂ) by rw [←Complex.ofReal_mul];exact congrArg Complex.ofReal hp]
  congr 1
  rw [←wave_coe,←hs]
  apply tsum_congr
  intro k
  have hgrid : (x:AddCircle (π- -π))=gridAngle i := by
    rw [show i = ZMod.finEquiv N j from ((ZMod.finEquiv N).apply_symm_apply i).symm] at *
    exact (CircleGridSpectrum.gridAngle_fin j).symm
  have hphase : fourier k z=char (k:ZMod N) i*fourier k ((-w.arg:ℝ):AddCircle (π- -π)) := by
    rw [←CircleGridSpectrum.sampled_fourier,←hgrid]
    simp only [z,fourier_coe_apply]
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [wave_coeff,hphase,shiftCoeff,smul_eq_mul]
  ring

private theorem dft_alias {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : Summable (fun k => ‖a k‖)) (r : ZMod N) :
    ZMod.dft (series a) r / (N:ℂ) = ∑' k : ℤ, if (k:ZMod N)=r then a k else 0 := by
  have hh := character_eigenvalue a ha r 0
  simp only [convolution,zero_sub,char,mul_zero,AddChar.map_zero_eq_one,mul_one] at hh
  rw [←hh,ZMod.dft_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun j => by simp [mul_comm,smul_eq_mul])

def envelope (j : ℤ) := 1/(1+|(j:ℝ)|)^2
private theorem envelope_summable : Summable envelope := by
  apply (Real.summable_one_div_int_pow.mpr (by decide : 1<2)).of_norm_bounded_eventually
  filter_upwards [({0}:Finset ℤ).finite_toSet.compl_mem_cofinite] with j hj
  have hc : j≠0 := by simpa using hj
  have hr : (j:ℝ)≠0 := by exact_mod_cast hc
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤envelope j by unfold envelope; positivity)]
  unfold envelope
  apply one_div_le_one_div_of_le (sq_pos_of_ne_zero hr)
  nlinarith [abs_nonneg (j:ℝ),sq_abs (j:ℝ)]

private theorem bound_shift {N : ℕ} {k : ℤ} (hk : 2≤k.natAbs) (hN : k.natAbs≤N) (j : ℤ) :
    |halfWaveCoeff ((k+2*(N:ℤ)*j:ℤ):ℝ)| ≤ 32/(1+|(k:ℝ)|)^2 * envelope j := by
  have kabs : (k.natAbs:ℝ)=|(k:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  have nk : |(k:ℝ)|≤N := by rw [←kabs]; exact_mod_cast hN
  have kh : (2:ℝ)≤|(k:ℝ)| := by rw [←kabs]; exact_mod_cast hk
  let l := k+2*(N:ℤ)*j
  have eql : (l:ℝ) = (k:ℝ)+2*(N:ℝ)*(j:ℝ) := by simp [l]
  have lower : |(k:ℝ)| *(1+|(j:ℝ)|) ≤ 2*|(l:ℝ)| := by
    by_cases hj : j=0
    · simp [l,hj]; linarith
    · have jh : (1:ℝ)≤|(j:ℝ)| := by rw [←Int.cast_abs]; exact_mod_cast Int.add_one_le_iff.mpr (abs_pos.mpr hj)
      have tr := abs_add_le (l:ℝ) (-(k:ℝ))
      rw [show (l:ℝ)+-(k:ℝ)=2*(N:ℝ)*(j:ℝ) by rw [eql];ring,abs_mul,abs_of_nonneg (show (0:ℝ)≤2*N by positivity),abs_neg] at tr
      nlinarith [mul_le_mul_of_nonneg_right nk (abs_nonneg (j:ℝ)),
        mul_nonneg (sub_nonneg.mpr jh) (abs_nonneg (k:ℝ))]
  have ll : |(k:ℝ)| ≤ |(l:ℝ)| := by
    by_cases hj : j=0
    · simp [l,hj]
    · have jh : (1:ℝ)≤|(j:ℝ)| := by rw [←Int.cast_abs]; exact_mod_cast Int.add_one_le_iff.mpr (abs_pos.mpr hj)
      nlinarith [mul_nonneg (sub_nonneg.mpr jh) (abs_nonneg (k:ℝ))]
  have lh : 2≤l.natAbs := by
    exact_mod_cast (show (2:ℝ)≤l.natAbs by rw [Nat.cast_natAbs,Int.cast_abs]; exact kh.trans ll)
  apply (halfWaveCoeff_high lh).trans
  unfold envelope
  have h1 : (1+|(k:ℝ)|)*(1+|(j:ℝ)|) ≤ 4*|(l:ℝ)| := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (show 1≤|(k:ℝ)| by linarith)) (show 0≤1+|(j:ℝ)| by positivity)]
  have hs := pow_le_pow_left₀ (show 0≤(1+|(k:ℝ)|)*(1+|(j:ℝ)|) by positivity) h1 2
  rw [mul_pow,mul_pow,sq_abs] at hs
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (show 0<(l:ℝ)^2 by rw [←sq_abs]; exact sq_pos_of_pos (by linarith)) (by positivity)).mpr
  nlinarith

def aliasCap := 32*∑' j : ℤ, envelope j

private theorem alias_bound {N : ℕ} [NeZero N] (ho : Odd N) (θ : ℝ) {r : ZMod N}
    (hp : r≠1) (hm : r≠ -1) {k : ℤ} (hkr : (k:ZMod N)=r) (he : Even k)
    (hk : 2≤k.natAbs) (hN : k.natAbs≤N) :
    ‖∑' l : ℤ, if (l:ZMod N)=r then shiftCoeff θ l else 0‖ ≤ aliasCap/(1+|(k:ℝ)|)^2 := by
  let f (l : ℤ) : ℂ := if (l:ZMod N)=r then shiftCoeff θ l else 0
  let g (j : ℤ) := k+2*(N:ℤ)*j
  have ng : (N:ℤ)≠0 := by exact_mod_cast NeZero.ne N
  have hg : Function.Injective g := fun i j h => mul_left_cancel₀ (show (2*(N:ℤ))≠0 by positivity) (add_left_cancel h)
  have hs : Function.support f ⊆ Set.range g := by
    intro l hl
    change f l ≠ 0 at hl
    have hr : (l:ZMod N)=r := by by_contra h; exact hl (by simp [f,h])
    have el : Even l := by
      by_contra h
      have ha : l.natAbs≠1 := by
        rintro hu
        rcases (show l=1 ∨ l= -1 by omega) with h1|h1
        · exact hp (by simp [←hr,h1])
        · exact hm (by simp [←hr,h1])
      exact hl (by simp [f,hr,shiftCoeff,halfWaveCoeff_zero h ha])
    have hd : ((l-k:ℤ):ZMod N)=0 := by simp [hr,hkr]
    obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (l-k) N).mp hd
    have hodd : ¬Even (N:ℤ) := by rcases ho with ⟨u,hu⟩;rw [hu];push_cast;rintro ⟨y,hy⟩;omega
    obtain ⟨j,hj⟩ := (Int.even_mul.mp (ha ▸ el.sub he)).resolve_left hodd
    exact ⟨j, by dsimp [g]; rw [hj] at ha; linear_combination -ha⟩
  have fb (j : ℤ) : ‖f (g j)‖ ≤ 32/(1+|(k:ℝ)|)^2 * envelope j := by
    have hr : ((g j:ℤ):ZMod N)=r := by simp [g,hkr]
    simpa [f,hr,shift_norm,g] using bound_shift hk hN j
  have hsum := envelope_summable.mul_left (32/(1+|(k:ℝ)|)^2)
  have habs : Summable (fun j => ‖f (g j)‖) := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fb
  calc
    _ = ‖∑' j : ℤ, f (g j)‖ := congrArg norm (hg.tsum_eq hs).symm
    _ ≤ _ := (norm_tsum_le_tsum_norm habs).trans (habs.tsum_le_tsum fb hsum)
    _ = _ := by rw [tsum_mul_left,aliasCap]; ring

variable {N m : ℕ} [NeZero N]

def unitMode (r : ZMod N) (w : ℂ) : ℂ := ZMod.dft (fun i : ZMod N =>
  (feature w (gridPoint N ((ZMod.finEquiv N).symm i)):ℂ)) r / (N:ℂ)

private theorem fourier_sup (f : ZMod N → ℂ) (r : ZMod N) {B : ℝ} (hb : ∀ i, ‖f i‖≤B) :
    ‖ZMod.dft f r/(N:ℂ)‖ ≤ B := by
  rw [ZMod.dft_apply,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (NeZero.pos N))).mpr
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : ZMod N, B := Finset.sum_le_sum (fun i _ => by simp [AddChar.norm_apply,hb i,smul_eq_mul])
    _ = B*N := by simp [ZMod.card,mul_comm]

theorem unitMode_le (r : ZMod N) (w : ℂ) : ‖unitMode r w‖ ≤ ‖w‖ := by
  apply fourier_sup
  intro i
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
  apply max_le _ (norm_nonneg w)
  simpa only [grid_norm,mul_one] using real_inner_le_norm w (gridPoint N ((ZMod.finEquiv N).symm i))

theorem unitMode_high (ho : Odd N) {r : ZMod N} (hp : r≠1) (hm : r≠ -1) {k : ℤ}
    (hkr : (k:ZMod N)=r) (he : Even k) (hk : 2≤k.natAbs) (hN : k.natAbs≤N) (w : ℂ) :
    ‖unitMode r w‖ ≤ (aliasCap/(1+|(k:ℝ)|)^2)*‖w‖ := by
  have h (i : ZMod N) := wave_series w i
  unfold unitMode
  simp_rw [h]
  rw [show (fun i => (↑‖w‖:ℂ)*series (shiftCoeff w.arg) i) =
    (↑‖w‖:ℂ) • series (shiftCoeff w.arg) from rfl,map_smul]
  change ‖(↑‖w‖:ℂ)*ZMod.dft (series (shiftCoeff w.arg)) r / (N:ℂ)‖ ≤ _
  rw [mul_div_assoc,dft_alias _ (shift_summable _),norm_mul,Complex.norm_real,norm_norm,mul_comm]
  exact mul_le_mul_of_nonneg_right (alias_bound ho w.arg hp hm hkr he hk hN) (norm_nonneg w)

private theorem char_grid (i : ZMod N) : char 1 i = gridPoint N ((ZMod.finEquiv N).symm i) := by
  let j := (ZMod.finEquiv N).symm i
  have h := CircleGridSpectrum.sampled_fourier (N:=N) 1 i
  simp only [Int.cast_one] at h
  rw [←h,←show gridAngle (ZMod.finEquiv N j) = gridAngle i by simp [j],
    CircleGridSpectrum.gridAngle_fin,fourier_coe_apply]
  rw [show 2*(π:ℂ)*Complex.I*(1:ℤ)*(physicalAngle j)/(↑(π- -π):ℂ) = (physicalAngle j:ℂ)*Complex.I by push_cast;field_simp [show (π:ℂ)≠0 by exact_mod_cast pi_ne_zero];ring]
  rw [Complex.exp_mul_I]
  rw [←Complex.ofReal_cos,←Complex.ofReal_sin]
  apply Complex.ext <;> simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im,mul_zero,mul_one,zero_add,add_zero,sub_zero] <;> rfl

private def label (i : ZMod N) : ℂ := (1+(gridPoint N ((ZMod.finEquiv N).symm i)).re : ℝ)
private def labelMode (r : ZMod N) := ZMod.dft (label (N:=N)) r/(N:ℂ)
private theorem labelMode_le (r : ZMod N) : ‖labelMode r‖≤2 := by
  apply fourier_sup
  intro i
  have h := Complex.abs_re_le_norm (gridPoint N ((ZMod.finEquiv N).symm i))
  rw [grid_norm] at h
  unfold label
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact (abs_add_le 1 _).trans (by rw [abs_one];linarith)
private theorem char_dft (p r : ZMod N) : ZMod.dft (char p) r/(N:ℂ) = if p=r then 1 else 0 := by
  rw [ZMod.dft_apply]
  have hc (i : ZMod N) : ZMod.stdAddChar (-(i*r)) • char p i = char (p-r) i := by
    rw [smul_eq_mul,char,char,←AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hc]
  simp [CircleGridSpectrum.char_mean, sub_eq_zero]
private theorem labelMode_zero {r : ZMod N} (hn : r≠0) (hp : r≠1) (hm : r≠ -1) : labelMode r=0 := by
  have hl : label (N:=N) = char 0 + (2:ℂ)⁻¹ • (char 1 + char (-1)) := by
    ext1 i
    have hneg : char (-1) i=conj (char 1 i) := by simp [char,AddChar.map_neg_eq_conj]
    rw [Pi.add_apply,Pi.smul_apply,Pi.add_apply,hneg,char_grid]
    unfold label
    simp only [char,zero_mul,AddChar.map_zero_eq_one,smul_eq_mul,Complex.ofReal_add,Complex.ofReal_one]
    rw [Complex.add_conj]
    push_cast
    ring
  unfold labelMode
  rw [hl,map_add,map_smul,map_add]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_div,mul_div_assoc,char_dft,Ne.symm hn,Ne.symm hp,Ne.symm hm,ite_false,mul_zero,zero_add]

open CircleSharpInitialization CircleInitializationConcentration

private def outMode (r : ZMod N) (ω : Seed m) : ℂ :=
  √(m:ℝ) • ((m:ℝ)⁻¹ • ∑ j : Fin m, ω (j,0) • unitMode r (⟨ω (j,1),ω (j,2)⟩:ℂ))

private theorem raw_decompose (hm : 0<m) (r : ZMod N) (ω : Seed m) :
    initialCoeff N m r ω = outMode r ω-labelMode r := by
  let V (j : Fin m) (i : ZMod N) : ℂ := feature ((initial ω).w j) (gridPoint N ((ZMod.finEquiv N).symm i))
  have x (i : ZMod N) :
      (↑(output (1/√(m:ℝ)) (initial ω) (gridPoint N ((ZMod.finEquiv N).symm i)) -
        (1+(gridPoint N ((ZMod.finEquiv N).symm i)).re)):ℂ) =
      (((↑(1/√(m:ℝ)):ℂ) • (∑ j, (↑(ω (j,0)):ℂ) • V j) - (label (N:=N))) : ZMod N → ℂ) i := by
    simp [output,initial,V,label,Complex.real_smul,Finset.sum_apply]
  unfold initialCoeff
  simp_rw [x]
  rw [map_sub,map_smul,map_sum]
  simp only [map_smul,Pi.sub_apply,Pi.smul_apply,Finset.sum_apply,sub_div,labelMode]
  congr 1
  have hscale : √(m:ℝ)*(m:ℝ)⁻¹=1/√(m:ℝ) := by
    field_simp [show (m:ℝ)≠0 by exact_mod_cast hm.ne',sqrt_ne_zero'.mpr (show 0<(m:ℝ) by exact_mod_cast hm)]
    nlinarith [sq_sqrt (Nat.cast_nonneg m)]
  unfold outMode
  rw [←mul_smul,hscale]
  simp only [Complex.real_smul,unitMode,V,initial,smul_eq_mul,mul_div_assoc,Finset.sum_div]

private theorem unitMode_cont (r : ZMod N) : Continuous (unitMode r) := by
  unfold unitMode
  simp only [ZMod.dft_apply,smul_eq_mul]
  unfold feature
  fun_prop

private theorem mean_zero (F : ℝ×ℝ → ℝ) : (∫ z : Atom, z 0*F (z 1,z 2) ∂atomLaw)=0 := by
  let e := CircleReferenceMoments.split
  change (∫ z, (fun p : ℝ×(ℝ×ℝ) => p.1*F p.2) (e z) ∂atomLaw)=0
  rw [CircleReferenceMoments.split_preserving.integral_comp' (fun p : ℝ×(ℝ×ℝ) => p.1*F p.2),
    integral_prod_mul (fun a : ℝ => a) F,integral_id_gaussianReal,zero_mul]

private theorem component_fourth (hm : 0<m) (r : ZMod N) (p : ℂ →L[ℝ] ℝ) (hp : ∀ z, |p z|≤‖z‖)
    {D : ℝ} (hd : 0<D) (hunit : ∀ w, ‖unitMode r w‖≤D*‖w‖) :
    MemLp (fun ω : Seed m => p (outMode r ω)) 4 (seedLaw m) ∧
    lpNorm (fun ω : Seed m => p (outMode r ω)) 4 (seedLaw m) ≤ markConstant*D := by
  let F (w : ℝ×ℝ) := p (unitMode r (⟨w.1,w.2⟩:ℂ))
  let X (z : Atom) := z 0*F (z 1,z 2)
  have hF : Continuous F := p.continuous.comp ((unitMode_cont r).comp Complex.equivRealProdCLM.symm.continuous)
  have hmX : Measurable X := (measurable_pi_apply _).mul (hF.measurable.comp ((measurable_pi_apply _).prodMk (measurable_pi_apply _)))
  have dom (z : Atom) : |X z|≤D*atomEnergy z := by
    let w : ℂ := ⟨z 1,z 2⟩
    have e : ‖w‖^2=(z 1)^2+(z 2)^2 := by rw [Complex.sq_norm,Complex.normSq_apply];ring
    have hf : |F (z 1,z 2)|≤D*‖w‖ := (hp _).trans (hunit _)
    have zcap : |z 0| * ‖w‖ ≤ atomEnergy z := by
      unfold atomEnergy
      nlinarith [sq_nonneg (|z 0|-‖w‖),sq_abs (z 0),sq_nonneg ‖w‖,sq_nonneg (z 0)]
    rw [show |X z|=|z 0| * |F (z 1,z 2)| from abs_mul _ _]
    calc
      _ ≤ |z 0| *(D*‖w‖) := mul_le_mul_of_nonneg_left hf (abs_nonneg _)
      _ = D*(|z 0| * ‖w‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left zcap hd.le
  have h := average_fourth hm X hmX hd dom
  have eq : (fun ω : Seed m => p (outMode r ω)) = centeredSum X := by
    funext ω
    have hz : (∫ z, X z ∂atomLaw)=0 := mean_zero F
    simp only [outMode, map_smul,map_sum,centeredSum,hz,sub_zero,sampleAverage,F,X,smul_eq_mul]
  rwa [eq]

def modeConstant := 2*markConstant*(1+aliasCap)+2

private theorem out_fourth (hm : 0<m) (r : ZMod N) {D : ℝ} (hd : 0<D)
    (hunit : ∀ w, ‖unitMode r w‖≤D*‖w‖) : MemLp (outMode (m:=m) r) 4 (seedLaw m) ∧
    lpNorm (outMode (m:=m) r) 4 (seedLaw m) ≤ 2*markConstant*D := by
  let A := outMode (m:=m) r
  have hr := component_fourth hm r Complex.reCLM Complex.abs_re_le_norm hd hunit
  have hi := component_fourth hm r Complex.imCLM Complex.abs_im_le_norm hd hunit
  let R (ω : Seed m) := |(A ω).re|
  let I (ω : Seed m) := |(A ω).im|
  have hR : MemLp R 4 (seedLaw m) := hr.1.norm
  have hI : MemLp I 4 (seedLaw m) := hi.1.norm
  have hRI (ω : Seed m) : ‖A ω‖≤(R+I) ω := Complex.norm_le_abs_re_add_abs_im _
  have hmem : MemLp A 4 (seedLaw m) := by
    apply (hR.add hI).mono' _ (ae_of_all _ hRI)
    exact Complex.measurableEquivRealProd.symm.measurable.comp_aemeasurable
      (hr.1.aemeasurable.prodMk hi.1.aemeasurable) |>.aestronglyMeasurable
  refine ⟨hmem,?_⟩
  apply (lpNorm_mono_real (hR.add hI) hRI).trans
  have hh := lpNorm_add_le (g:=I) hR (by norm_num)
  apply hh.trans
  change lpNorm (fun ω : Seed m => |Complex.reCLM (outMode r ω)|) _ _ + lpNorm (fun ω : Seed m => |Complex.imCLM (outMode r ω)|) _ _ ≤ _
  rw [lpNorm_fun_abs hr.1.aestronglyMeasurable,lpNorm_fun_abs hi.1.aestronglyMeasurable]
  linarith [hr.2,hi.2]

private theorem aliasCap_pos : 0<aliasCap := by
  have h := envelope_summable.le_tsum 0 (fun i _ => show 0≤envelope i by unfold envelope; positivity)
  have h0 : envelope 0=1 := by norm_num [envelope]
  rw [h0] at h
  unfold aliasCap
  positivity

private theorem mark_nonneg : 0≤markConstant := by unfold markConstant; positivity

theorem initialCoeff_high (hm : 0<m) (ho : Odd N) {r : ZMod N}
    (h0 : r≠0) (hp : r≠1) (hn : r≠ -1) {k : ℤ} (hkr : (k:ZMod N)=r)
    (he : Even k) (hk : 2≤k.natAbs) (hN : k.natAbs≤N) :
    MemLp (initialCoeff N m r) 4 (seedLaw m) ∧
      lpNorm (initialCoeff N m r) 4 (seedLaw m) ≤ modeConstant/(1+|(k:ℝ)|)^2 := by
  have hD : 0<aliasCap/(1+|(k:ℝ)|)^2 := div_pos aliasCap_pos (by positivity)
  have h := out_fourth hm r hD (unitMode_high ho hp hn hkr he hk hN)
  have hfun : initialCoeff N m r=outMode r := by ext ω:1;rw [raw_decompose hm,labelMode_zero h0 hp hn,sub_zero]
  rw [hfun]
  refine ⟨h.1,h.2.trans ?_⟩
  rw [←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold modeConstant
  nlinarith [mark_nonneg]

/-- Uniform estimate for all modes, including the three deterministic label modes. -/
theorem initialCoeff_uniform (hm : 0<m) (r : ZMod N) : MemLp (initialCoeff N m r) 4 (seedLaw m) ∧
    lpNorm (initialCoeff N m r) 4 (seedLaw m) ≤ modeConstant := by
  have h := out_fourth hm r (by norm_num : (0:ℝ)<1) (fun w => (unitMode_le r w).trans_eq (one_mul _).symm)
  let F := outMode (m:=m) r
  let L (_ : Seed m) := -labelMode r
  have hL : MemLp L 4 (seedLaw m) := memLp_const _
  have heq : initialCoeff N m r = F+L := by funext ω;exact raw_decompose hm r ω
  rw [heq]
  refine ⟨h.1.add hL,(lpNorm_add_le h.1 (by norm_num)).trans ?_⟩
  have hlabel : lpNorm L 4 (seedLaw m) = ‖labelMode r‖ := by simp [L,lpNorm_const' (show (4:ENNReal)≠0 by norm_num) (show (4:ENNReal)≠⊤ by norm_num)]
  rw [hlabel]
  unfold modeConstant
  nlinarith [h.2,labelMode_le r,mul_nonneg mark_nonneg aliasCap_pos.le]

end CircleResidualSpectrum
