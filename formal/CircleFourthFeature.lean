module

public import CircleFourthSmallBall
import all CircleFourthSmallBall
public import CircleFourthEigen
public import CircleResidualSpectrum
import all CircleResidualSpectrum
import all CircleSpectralPathLength
import all CircleSpectrum
import all CircleGridSpectrum
import all CircleEscape
import all CircleEscapeBridge
import all CircleInitializationConcentration
import Mathlib.Tactic

/-! The actual residual's fourth real Fourier mode under Gaussian initialization. -/
public section
noncomputable section
namespace CircleFourthFeature
open Real MeasureTheory ProbabilityTheory Set Finset Filter Topology
  CircleResidualSpectrum CircleInitializationConcentration CircleGridSpectrum CircleSpectrum CircleEscapeBridge
variable {N m : ℕ} [NeZero N]

def feature4 (N : ℕ) [NeZero N] (x : Layer 2) : ℝ := (unitMode (4:ZMod N) (⟨x 0,x 1⟩:ℂ)).re

private theorem mk_cont : Continuous (fun x : Layer 2 => (⟨x 0,x 1⟩:ℂ)) :=
  Complex.equivRealProdCLM.symm.continuous.comp (show Continuous (fun x : Layer 2 => (x 0,x 1)) by fun_prop)

theorem feature4_continuous (N : ℕ) [NeZero N] : Continuous (feature4 N) :=
  Complex.continuous_re.comp ((unitMode_cont _).comp mk_cont)

theorem feature4_sq (N : ℕ) [NeZero N] (x : Layer 2) : (feature4 N x)^2≤(x 0)^2+(x 1)^2 := by
  have h := (Complex.abs_re_le_norm _).trans (unitMode_le (4:ZMod N) (⟨x 0,x 1⟩:ℂ))
  have h' := pow_le_pow_left₀ (abs_nonneg _) h 2
  rwa [sq_abs,Complex.sq_norm,Complex.normSq_apply,←sq,←sq] at h'

theorem feature4_sq_integrable (N : ℕ) [NeZero N] : Integrable (fun x => feature4 N x^2) (layerLaw 2) := by
  have coord (i : Fin 2) := (memLp_id_gaussianReal' (μ:=0) (v:=1) 2 (by norm_num)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) i)
  have hI (i : Fin 2) : Integrable (fun x : Layer 2 => x i^2) (layerLaw 2) := by
    simpa [layerLaw,Real.norm_eq_abs,sq_abs] using (coord i).integrable_norm_pow (by decide : 2≠0)
  exact (hI 0 |>.add (hI 1)).mono' (((feature4_continuous N).pow 2).aestronglyMeasurable)
    (ae_of_all _ fun x => by change |feature4 N x^2|≤(x 0)^2+(x 1)^2; rw [abs_of_nonneg (sq_nonneg _)]; exact feature4_sq N x)

private theorem unit_lip (r : ZMod N) (v w : ℂ) : ‖unitMode r v-unitMode r w‖≤‖v-w‖ := by
  let f (v : ℂ) (i : ZMod N) : ℂ := CircleEscape.feature v (CircleEscape.gridPoint N ((ZMod.finEquiv N).symm i))
  change ‖ZMod.dft (f v) r/N - ZMod.dft (f w) r/N‖≤_
  rw [←sub_div,←Pi.sub_apply,←map_sub]
  apply fourier_sup
  intro i
  let x := CircleEscape.gridPoint N ((ZMod.finEquiv N).symm i)
  change ‖(CircleEscape.feature v x:ℂ)-(CircleEscape.feature w x:ℂ)‖≤_
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  apply (abs_max_sub_max_le_abs _ _ _).trans
  rw [←inner_sub_left]
  simpa only [x,CircleEscape.grid_norm,mul_one] using (abs_real_inner_le_norm (v-w) x)

private theorem mode_at_axis (N : ℕ) [NeZero N] :
    unitMode (4:ZMod N) (1:ℂ)=∑' j : ℤ, if (j:ZMod N)=4 then shiftCoeff 0 j else 0 := by
  have h (i : ZMod N) := wave_series (1:ℂ) i
  simp only [norm_one,Complex.arg_one,Complex.ofReal_one,one_mul] at h
  unfold unitMode
  simp_rw [h]
  exact dft_alias _ (shift_summable 0) _

def limitAmplitude := 1/(15*π)
theorem limitAmplitude_pos : 0<limitAmplitude := by unfold limitAmplitude;positivity

private theorem fourth_coeff : (shiftCoeff 0 4).re = -limitAmplitude := by
  simp only [shiftCoeff,neg_zero,AddCircle.coe_zero]
  have h := halfWaveCoeff_even 2
  norm_num at h
  unfold limitAmplitude
  norm_num
  rw [h]
  ring

private def patch := {x : Layer 2 | ‖(⟨x 0,x 1⟩:ℂ)-1‖<limitAmplitude/4}

private theorem patch_positive : 0<(layerLaw 2).real patch := by
  let : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    ⟨fun U ho ne he => ho.measure_ne_zero volume ne ((gaussianReal_absolutelyContinuous' 0 (by norm_num)) he)⟩
  let : Measure.IsOpenPosMeasure (layerLaw 2) := by unfold layerLaw;infer_instance
  have ho : IsOpen patch := isOpen_lt ((mk_cont.sub continuous_const).norm) continuous_const
  have hx : (![1,0] : Layer 2)∈patch := by
    change ‖(⟨1,0⟩:ℂ)-1‖<limitAmplitude/4
    rw [show (⟨1,0⟩:ℂ)=1 from rfl,sub_self,norm_zero]
    linarith [limitAmplitude_pos]
  exact ENNReal.toReal_pos (ho.measure_ne_zero (layerLaw 2) ⟨_,hx⟩) (measure_ne_top _ _)

def varianceFloor := (layerLaw 2).real patch*(limitAmplitude/2)^2

theorem varianceFloor_pos : 0<varianceFloor := mul_pos patch_positive (sq_pos_of_pos (by linarith [limitAmplitude_pos]))

private theorem feature4_second_of_axis (h : (unitMode (4:ZMod N) (1:ℂ)).re ≤ -(3*limitAmplitude/4)) :
    varianceFloor ≤ ∫ x, feature4 N x^2 ∂layerLaw 2 := by
  have hpatch : MeasurableSet patch := (isOpen_lt ((mk_cont.sub continuous_const).norm) continuous_const).measurableSet
  have b (x : Layer 2) (hx : x∈patch) : (limitAmplitude/2)^2≤feature4 N x^2 := by
    have hp := (Complex.abs_re_le_norm ((unitMode (4:ZMod N) (⟨x 0,x 1⟩:ℂ))-unitMode 4 1)).trans (unit_lip _ _ _)
    rw [Complex.sub_re] at hp
    change ‖(⟨x 0,x 1⟩:ℂ)-1‖<limitAmplitude/4 at hx
    have ha : feature4 N x ≤ -limitAmplitude/2 := by
      unfold feature4
      linarith [le_abs_self ((unitMode (4:ZMod N) (⟨x 0,x 1⟩:ℂ)).re-(unitMode (4:ZMod N) 1).re)]
    have hp := sq_le_sq₀ (show 0≤limitAmplitude/2 by linarith [limitAmplitude_pos]) (show 0≤ -feature4 N x by linarith [limitAmplitude_pos]) |>.2
      (show limitAmplitude/2≤ -feature4 N x by linarith)
    simpa only [neg_sq] using hp
  rw [varianceFloor,←smul_eq_mul,←setIntegral_const]
  exact (setIntegral_mono_on (integrable_const _).integrableOn (feature4_sq_integrable N).integrableOn hpatch b).trans
    (setIntegral_le_integral (feature4_sq_integrable N) (ae_of_all _ (fun x => sq_nonneg _)))

theorem feature4_second_eventually : ∀ᶠ n : ℕ in atTop,
    varianceFloor ≤ ∫x,feature4 (n+1) x^2 ∂layerLaw 2 := by
  have grows : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_atTop_mono (f:=id) (fun n : ℕ => Nat.le_succ n) tendsto_id
  have h := (CircleFourthEigen.complex_alias_limit (shiftCoeff 0) (shift_summable 0) 4).comp grows
  have h' : Tendsto (fun n : ℕ => unitMode (4:ZMod (n+1)) (1:ℂ)) atTop (𝓝 (shiftCoeff 0 4)) := by
    convert h using 1
    funext n; simpa only [Function.comp_apply,Int.cast_ofNat] using mode_at_axis (n+1)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h'
  rw [fourth_coeff] at hr
  have near := hr.eventually (eventually_le_nhds (show -limitAmplitude < -(3*limitAmplitude/4) by linarith [limitAmplitude_pos]))
  filter_upwards [near] with n hn
  exact feature4_second_of_axis hn

omit [NeZero N] in
theorem no_teacher_four (hn : 9<N) : (4:ZMod N)≠0 ∧ (4:ZMod N)≠1 ∧ (4:ZMod N)≠ -1 := by
  have notzero (k : ℕ) (hp : 0<k) (hk : k<N) : (k:ZMod N)≠0 := by
    exact fun hh => (Nat.not_dvd_of_pos_of_lt hp hk) ((ZMod.natCast_eq_zero_iff _ _).mp hh)
  refine ⟨notzero 4 (by decide) (by omega),?_,?_⟩
  · intro hh
    exact notzero 3 (by decide) (by omega) (by change (3:ZMod N)=0;linear_combination hh)
  · intro hh
    exact notzero 5 (by decide) (by omega) (by change (5:ZMod N)=0;linear_combination hh)

theorem actual_fourth (hn : 9<N) (hm : 0<m) (ω : Seed m) :
    (initialCoeff N m (4:ZMod N) ω).re = (1/√(m:ℝ))*
      ∑ j, (splitLayer m ω).1 j*feature4 N (fun i => (splitLayer m ω).2 i j) := by
  obtain ⟨z,o,neg⟩ := no_teacher_four hn
  rw [raw_decompose hm,labelMode_zero z o neg,sub_zero]
  change (outMode (4:ZMod N) ω).re = (1/√(m:ℝ))*∑ j, ω (j,0)*(unitMode (4:ZMod N) (⟨ω (j,1),ω (j,2)⟩:ℂ)).re
  rw [outMode]
  simp only [Complex.smul_re,smul_eq_mul,Complex.re_sum]
  have h0 : 0<√(m:ℝ) := by positivity
  have hh : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  field_simp
  rw [sq_sqrt (Nat.cast_nonneg (α:=ℝ) m)]

/-- Uniform small-ball probability for the actual initialization and width schedule. -/
def smallBallConstant := 2/√(varianceFloor/2)+15/(varianceFloor/2)^2

theorem fourth_small_ball (hn : 9<N) (hm : 0<m)
    (lower : varianceFloor≤∫x,feature4 N x^2 ∂layerLaw 2) {δ : ℝ} (hd : 0≤δ) :
    (seedLaw m).real {ω | |(initialCoeff N m (4:ZMod N) ω).re|≤δ} ≤
      2*δ/√(varianceFloor/2)+15/((m:ℝ)*(varianceFloor/2)^2) := by
  have eq (ω : Seed m) : (initialCoeff N m (4:ZMod N) ω).re = CircleFourthSmallBall.readout (feature4 N) ω := by
    rw [actual_fourth hn hm]
    rfl
  simp_rw [eq]
  exact CircleFourthSmallBall.readout_small_ball hm (feature4_continuous N).measurable (feature4_sq N)
    varianceFloor_pos lower hd

theorem fourth_small_ball_schedule (hn : 9<N) (lower : varianceFloor≤∫x,feature4 N x^2 ∂layerLaw 2) :
    (seedLaw (N^32)).real {ω | |(initialCoeff N (N^32) (4:ZMod N) ω).re|≤1/(N:ℝ)} ≤
      smallBallConstant/(N:ℝ) := by
  have np : 0<(N:ℝ) := by exact_mod_cast (NeZero.pos N)
  have one : 1≤(N:ℝ) := by exact_mod_cast (NeZero.pos N)
  have pw : (N:ℝ)≤N^32 := (pow_one _).symm.trans_le (pow_le_pow_right₀ one (by decide : 1≤32))
  have fc := varianceFloor_pos
  apply (fourth_small_ball hn (pow_pos (NeZero.pos _) _) lower (δ:=1/(N:ℝ)) (by positivity)).trans
  push_cast
  unfold smallBallConstant
  calc
    _ ≤ 2*(1/(N:ℝ))/√(varianceFloor/2)+15/((N:ℝ)*(varianceFloor/2)^2) :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul_of_nonneg_right pw (sq_nonneg _)))
    _ = _ := by ring

theorem fourth_small_ball_eventually : ∀ᶠ n : ℕ in atTop,
    (seedLaw ((n+1)^32)).real {ω | |(initialCoeff (n+1) ((n+1)^32) (4:ZMod (n+1)) ω).re|≤1/((n:ℝ)+1)} ≤
      smallBallConstant/((n:ℝ)+1) := by
  filter_upwards [feature4_second_eventually,eventually_ge_atTop 10] with n hl hn
  simpa only [Nat.cast_add,Nat.cast_one] using fourth_small_ball_schedule (N:=n+1) (by omega) hl

end CircleFourthFeature
