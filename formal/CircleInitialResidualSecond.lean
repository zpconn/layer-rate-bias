module

public import CircleActualTracking
public import CircleReferenceMoments
import all CircleReferenceMoments
import all CircleFlowMoments
import all CircleActualTracking
import all CircleTangentDrift
import all CircleInitializationConcentration
import all CircleKernelIdentification
import all CircleGridSpectrum
import all CircleFlowPath
import all CircleEscapeBridge
import all CircleEscape
import Mathlib.Tactic

/-! Exact mean square of the Gaussian initial residual on the training circle. -/
@[expose] public section
noncomputable section
namespace CircleInitialResidualSecond
open Real ProbabilityTheory MeasureTheory CircleInitializationConcentration CircleReferenceMoments
  CircleKernelIdentification CircleGridSpectrum CircleFlowPath CircleEscapeBridge CircleActualTracking CircleTangentDrift
variable {N m : ℕ}

private def term (u : ℝ) (z : Atom) := z 0*phi u (z 1,z 2)

private theorem term_moments (u : ℝ) :
    MemLp (term u) 2 atomLaw ∧ (∫ z, term u z ∂atomLaw)=0 ∧ variance (term u) atomLaw=1/2 := by
  have ha : MemLp (fun z : ℝ×(ℝ×ℝ) => z.1) 4 (G.prod standardPair) :=
    (memLp_id_gaussianReal 4).comp_measurePreserving measurePreserving_fst
  have hb : MemLp (fun z : ℝ×(ℝ×ℝ) => phi u z.2) 4 (G.prod standardPair) :=
    (phi_mem 4 u).comp_measurePreserving measurePreserving_snd
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)];norm_num⟩
  have hi : MemLp (term u) 2 atomLaw := (ha.fun_mul hb).comp_measurePreserving CircleReferenceMoments.split_preserving
  have mean : (∫ z, term u z ∂atomLaw)=0 := by
    change (∫ z, (fun p : ℝ×(ℝ×ℝ) => p.1*phi u p.2) (CircleReferenceMoments.split z) ∂atomLaw)=0
    rw [CircleReferenceMoments.split_preserving.integral_comp' (fun p : ℝ×(ℝ×ℝ) => p.1*phi u p.2),
      integral_prod_mul (fun a : ℝ => a) (phi u),integral_id_gaussianReal,zero_mul]
  refine ⟨hi,mean,?_⟩
  rw [variance_eq_sub hi,mean]
  simp only [Pi.pow_apply,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,sub_zero]
  change (∫ z, (fun p : ℝ×(ℝ×ℝ) => (p.1*phi u p.2)^2) (CircleReferenceMoments.split z) ∂atomLaw)=_
  rw [CircleReferenceMoments.split_preserving.integral_comp' (fun p : ℝ×(ℝ×ℝ) => (p.1*phi u p.2)^2)]
  simp_rw [mul_pow]
  rw [integral_prod_mul (fun a : ℝ => a^2) (fun w => phi u w^2),CircleKernelIdentification.gaussian_second,one_mul]
  have h := cartesian_kernel_isotropic 0 u u
  rw [sub_self,abs_zero,polarNTK,angular_covariance 0 le_rfl pi_pos.le] at h
  have half : π/(2*π) = 1/2 := by field_simp
  simpa [phi,cartesianKernel,cartesianProduct,sq,half] using h

def prediction (N m : ℕ) (i : Fin N) (z : Seed m) := output (1/√m) z (circleInput N i)

/-- Pointwise prediction on every training node has zero mean and variance one half. -/
theorem prediction_moments (hm : 0<m) (i : Fin N) :
    MemLp (prediction N m i) 2 (seedLaw m) ∧ (∫ z, prediction N m i z ∂seedLaw m)=0 ∧
    (∫ z, (prediction N m i z)^2 ∂seedLaw m)=1/2 := by
  let f := term (physicalAngle i)
  have a := term_moments (physicalAngle i)
  have hm' : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hs : √(m:ℝ)≠0 := sqrt_ne_zero'.mpr (by exact_mod_cast hm)
  have scale : √(m:ℝ)*(m:ℝ)⁻¹ = 1/√(m:ℝ) := by
    field_simp [hs,hm']; nlinarith [sq_sqrt (Nat.cast_nonneg m)]
  have id : prediction N m i = fun z => √m*sampleAverage f z := by
    ext z
    rw [prediction,CircleFlowMoments.output_eq_complex,CircleEscape.output,sampleAverage,←mul_assoc,scale]
    congr 1
    simp only [term,f,initial,feature_coord]
  have m₂ : MemLp (prediction N m i) 2 (seedLaw m) := id ▸ (average_mem (m:=m) a.1).const_mul _
  have mean : (∫ z, prediction N m i z ∂seedLaw m)=0 := by
    rw [id,integral_const_mul,average_mean hm a.1,a.2.1,mul_zero]
  have v : variance (prediction N m i) (seedLaw m) = 1/2 := by
    rw [id,variance_const_mul,average_variance hm a.1,a.2.2,sq_sqrt (Nat.cast_nonneg m)]
    field_simp
  rw [variance_eq_sub m₂,mean] at v
  exact ⟨m₂,mean,by simpa using v⟩

private def raw (N m : ℕ) (i : Fin N) (z : Seed m) := prediction N m i z - circleLabel N i

private theorem raw_sq (hm : 0<m) (i : Fin N) :
    Integrable (fun z => (raw N m i z)^2) (seedLaw m) ∧
    (∫ z, (raw N m i z)^2 ∂seedLaw m)=1/2+(circleLabel N i)^2 := by
  have a := prediction_moments hm i
  have hi : MemLp (raw N m i) 2 (seedLaw m) := a.1.sub (memLp_const _)
  refine ⟨hi.integrable_sq,?_⟩
  have eq (z : Seed m) : (raw N m i z)^2 =
      (prediction N m i z)^2 - (2*circleLabel N i)*prediction N m i z + (circleLabel N i)^2 := by
    unfold raw;ring
  simp_rw [eq]
  have hi' := (a.1.integrable (by norm_num)).const_mul (2*circleLabel N i)
  have subint : Integrable (fun z => (prediction N m i z)^2-(2*circleLabel N i)*prediction N m i z) (seedLaw m) := a.1.integrable_sq.sub hi'
  rw [integral_add subint (integrable_const _),integral_sub a.1.integrable_sq hi',
    integral_const_mul,a.2.2,a.2.1,integral_const];simp

theorem residual_second (hn : 3≤N) (hm : 0<m) :
    Integrable (fun z : Seed m => ‖gridR N z‖^2) (seedLaw m) ∧
    (∫ z : Seed m, ‖gridR N z‖^2 ∂seedLaw m)=2 := by
  have eq (z : Seed m) : ‖gridR N z‖^2 = (∑ i, (raw N m i z)^2)/N := rmsCoordinates_norm_sq _
  have hp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  simp_rw [eq]
  constructor
  · exact (integrable_finsetSum _ (fun i _ => (raw_sq hm i).1)).div_const _
  · rw [integral_div,integral_finsetSum _ (fun i _ => (raw_sq hm i).1)]
    simp_rw [(raw_sq hm _).2]
    rw [Finset.sum_add_distrib,add_div]
    have h := circle_teacher_square hn
    rw [one_div,←div_eq_inv_mul] at h
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,h]
    field_simp;ring

/-- Markov failure probability for the norm of the actual initial grid residual. -/
theorem residual_tail (hn : 3≤N) (_odd : Odd N) (hm : 0<m) {R : ℝ} (hR : 0<R) :
    (seedLaw m).real {z | R < ‖gridR N z‖} ≤ 2/R^2 := by
  have r := residual_second hn hm
  have ub := mul_meas_ge_le_integral_of_nonneg (μ:=seedLaw m) (f:=fun z => ‖gridR N z‖^2)
    (ae_of_all _ fun z => sq_nonneg _) r.1 (R^2)
  rw [r.2] at ub
  apply (measureReal_mono (s₂:={z : Seed m | R^2≤‖gridR N z‖^2}) (fun z hz =>
    pow_le_pow_left₀ hR.le (le_of_lt hz) 2)).trans
  exact (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by rwa [mul_comm])

end CircleInitialResidualSecond
