module
public import CirclePairedOrdering
public import CircleMajorityLimit
public import CircleFourthSmallBall
import all CircleFourthSmallBall
import all CircleScoreMargin
import all CircleFlowPath
import all CircleEscapeBridge
import all CircleGaussianCDF
import all CirclePairedOrdering
import all CircleReferenceMoments
import all CircleMajorityCF
import all CircleKernelIdentification
import all CircleInitializationConcentration
import CircleReferenceKurtosis
import Mathlib.Tactic

/-! A uniform positive Gaussian mass for each fixed initial grid-score margin. -/
@[expose] public section
noncomputable section
namespace CircleMarginMass
open MeasureTheory ProbabilityTheory Real Set Filter Topology CircleInitializationConcentration
 CircleEscapeBridge CircleKernelIdentification CircleReferenceMoments CircleFourthSmallBall CircleSpectrum
 CircleGaussianCDF
open scoped ENNReal

private def feature (N : ℕ) (x : Layer 2) := gridFeature N (x 0,x 1)

private theorem feature_meas (N : ℕ) : Measurable (feature N) := by
  unfold feature gridFeature phi projection; fun_prop

private theorem feature_sq {N : ℕ} (hn : 0<N) (x : Layer 2) :
    feature N x^2≤x 0^2+x 1^2 := by
  let r := sqrt (x 0^2+x 1^2)
  have r0 : 0≤r := sqrt_nonneg _
  have r2 : r^2=x 0^2+x 1^2 := sq_sqrt (by positivity)
  have bound (u : ℝ) : phi u (x 0,x 1) ≤ r := by
    apply max_le _ r0
    change x 0*cos u+x 1*sin u≤r
    have e : (x 0*cos u+x 1*sin u)^2+(x 0*sin u-x 1*cos u)^2=x 0^2+x 1^2 := by
      linear_combination (x 0^2+x 1^2)*sin_sq_add_cos_sq u
    nlinarith [sq_nonneg (x 0*sin u-x 1*cos u)]
  have np : (0:ℝ)<N := by exact_mod_cast hn
  have h : feature N x ≤ r := by
    apply (div_le_iff₀ np).mpr
    simpa [mul_comm] using Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin N) _ => bound (CircleGridSpectrum.physicalAngle i))
  have h0 : 0≤feature N x := div_nonneg (Finset.sum_nonneg fun _ _ => le_max_right _ _) np.le
  exact (pow_le_pow_left₀ h0 h 2).trans_eq r2

private theorem feature_second (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) :
    c0≤∫ x, feature (n+1) x^2 ∂layerLaw 2 := by
  have mp : MeasurePreserving (fun x : Layer 2 => (x 0,x 1)) (layerLaw 2) standardPair :=
    measurePreserving_finTwoArrow _
  rw [show (∫ x, feature (n+1) x^2 ∂layerLaw 2) = ∫ w, gridFeature (n+1) w^2 ∂standardPair from
    mp.hasLaw.integral_comp (f:=fun w => gridFeature (n+1) w^2) (by unfold gridFeature phi projection; fun_prop),
    grid_second hn ho]
  exact le_add_of_nonneg_right ((by positivity : 0≤1/(4*π^2*((n:ℝ)+1)^4)).trans (CircleReferenceKurtosis.S_lower n))

private theorem normal_pos (t : ℝ) : 0<normalCDF t := by
  let : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    ⟨fun U ho ne he => ho.measure_ne_zero volume ne ((gaussianReal_absolutelyContinuous' 0 (by norm_num)) he)⟩
  apply lt_of_lt_of_le (ENNReal.toReal_pos (isOpen_Iio.measure_ne_zero (gaussianReal 0 1) (nonempty_Iio (a:=t))) (measure_ne_top _ _))
  exact measureReal_mono (μ:=gaussianReal 0 1) (Iio_subset_Iic_self (a:=t))

/-- Lower bound for a one-sided grid-mean tail and hence for the two-sided score margin. -/
def marginFloor (γ : ℝ) := normalCDF (-γ / sqrt (c0/2))/2

theorem marginFloor_eq (γ : ℝ) : marginFloor γ = normalCDF (-(π*γ))/2 := by
  have sp : sqrt (c0/2)=π⁻¹ := by
    apply (sq_eq_sq₀ (sqrt_nonneg _) (inv_nonneg.mpr pi_pos.le)).mp
    rw [sq_sqrt (by unfold c0; positivity)]
    unfold c0; field_simp
  rw [marginFloor,sp,div_inv_eq_mul,neg_mul,mul_comm γ π]

theorem marginFloor_pos (γ : ℝ) : 0<marginFloor γ := half_pos (normal_pos _)

theorem margin_mass {n m : ℕ} (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m)
    (large : 30≤(m:ℝ)*(c0/2)^2) {γ : ℝ} (hγ : 0≤γ) :
    marginFloor γ ≤ (seedLaw m).real {z | γ≤|CirclePairedCoefficient.score (n+1) m z|} := by
  let V := feature (n+1)
  let q := c0/2
  let p := normalCDF (-γ/sqrt q)
  have qp : 0<q := by dsimp [q,c0]; positivity
  have pp : 0≤p := measureReal_nonneg
  have vm : Measurable V := feature_meas _
  let E := {h : Hidden m | q≤empirical V h}
  have em : Measurable (empirical (m:=m) V) :=
    Finset.measurable_fun_sum _ fun j _ => (coeff_joint vm j).pow_const 2
  have me : MeasurableSet E := measurableSet_le measurable_const em
  have hs : MeasurePreserving (fun z => (splitLayer m z).2) (seedLaw m) (hiddenLaw m) :=
    measurePreserving_snd.comp (CircleInitializationConcentration.split_preserving m)
  have bad := raw_lower_tail hm vm (feature_sq (by omega)) (c:=c0) (by unfold c0; positivity) (feature_second n hn ho)
  have he : ((fun z => (splitLayer m z).2) ⁻¹' Eᶜ) = {z | sampleAverage (CircleFourthSmallBall.single V) z < q} := by
    ext z; simp [E,empirical_split]
  have hmass : 1/2≤(hiddenLaw m).real E := by
    rw [←sub_le_sub_iff_left (a:=(1:ℝ)),←probReal_compl_eq_one_sub me,←hs.measureReal_preimage me.compl.nullMeasurableSet,he]
    exact bad.trans (by dsimp only [q] at *; rw [div_le_iff₀ (by positivity : 0<(m:ℝ)*(c0/2)^2)]; linarith)
  let A := {v : Layer m × Hidden m | linearReadout (coeff V v.2) v.1 ≤ -γ}
  have rm : Measurable (fun v : Layer m × Hidden m => linearReadout (coeff V v.2) v.1) :=
    Finset.measurable_fun_sum _ fun j _ => ((coeff_joint vm j).comp measurable_snd).mul
      ((measurable_pi_apply j).comp measurable_fst)
  have ma : MeasurableSet A := measurableSet_le rm measurable_const
  have fiber (h : Hidden m) (hh : h∈E) :
      ENNReal.ofReal p ≤ layerLaw m ((fun a => (a,h)) ⁻¹' A) := by
    change _ ≤ layerLaw m {a | linearReadout (coeff V h) a ∈ Iic (-γ)}
    rw [(linearReadout_law (coeff V h)).measure_eq (p:=fun x => x∈Iic (-γ)) measurableSet_Iic]
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
    rw [ENNReal.toReal_ofReal pp]
    change p ≤ varianceCDF (empirical V h) (-γ)
    rw [scale _ _ (qp.trans_le hh)]
    apply measureReal_mono (Iic_subset_Iic.mpr _)
    rw [neg_div,neg_div]; exact neg_le_neg (div_le_div_of_nonneg_left hγ (sqrt_pos.mpr qp) (sqrt_le_sqrt hh))
  have lb : ENNReal.ofReal p * hiddenLaw m E ≤ (layerLaw m).prod (hiddenLaw m) A := by
    rw [Measure.prod_apply_symm ma,←setLIntegral_const,←lintegral_indicator me]
    exact lintegral_mono fun h => by
      by_cases hh : h∈E
      · simpa only [indicator_of_mem hh] using fiber h hh
      · simp [indicator_of_notMem hh]
  have read (z : Seed m) : CircleScoreMargin.gridMean (n+1) m z = readout V z := CircleMajorityCF.gridMean_eq_sum _ _ _
  have incl : splitLayer m ⁻¹' A ⊆ {z | γ≤|CirclePairedCoefficient.score (n+1) m z|} := by
    intro z hz
    have hz' : readout V z≤ -γ := (readout_split V z) ▸ hz
    change γ ≤ |CirclePairedCoefficient.score (n+1) m z|
    rw [CirclePairedOrdering.score_eq,read]
    exact (by linarith : γ≤1-readout V z).trans (le_abs_self _)
  apply le_trans _ (measureReal_mono incl)
  rw [(CircleInitializationConcentration.split_preserving m).measureReal_preimage ma.nullMeasurableSet]
  have z := ENNReal.toReal_mono (measure_ne_top _ _) lb
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal pp] at z
  apply le_trans _ z
  simpa [marginFloor,p,q,div_eq_mul_inv,Measure.real] using mul_le_mul_of_nonneg_left hmass pp

/-- Every fixed margin already occurs at each positive finite width and grid size. -/
theorem finite_margin_positive {N m : ℕ} (hN : 0<N) (hm : 0<m) (γ : ℝ) :
    0 < (seedLaw m).real {z | γ≤|CirclePairedCoefficient.score N m z|} := by
  let : NeZero N := ⟨hN.ne'⟩
  let V := feature N
  let x : Layer 2 := ![1,0]
  have vpos : 0<V x := by
    apply div_pos _ (by exact_mod_cast hN)
    apply Finset.sum_pos' (fun _ _ => le_max_right _ _)
    refine ⟨(0 : Fin N),Finset.mem_univ _,?_⟩
    norm_num [phi,projection,CircleGridSpectrum.physicalAngle,x]
  let k := (1/sqrt m)*(m:ℝ)*V x
  have kp : 0<k := by dsimp only [k]; positivity
  let a := -(γ+1)/k
  let z : Seed m := fun p => if p.2=0 then a else if p.2=1 then 1 else 0
  have mean : CircleScoreMargin.gridMean N m z = -(γ+1) := by
    rw [CircleMajorityCF.gridMean_eq_sum]
    have atom (j : Fin m) : CircleMajorityCF.single N (currySeed m z j) = a*V x := by
      change z (j,0)*gridFeature N (z (j,1),z (j,2))=a*gridFeature N (1,0)
      norm_num [z]
    simp only [atom,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    calc _ = a*k := by dsimp only [k]; ring
         _ = _ := div_mul_cancel₀ _ kp.ne'
  let A := {w : Seed m | CircleScoreMargin.gridMean N m w < -γ}
  have mc : Continuous (CircleScoreMargin.gridMean N m) := by
    unfold CircleScoreMargin.gridMean CircleFlowPath.output CircleFlowPath.pre; fun_prop
  have mo : IsOpen A := isOpen_lt mc continuous_const
  have ne : A.Nonempty := ⟨z,show CircleScoreMargin.gridMean N m z < -γ by rw [mean];linarith⟩
  let : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    ⟨fun U ho hn he => ho.measure_ne_zero volume hn ((gaussianReal_absolutelyContinuous' 0 (by norm_num)) he)⟩
  let : Measure.IsOpenPosMeasure (seedLaw m) := by unfold seedLaw; infer_instance
  apply (ENNReal.toReal_pos (mo.measure_ne_zero (seedLaw m) ne) (measure_ne_top _ _)).trans_le
  apply measureReal_mono (μ:=seedLaw m) (h₂:=measure_ne_top _ _)
  intro w hw
  change γ≤|CirclePairedCoefficient.score N m w|
  rw [CirclePairedOrdering.score_eq]
  exact (by change CircleScoreMargin.gridMean N m w < -γ at hw; linarith : γ≤1-CircleScoreMargin.gridMean N m w).trans (le_abs_self _)

theorem schedule_mass {γ : ℝ} (hg : 0≤γ) :
    ∀ᶠ n : ℕ in atTop, ∀ _ho : Odd (n+1),
      marginFloor γ ≤ (seedLaw ((n+1)^32)).real {z | γ≤|CirclePairedCoefficient.score (n+1) ((n+1)^32) z|} := by
  have hq : 0<(c0/2)^2 := by unfold c0; positivity
  have hn := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop (30/(c0/2)^2))
  filter_upwards [hn,eventually_ge_atTop 3] with n hn h3 ho
  apply margin_mass (by omega) ho (by positivity) _ hg
  have b : (n:ℝ)≤((n+1:ℕ):ℝ)^32 := by
    push_cast; exact (by linarith : (n:ℝ)≤(n:ℝ)+1).trans (le_self_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) n]) (by norm_num))
  push_cast at *
  exact (div_le_iff₀ hq).mp (hn.trans b)
end CircleMarginMass
