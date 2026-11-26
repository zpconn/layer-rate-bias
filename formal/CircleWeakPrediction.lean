module
public import CircleGaussianLimit
import Mathlib.Probability.CDF
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import all CircleGDLimits
import all CircleConditioning
import all CircleCapMoments
import all CircleGaussianLimit
import all CircleGaussianCDF
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-! Weak convergence of the prediction laws, including the standardized
difference of two independently initialized predictions. -/
public section
noncomputable section
namespace CircleWeakPrediction
open Filter Topology Real Set MeasureTheory ProbabilityTheory CircleEscapeBridge CircleGaussianCDF
  CircleGaussianLimit CircleReferenceDistribution
open scoped NNReal ENNReal

/-- Convergence of the ordinary CDF at every point implies weak convergence
in Mathlib's topology on real probability measures. -/
theorem weak_of_cdf (μ : ℕ→ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (h : ∀ t : ℝ, Tendsto (fun i => (μ i : Measure ℝ).real (Iic t)) atTop
      (𝓝 ((ν : Measure ℝ).real (Iic t)))) : Tendsto μ atTop (𝓝 ν) := by
  apply (isPiSystem_Ioc (id : ℝ→ℝ) id).tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a,b,hab,rfl⟩
    exact measurableSet_Ioc
  · intro U hU x hx
    obtain ⟨l,u,⟨hl,hr⟩,hu⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
    obtain ⟨r,hxr,hru⟩ := exists_between hr
    refine ⟨Ioc l r,⟨l,r,hl.trans hxr,rfl⟩,?_,(Ioc_subset_Ioo_right hru).trans hu⟩
    exact Filter.mem_of_superset (Ioo_mem_nhds hl hxr) Ioo_subset_Ioc_self
  · rintro s ⟨a,b,hab,rfl⟩
    change a<b at hab
    apply NNReal.tendsto_coe.mp
    simp only [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
    have eq (ρ : ProbabilityMeasure ℝ) : (ρ : Measure ℝ).real (Ioc a b) =
        (ρ : Measure ℝ).real (Iic b)-(ρ : Measure ℝ).real (Iic a) := by
      rw [←Iic_sdiff_Iic,measureReal_sdiff (μ:=(ρ:Measure ℝ)) (Iic_subset_Iic.mpr hab.le) measurableSet_Iic]
    simpa only [id_eq,eq] using (h b).sub (h a)

def gaussianLaw (a v : ℝ) : ProbabilityMeasure ℝ := ⟨gaussianReal a v.toNNReal,inferInstance⟩
def seedProb (m : ℕ) : ProbabilityMeasure (Seed m) := ⟨seedLaw m,inferInstance⟩
def scaled (n : ℕ) {m : ℕ} (Y : Seed m→ℝ) (ω : Seed m) := ((n:ℝ)+1)^2*(Y ω-1)

private theorem target_cdf (a v t : ℝ) (hv : 0<v) :
    (gaussianLaw (-a) v : Measure ℝ).real (Iic t) = normalCDF ((t+a)/sqrt v) := by
  rw [←scale _ _ hv]
  change (gaussianReal (-a) v.toNNReal).real (Iic t) = (gaussianReal 0 v.toNNReal).real (Iic (t+a))
  have hs := gaussianReal_map_sub_const (μ:=0) (v:=v.toNNReal) a
  rw [zero_sub] at hs
  unfold Measure.real
  rw [←hs,Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext z
  exact sub_le_iff_le_add

/-- The law of the actual teacher-centered statistic converges weakly to
the stated Gaussian distribution. -/
theorem weak_prediction (n m : ℕ→ℕ) (Y : (i : ℕ)→Seed (m i)→ℝ)
    (meas : ∀ i, Measurable (Y i)) (a v : ℝ) (hv : 0<v) (clt : PredictionCLT n m Y a v) :
    Tendsto (fun i => (seedProb (m i)).map (scaled (n i) (Y i))) atTop (𝓝 (gaussianLaw (-a) v)) := by
  apply weak_of_cdf
  intro t
  rw [target_cdf a v t hv]
  have hm (i : ℕ) : Measurable (scaled (n i) (Y i)) := measurable_const.mul ((meas i).sub_const _)
  have eq (i : ℕ) : ((seedProb (m i)).map (scaled (n i) (Y i)) : Measure ℝ).real (Iic t) =
      (seedLaw (m i)).real {ω | ((n i:ℝ)+1)^2*(Y i ω-1)≤t} := by
    unfold Measure.real; rw [ProbabilityMeasure.map_apply' _ (hm i).aemeasurable measurableSet_Iic];rfl
  simpa only [eq] using clt t

private def contrast (p : ℝ×ℝ) := (p.1-p.2)/sqrt 2
private theorem contrast_gaussian : ((gaussianLaw 0 1).prod (gaussianLaw 0 1)).map contrast=gaussianLaw 0 1 := by
  let G := gaussianReal (0:ℝ) 1
  have indep := indepFun_prod (μ:=G) (ν:=G) measurable_id (measurable_id.neg)
  have h1 : HasLaw Prod.fst G (G.prod G) := measurePreserving_fst.hasLaw
  have h2 : HasLaw (fun p : ℝ×ℝ => -p.2) (gaussianReal (-0) 1) (G.prod G) :=
    gaussianReal_neg ((measurePreserving_snd (μ:=G) (ν:=G)).hasLaw)
  have h3 : HasLaw (fun p : ℝ×ℝ => p.1-p.2) (gaussianReal 0 2) (G.prod G) := by
    refine ⟨by fun_prop,?_⟩
    have h := gaussianReal_add_gaussianReal_of_indepFun indep h1 h2
    convert h using 1 <;> norm_num [Pi.add_def,sub_eq_add_neg]
  have h4 := gaussianReal_mul_const h3 (sqrt (2:ℝ))⁻¹
  apply Subtype.ext
  simp only [ProbabilityMeasure.val_eq_to_measure,ProbabilityMeasure.toMeasure_map,gaussianLaw,Real.toNNReal_one]
  change (G.prod G).map contrast = gaussianReal 0 1
  convert h4.map_eq using 1
  · congr 1
  · congr 1
    · ring
    · ext; simp

/-- Independent standardized replications: if one-seed laws converge to the
standard normal, their difference divided by √2 does as well. -/
theorem independent_difference (m : ℕ→ℕ) (X : (i : ℕ)→Seed (m i)→ℝ)
    (meas : ∀ i, Measurable (X i)) (clt : ∀ t : ℝ, Tendsto (fun i =>
      (seedLaw (m i)).real {ω | X i ω≤t}) atTop (𝓝 (normalCDF t))) :
    Tendsto (fun i => ((seedProb (m i)).prod (seedProb (m i))).map
      (fun p => (X i p.1-X i p.2)/sqrt 2)) atTop (𝓝 (gaussianLaw 0 1)) := by
  let P i := (seedProb (m i)).map (X i)
  have w : Tendsto P atTop (𝓝 (gaussianLaw 0 1)) := by
    apply weak_of_cdf
    intro t
    have eq (i : ℕ) : (P i : Measure ℝ).real (Iic t)=(seedLaw (m i)).real {ω | X i ω≤t} := by
      unfold P Measure.real
      rw [ProbabilityMeasure.map_apply' _ (meas i).aemeasurable measurableSet_Iic];rfl
    simpa only [eq,gaussianLaw,Real.toNNReal_one,ProbabilityMeasure.coe_mk,normalCDF] using clt t
  have p := ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (w.prodMk_nhds w)
  have d := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ p
    (f:=contrast) (by unfold contrast;fun_prop)
  rw [contrast_gaussian] at d
  convert d using 1
  ext i : 1
  dsimp only [P,Function.comp_apply]
  rw [ProbabilityMeasure.map_prod_map _ _ (meas i) (meas i)]
  apply Subtype.ext
  change _ = Measure.map contrast (Measure.map (Prod.map (X i) (X i)) _)
  rw [Measure.map_map (by unfold contrast;fun_prop) (by fun_prop)]
  rfl


/-- Under the same finite-width tracking schedule, two independent trained
outputs have an asymptotically standard normal difference after division
by the exact finite-grid standard deviation √(2V). -/
theorem independent_training (n m : ℕ→ℕ) (wide : Tendsto m atTop atTop)
    (hn : ∀ i, 3≤n i+1) (ho : ∀ i, Odd (n i+1)) (hm : ∀ i, 0<m i)
    (b e δ : ℕ→ℝ) (Y : (i : ℕ)→Seed (m i)→ℝ) (meas : ∀ i, Measurable (Y i))
    (he : ∀ i, 0≤e i) (failure : ∀ i, (seedLaw (m i)).real
      {ω | e i < |Y i ω-reference (n i+1) (m i) (b i) ω|} ≤ δ i)
    (hd : Tendsto δ atTop (𝓝 0))
    (small : Tendsto (fun i => e i/√(featureVariance (n i+1) (b i))) atTop (𝓝 0)) :
    Tendsto (fun i => ((seedProb (m i)).prod (seedProb (m i))).map
      (fun p => (Y i p.1-Y i p.2)/√(2*featureVariance (n i+1) (b i)))) atTop (𝓝 (gaussianLaw 0 1)) := by
  let V i := featureVariance (n i+1) (b i)
  let X i ω := (Y i ω-b i)/√(V i)
  have hcost : Tendsto (fun i => e i/√(2*π*V i)) atTop (𝓝 0) := by
    simpa only [sqrt_mul (show (0:ℝ)≤2*π by positivity),div_div, mul_comm (√(2*π)),zero_div,V] using
      small.div_const (√(2*π))
  have hsum : Tendsto (fun i => 5*CircleReferenceKurtosis.ratioConstant/(m i:ℝ)+δ i+e i/√(2*π*V i))
      atTop (𝓝 0) := by
    have w := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp wide)).const_mul (5*CircleReferenceKurtosis.ratioConstant)
    simpa [div_eq_mul_inv] using (w.add hd).add hcost
  have single (t : ℝ) : Tendsto (fun i => (seedLaw (m i)).real {ω | X i ω≤t}) atTop (𝓝 (normalCDF t)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun i => dist_nonneg) _ hsum
    intro i
    exact uniform_training (n i) (m i) (hn i) (ho i) (hm i) (b i) (Y i) (he i) (failure i) t
  convert independent_difference m X (fun i => ((meas i).sub_const _).div_const _) single using 1
  ext i : 1
  congr 1
  ext p
  dsimp only [X,V]
  rw [sqrt_mul (by norm_num : (0:ℝ)≤2),←sub_div,sub_sub_sub_cancel_right,div_div,mul_comm]


/-- The conditioned curvature screen changes every distribution function by
at most its rejected mass. The accepted unit-step law has the same Gaussian
limit at every benchmark horizon. -/
theorem accepted_gd (n T : ℕ→ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (odd : ∀ i, Odd (n i+1))
    (lo : ∀ i, CircleKernelGD.short ((n i:ℝ)+1)≤T i) (hi : ∀ i, T i≤385*(n i+1)^3) (t : ℝ) :
    Tendsto (fun i => (CircleGDLimits.acceptedLaw (n i)).real {ω |
      ((n i:ℝ)+1)^2*(CircleGDLimits.fixed (n i) (T i) ω-1)≤t}) atTop
      (𝓝 (normalCDF ((t+π^2/36)/√(7*π^2/1620)))) := by
  let m i := CircleGDLimits.Width (n i)
  let μ i := seedLaw (m i)
  let ν i := CircleGDLimits.acceptedLaw (n i)
  let E i := CircleCapMoments.screen (n i+1) (m i)
  let A i := {ω | ((n i:ℝ)+1)^2*(CircleGDLimits.fixed (n i) (T i) ω-1)≤t}
  have close (i : ℕ) : |(ν i).real (A i)-(μ i).real (A i)|≤exp (-(m i:ℝ)/240) := by
    have M : 81≤n i+1 := by have := hn i;omega
    have hM : 0<m i := pow_pos (Nat.succ_pos _) _
    have hE : MeasurableSet (E i) := CircleCapMoments.screen_measurable _ _ (by omega) (odd i) hM
    have pos : (μ i) (E i)≠0 := CircleGDLimits.accept_pos M (odd i)
    let : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure pos
    have hA : MeasurableSet (A i) := measurableSet_le
      (measurable_const.mul ((CircleGDLimits.fixed_measurable (n i) (T i)).sub_const 1)) measurable_const
    rw [abs_sub_comm]
    have h := TrainingLaws.event_gap_le (μ i) (ν i) hA
    have tv : tvDist (μ i) (ν i)/2=(μ i).real (E i)ᶜ := CircleConditioning.seed_tv (μ i) hE pos
    rw [tv] at h
    refine h.trans ?_
    rw [measureReal_compl hE,probReal_univ]
    linarith only [(CircleCapMoments.screen_probability _ _ M (odd i) hM).1]
  have mg : Tendsto (fun i => (m i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp (CircleGaussianLimit.width_grows n grow)
  have ev : Tendsto (fun i => exp (-(m i:ℝ)/240)) atTop (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    simpa only [neg_div,Function.comp_def] using tendsto_neg_atTop_atBot.comp (mg.atTop_div_const (by norm_num : (0:ℝ)<240))
  have er : Tendsto (fun i => (ν i).real (A i)-(μ i).real (A i)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) close ev)
  have cc := CircleGaussianLimit.fixed_gd n T grow hn odd lo hi t
  change Tendsto (fun i => (μ i).real (A i)) _ _ at cc
  simpa [ν,A] using er.add cc

/-- Coverage of any fixed interval from a uniform error on a CDF. -/
theorem interval_coverage {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω→ℝ) (meas : Measurable Y) (d : ℝ) (bound : ∀ t, |μ.real {ω | Y ω≤t}-normalCDF t|≤d)
    (a b : ℝ) (hab : a≤b) :
    normalCDF b-normalCDF a-2*d ≤ μ.real {ω | a<Y ω ∧ Y ω≤b} := by
  have eq : {ω | a<Y ω ∧ Y ω≤b} = {ω | Y ω≤b} \ {ω | Y ω≤a} := by ext; simp [and_comm]
  have sub : {ω | Y ω≤a} ⊆ {ω | Y ω≤b} := fun _ h => le_trans h hab
  rw [eq,measureReal_sdiff (μ:=μ) sub (measurableSet_le meas measurable_const)]
  linarith only [(abs_le.mp (bound b)).1,(abs_le.mp (bound a)).2]


/-- Standard normal quantile, characterized by the inverse CDF on (0,1). -/
def normalQuantile (p : ℝ) := Function.invFun normalCDF p

theorem normalQuantile_spec {p : ℝ} (h0 : 0<p) (h1 : p<1) : normalCDF (normalQuantile p)=p := by
  have id : (fun x => normalCDF x) = (cdf (gaussianReal 0 1) : ℝ→ℝ) := funext fun x => (cdf_eq_real _ x).symm
  have low := (tendsto_cdf_atBot (gaussianReal 0 1)).eventually (eventually_lt_nhds h0)
  have high := (tendsto_cdf_atTop (gaussianReal 0 1)).eventually (eventually_gt_nhds h1)
  rw [←id] at low high
  apply Function.invFun_eq
  exact mem_range_of_exists_le_of_exists_ge (continuous_iff_continuousAt.mpr fun x => (normalCDF_deriv x).continuousAt)
    (low.mono (fun _ h=>h.le)).exists (high.mono (fun _ h=>h.le)).exists

/-- A CDF error bound gives a finite-width interval for each physical
population-prediction quantile, including the finite-grid shift b. -/
theorem quantile_interval {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω→ℝ) (b σ p d : ℝ) (hσ : 0<σ) (hd : 0≤d) (hp : d<p) (hp' : p<1-d)
    (cdfBound : ∀ t, |μ.real {ω | (Y ω-b)/σ≤t}-normalCDF t|≤d) :
    sInf {x | p≤μ.real {ω | Y ω≤x}} ∈ Icc (b+σ*normalQuantile (p-d)) (b+σ*normalQuantile (p+d)) := by
  let A := {x | p≤μ.real {ω | Y ω≤x}}
  have mono : StrictMono normalCDF := strictMono_of_deriv_pos fun x => by
    rw [(normalCDF_deriv x).deriv];unfold density;positivity
  have ql := normalQuantile_spec (p:=p-d) (by linarith) (by linarith)
  have qu := normalQuantile_spec (p:=p+d) (by linarith) (by linarith)
  have raw (x : ℝ) : |μ.real {ω | Y ω≤x}-normalCDF ((x-b)/σ)|≤d := by
    have eq : {ω | (Y ω-b)/σ≤(x-b)/σ}={ω | Y ω≤x} := by ext ω; simp [div_le_div_iff_of_pos_right hσ]
    simpa only [eq] using cdfBound ((x-b)/σ)
  have upper : b+σ*normalQuantile (p+d)∈A := by
    change p ≤ μ.real {ω | Y ω≤b+σ*normalQuantile (p+d)}
    have h := (abs_le.mp (raw (b+σ*normalQuantile (p+d)))).1
    rw [show (b+σ*normalQuantile (p+d)-b)/σ=normalQuantile (p+d) by field_simp;ring,qu] at h
    linarith
  have lower (x : ℝ) (hx : x∈A) : b+σ*normalQuantile (p-d)≤x := by
    by_contra! h
    have ht : (x-b)/σ<normalQuantile (p-d) := (div_lt_iff₀ hσ).mpr (by linarith)
    have hh := mono ht
    rw [ql] at hh
    change p≤μ.real {ω | Y ω≤x} at hx
    linarith only [hx,hh,(abs_le.mp (raw x)).2]
  exact ⟨le_csInf ⟨_,upper⟩ lower,csInf_le ⟨_,lower⟩ upper⟩

end CircleWeakPrediction
