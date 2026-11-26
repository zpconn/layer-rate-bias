module
public import CircleReferenceDistribution
public import CircleSharpMoments
public import CircleSharpGDMoments
import all CircleReferenceDistribution
import all CircleGaussianCDF
import all CircleReferenceMoments
import all CircleComparison
import all CircleGDLimits
import all CircleDiscreteMoments
import all CircleKernelGD
import all CircleCapMoments
import all CircleSpectrum
import Mathlib.Tactic

/-! Gaussian limits of the population prediction at its N⁻² fluctuation scale.
CDF convergence is proved directly on the original, varying seed spaces. -/
public section
noncomputable section
namespace CircleGaussianLimit
open Real Filter Topology Set MeasureTheory ProbabilityTheory CircleEscapeBridge
  CircleReferenceDistribution CircleGaussianCDF CircleComparison CircleGDLimits CircleKernelGD

/-- The exact target law is N(-a,v), expressed through its CDF. -/
def PredictionCLT (n m : ℕ→ℕ) (Y : (i : ℕ)→ Seed (m i)→ℝ) (a v : ℝ) : Prop :=
  ∀ t : ℝ, Tendsto (fun i => (seedLaw (m i)).real {ω | ((n i:ℝ)+1)^2*(Y i ω-1)≤t})
    atTop (𝓝 (normalCDF ((t+a)/√v)))

private theorem markov_rms {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω→ℝ) (mem : MemLp D 2 μ) (q r : ℝ) (hq : 0<q) (hr : 0<r)
    (h : sqrt (∫ ω, D ω^2 ∂μ) ≤ r^2/q) :
    μ.real {ω | r/q < |D ω|} ≤ q*sqrt (∫ ω, D ω^2 ∂μ) := by
  let A := sqrt (∫ ω, D ω^2 ∂μ)
  have hA : 0≤A := sqrt_nonneg _
  have hA2 : A^2=∫ ω, D ω^2 ∂μ := sq_sqrt (integral_nonneg fun _=>sq_nonneg _)
  have hp := mul_meas_ge_le_integral_of_nonneg (μ:=μ) (ae_of_all _ fun x => sq_nonneg (D x))
    mem.integrable_sq ((r/q)^2)
  have hm : μ.real {ω | r/q < |D ω|} ≤ μ.real {ω | (r/q)^2 ≤ D ω^2} :=
    measureReal_mono (fun ω hw => by
      change r/q < |D ω| at hw
      exact (pow_le_pow_left₀ (div_nonneg hr.le hq.le) hw.le 2).trans_eq (sq_abs _))
  rw [←hA2] at hp
  apply hm.trans
  have hm2 := (le_div_iff₀ (sq_pos_of_pos (div_pos hr hq))).mpr ((mul_comm _ _).le.trans hp)
  refine hm2.trans ?_
  apply (div_le_iff₀ (sq_pos_of_pos (div_pos hr hq))).mpr
  have hqA := (le_div_iff₀ hq).mp h
  change A*q≤r^2 at hqA
  have hh := mul_le_mul_of_nonneg_left hqA hA
  change A^2 ≤ q*A*(r/q)^2
  field_simp [hq.ne']
  nlinarith only [hh]

/-- Arbitrary interpolation weights with convergent scaled bias and
variance, and any same-seed statistic tracked in RMS at little-o of N⁻². -/
theorem of_tracking (n m : ℕ→ℕ) (grow : Tendsto n atTop atTop)
    (mgrow : Tendsto m atTop atTop) (hn : ∀ i, 3≤n i+1) (ho : ∀ i, Odd (n i+1))
    (hm : ∀ i, 0<m i) (b : ℕ→ℝ) (Y : (i : ℕ)→Seed (m i)→ℝ) (a v : ℝ) (hv : 0<v)
    (bias : Tendsto (fun i => ((n i:ℝ)+1)^2*(1-b i)) atTop (𝓝 a))
    (var : Tendsto (fun i => ((n i:ℝ)+1)^4*featureVariance (n i+1) (b i)) atTop (𝓝 v))
    (mem : ∀ i, MemLp (fun ω => Y i ω-reference (n i+1) (m i) (b i) ω) 2 (seedLaw (m i)))
    (track : Tendsto (fun i => ((n i:ℝ)+1)^2*sqrt (∫ ω, (Y i ω-reference (n i+1) (m i) (b i) ω)^2 ∂seedLaw (m i)))
      atTop (𝓝 0)) : PredictionCLT n m Y a v := by
  intro t
  let x i := (n i:ℝ)+1
  let V i := featureVariance (n i+1) (b i)
  let d i := x i^2 * sqrt (V i)
  let D i ω := Y i ω-reference (n i+1) (m i) (b i) ω
  let E i := x i^2*sqrt (∫ ω, (D i ω)^2 ∂seedLaw (m i))
  let r i := sqrt (E i)+1/x i
  let t' i := (t+x i^2*(1-b i))/d i
  have xp (i : ℕ) : 0<x i := by dsimp [x];positivity
  have vp (i : ℕ) : 0<V i := featureVariance_pos (hn i) (ho i) _
  have sp (i : ℕ) : 0<sqrt (V i) := sqrt_pos.mpr (vp i)
  have ep (i : ℕ) : 0≤E i := mul_nonneg (sq_nonneg _) (sqrt_nonneg _)
  have dp (i : ℕ) : 0<d i := mul_pos (sq_pos_of_pos (xp i)) (sp i)
  have rp (i : ℕ) : 0<r i := by dsimp [r];positivity [xp i]
  have dl : Tendsto d atTop (𝓝 (sqrt v)) := by
    convert var.sqrt using 1
    ext i
    change x i^2*sqrt (V i)=sqrt (x i^4*V i)
    rw [Real.sqrt_mul (by positivity),show x i^4=(x i^2)^2 by ring,sqrt_sq (sq_nonneg _)]
  have tl : Tendsto t' atTop (𝓝 ((t+a)/sqrt v)) :=
    ((tendsto_const_nhds (x:=t)).add bias).div dl (sqrt_pos.mpr hv).ne'
  have rl : Tendsto r atTop (𝓝 0) := by
    have hE : Tendsto E atTop (𝓝 0) := track
    simpa only [r,x,Function.comp_apply,sqrt_zero,zero_add] using hE.sqrt.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp grow)
  have bound (i : ℕ) := uniform_training (n i) (m i) (hn i) (ho i) (hm i) (b i) (Y i)
    (e:=r i/x i^2) (δ:=E i) (div_nonneg (rp i).le (sq_nonneg _)) (by
      apply markov_rms _ (D i) (mem i) (x i^2) (r i) (sq_pos_of_pos (xp i)) (rp i)
      apply (le_div_iff₀ (sq_pos_of_pos (xp i))).mpr
      rw [mul_comm]
      change E i ≤ r i^2
      apply (sq_sqrt (ep i)).symm.le.trans
      exact pow_le_pow_left₀ (sqrt_nonneg _) (by dsimp [r]; linarith [one_div_pos.mpr (xp i)]) _) (t' i)
  have event (i : ℕ) : {ω | (Y i ω-b i)/sqrt (V i) ≤ t' i} = {ω | x i^2*(Y i ω-1)≤t} := by
    ext ω
    change (Y i ω-b i)/sqrt (V i) ≤ (t+x i^2*(1-b i))/(x i^2*sqrt (V i)) ↔ _
    rw [div_le_div_iff₀ (sp i) (dp i)]
    change _ ↔ x i^2*(Y i ω-1)≤t
    rw [show (Y i ω-b i)*(x i^2*sqrt (V i))= (x i^2*(Y i ω-b i))*sqrt (V i) by ring,
      mul_le_mul_iff_left₀ (sp i)]
    constructor <;> intro h <;> linarith only [h]
  have miss : Tendsto (fun i => (5*CircleReferenceKurtosis.ratioConstant)/(m i:ℝ)+E i+
        r i/(sqrt (2*π)*d i)) atTop (𝓝 0) := by
    have h1 := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp mgrow)).const_mul (5*CircleReferenceKurtosis.ratioConstant)
    have h2 : Tendsto E atTop (𝓝 0) := track
    simpa [div_eq_mul_inv] using (h1.add h2).add (rl.div (dl.const_mul (sqrt (2*π))) (by positivity))
  let P i := (seedLaw (m i)).real {ω | x i^2*(Y i ω-1)≤t}
  have er : Tendsto (fun i => P i-normalCDF (t' i)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun i => norm_nonneg _) _ miss
    intro i
    have h := bound i
    rw [event i] at h
    apply h.trans_eq
    rw [Real.sqrt_mul (by positivity : 0≤2*π)]
    change _+_+(r i/x i^2)/(sqrt (2*π)*sqrt (V i))=_+_+r i/(sqrt (2*π)*(x i^2*sqrt (V i)))
    simp only [div_eq_mul_inv,mul_inv_rev]; ring
  have hc := (normalCDF_deriv ((t+a)/sqrt v)).continuousAt.tendsto.comp tl
  simpa [P,x] using er.add hc


private theorem width_grows (n : ℕ→ℕ) (grow : Tendsto n atTop atTop) :
    Tendsto (fun i => Width (n i)) atTop atTop :=
  tendsto_atTop_mono (fun i => (Nat.le_succ (n i)).trans (Nat.le_pow (by decide : 0<32)))
    grow

/-- Every valid endpoint-measurable nonlinear flow at the paper's horizon
has the Gaussian limit at its own layer multiplier, including the original
equal-rate flow. -/
theorem flow (n : ℕ→ℕ) (grow : Tendsto n atTop atTop) (hn : ∀ i, 32≤n i+1)
    (odd : ∀ i, Odd (n i+1)) {τ : ℝ} (hτ : 1/2≤τ) (hu : τ≤2) (F : ∀ i, Benchmark (n i) τ) :
    PredictionCLT n (fun i => Width (n i)) (fun i => trained (n i) (F i))
      (π^2*τ/(12*(2+τ))) (π^2/360*(1+5*τ^2/(2+τ)^2)) := by
  have ht : 0<τ := by linarith
  have hn3 (i : ℕ) : 3≤n i+1 := (by have := hn i;omega)
  apply of_tracking n _ grow (width_grows n grow) hn3 odd (fun i => pow_pos (Nat.succ_pos _) _)
    (fun i => CircleSpectrum.weight τ (n i)) _ _ _ (by positivity)
  · exact (CircleSpectrum.bias_limit τ ht.le).comp grow
  · simpa only [fun i => featureVariance_eq (hn3 i) (odd i),CircleSpectrum.variance,Function.comp_def] using
      (CircleSpectrum.variance_limit τ ht.le).comp grow
  · intro i
    have hm := CircleComparison.integrable_pair (n i) ht hu (F i)
    exact hm.1.sub hm.2
  · have lim := (tendsto_inv_atTop_zero.comp
        (tendsto_sqrt_atTop.comp (CircleComparison.grown n grow))).const_mul oneRateConstant
    refine squeeze_zero (fun i => mul_nonneg (sq_nonneg _) (sqrt_nonneg _))
      (g:=fun i => oneRateConstant*(sqrt ((n i:ℝ)+1))⁻¹) ?_ (by simpa using lim)
    intro i
    have bd := one_rate_tracking (n i) (hn i) (odd i) hτ hu (F i)
    apply (mul_le_mul_of_nonneg_left bd (sq_nonneg ((n i:ℝ)+1))).trans_eq
    field_simp

/-- Capped GD has the teacher-centered Gaussian limit for every update
schedule from the short benchmark through 385 N³, hence at S, M and H. -/
theorem capped_gd (n T : ℕ→ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (odd : ∀ i, Odd (n i+1))
    (lo : ∀ i, short ((n i:ℝ)+1)≤T i) (hi : ∀ i, T i≤385*(n i+1)^3) :
    PredictionCLT n (fun i => Width (n i)) (fun i => capped (n i) (T i)) (π^2/36) (7*π^2/1620) := by
  let m i := Width (n i)
  have hm (i : ℕ) : 0<m i := pow_pos (Nat.succ_pos _) _
  have hn3 (i : ℕ) : 3≤n i+1 := by have := hn i;omega
  obtain ⟨h1,h2⟩ := stopped_reference_limits n m T grow hn3 odd hm lo
  have h (i : ℕ) := stopped_reference_moments (n i) (m i) (T i) (hn3 i) (odd i) (hm i)
  simp_rw [fun i => (h i).1] at h1
  simp_rw [fun i => (h i).2,← fun i => featureVariance_eq (hn3 i) (odd i)] at h2
  apply of_tracking n m grow (width_grows n grow) hn3 odd hm (fun i => stoppedWeight (n i) (T i)) _ _ _ (by positivity) h1 h2
  · intro i
    exact (CircleGDLimits.cap_mem (hn i) (odd i) (hi i)).sub
      (CircleSeedIntegrability.reference_memLp _ _ _ 2 (by norm_num))
  · apply CircleGDLimits.scaled_rms n grow (C:=(198*66*385:ℝ)^2+1044*sqrt 13) (by positivity)
    intro i
    simpa only [capped,m,Width,CircleCapMoments.cappedSq,Nat.cast_add,Nat.cast_one] using
      CircleDiscreteMoments.capped_stopped_mse (n i) (hn i) (odd i) (T i) (hi i)

/-- The ordinary unit-step learner has the same Gaussian distributional
limit on the complete Gaussian law, including the fitting horizon where
its rare-seed second moment diverges. -/
theorem fixed_gd (n T : ℕ→ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (odd : ∀ i, Odd (n i+1))
    (lo : ∀ i, short ((n i:ℝ)+1)≤T i) (hi : ∀ i, T i≤385*(n i+1)^3) :
    PredictionCLT n (fun i => Width (n i)) (fun i => fixed (n i) (T i)) (π^2/36) (7*π^2/1620) := by
  intro t
  let N i := n i+1
  let m i := Width (n i)
  let μ i := seedLaw (m i)
  let P (i : ℕ) (f : Seed (m i)→ℝ) := (μ i).real {ω | ((n i:ℝ)+1)^2*(f ω-1)≤t}
  let A i := CircleCapMoments.screen (N i) (m i)
  have close (i : ℕ) : |P i (fixed (n i) (T i))-P i (capped (n i) (T i))|≤exp (-(m i:ℝ)/240) := by
    have hm : 0<m i := pow_pos (Nat.succ_pos _) _
    have hN : 81≤N i := by have := hn i;dsimp [N];omega
    have hs := (CircleCapMoments.screen_probability (N i) (m i) hN (odd i) hm).1
    have hmA : (μ i).real (A i)ᶜ≤exp (-(m i:ℝ)/240) := by
      rw [measureReal_compl (CircleCapMoments.screen_measurable (N i) (m i) (by omega) (odd i) hm),probReal_univ]
      linarith only [hs]
    have bound (f g : Seed (m i)→ℝ) (hg : ∀ ω ∈ A i, f ω=g ω) : P i f ≤ P i g+(μ i).real (A i)ᶜ := by
      apply (measureReal_mono (μ:=μ i) (show {ω | ((n i:ℝ)+1)^2*(f ω-1)≤t} ⊆
        {ω | ((n i:ℝ)+1)^2*(g ω-1)≤t} ∪ (A i)ᶜ from ?_)).trans (measureReal_union_le _ _)
      intro ω hω
      by_cases ha : ω∈A i
      · apply Or.inl
        change ((n i:ℝ)+1)^2*(g ω-1)≤t
        rw [←hg ω ha];exact hω
      · exact Or.inr ha
    have eq (ω) (hω : ω∈A i) : fixed (n i) (T i) ω=capped (n i) (T i) ω :=
      CircleGDLimits.fixed_capped hω
    exact abs_le.mpr ⟨by linarith only [bound _ _ fun ω hω => (eq ω hω).symm,hmA],
      by linarith only [bound _ _ eq,hmA]⟩
  have mg : Tendsto (fun i => (m i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp (width_grows n grow)
  have ev : Tendsto (fun i => exp (-(m i:ℝ)/240)) atTop (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    simpa only [neg_div,Function.comp_def] using tendsto_neg_atTop_atBot.comp (mg.atTop_div_const (by norm_num : (0:ℝ)<240))
  have er : Tendsto (fun i => P i (fixed (n i) (T i))-P i (capped (n i) (T i))) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _=>norm_nonneg _) close ev)
  have cc := capped_gd n T grow hn odd lo hi t
  change Tendsto (fun i => P i (capped (n i) (T i))) _ _ at cc
  simpa using er.add cc

end CircleGaussianLimit
