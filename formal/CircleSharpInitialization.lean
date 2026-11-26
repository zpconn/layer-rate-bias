module

public import CircleGaussianBernstein
public import CircleGaussianTracking
import all CircleInitializationConcentration
import all CircleGaussianBernstein
import all CircleGaussianTracking
import all CircleFlowPath
import all CircleTangentDrift
import all CircleFlowMoments
import Mathlib.Tactic

/-! Fourth moments of centered, width-normalized initial neuron averages,
and logarithmic high-probability bounds for the actual grid residual. -/
public section
noncomputable section
namespace CircleSharpInitialization
open Real MeasureTheory ProbabilityTheory CircleEscapeBridge CircleInitializationConcentration
  CircleGaussianBernstein CircleGaussianTracking CircleTangentDrift CircleFlowPath

def centeredSum {m : ℕ} (X : Atom → ℝ) (ω : Seed m) : ℝ :=
  sqrt m * (sampleAverage X ω - ∫ z, X z ∂atomLaw)

def markConstant : ℝ := (48*16^4*exp 4 : ℝ)^((4:ℝ)⁻¹)

private theorem scaled_mgf {m : ℕ} (hm : 0 < m) (X : Atom → ℝ) (hX : Measurable X)
    (dom : ∀ z, |X z| ≤ energy z) (t : ℝ) (ht : |t| ≤ 1/16) :
    Integrable (fun ω : Seed m => exp (t*centeredSum X ω)) (seedLaw m) ∧
    mgf (centeredSum (m:=m) X) (seedLaw m) t ≤ exp (1024*t^2) := by
  let s := t/sqrt m
  have hm1 : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have hr := Real.one_le_sqrt.mpr hm1
  have hp : 0 < sqrt (m:ℝ) := by positivity
  have hs : |s| ≤ 1/16 := by
    rw [show |s| = |t|/sqrt m by simp [s,abs_div,abs_of_pos hp]]
    exact ((div_le_self (abs_nonneg _) hr)).trans ht
  let Y := fun z : Atom => X z - ∫ a, X a ∂atomLaw
  let ν := Measure.pi (fun _ : Fin m => atomLaw)
  let F := fun (j : Fin m) (a : Fin m → Atom) => Y (a j)
  let S : (Fin m → Atom) → ℝ := ∑ j, F j
  have hy : Measurable Y := hX.sub measurable_const
  have hf j : Measurable (F j) := hy.comp (measurable_pi_apply j)
  have ind : iIndepFun F ν := iIndepFun_pi (fun _ => hy.aemeasurable)
  have he := centered_mgf X hX dom s hs
  have hi (j : Fin m) : Integrable (fun a => exp (s*F j a)) ν :=
    (measurePreserving_eval (fun _ : Fin m => atomLaw) j).integrable_comp_of_integrable he.1
  have hsint : Integrable (fun a => exp (s*S a)) ν :=
    ind.integrable_exp_mul_sum hf (s:=Finset.univ) (fun j _ => hi j)
  have eq (ω : Seed m) : t*centeredSum X ω = s*S (currySeed m ω) := by
    simp only [S,F,Y,Finset.sum_apply,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,centeredSum,sampleAverage]
    change t*(sqrt m*((m:ℝ)⁻¹*(∑ j, X ((currySeed m) ω j))-_)) = s*((∑ j, X ((currySeed m) ω j))-_)
    dsimp [s]; field_simp; rw [sq_sqrt (by positivity)]
  constructor
  · simp_rw [eq]; exact (curry_preserving m).integrable_comp_of_integrable hsint
  · unfold mgf
    simp_rw [eq]
    rw [(curry_preserving m).integral_comp' (fun a => exp (s*S a))]
    change mgf (∑ j,F j) ν s ≤ _
    rw [ind.mgf_sum hf]
    have single (j : Fin m) : mgf (F j) ν s ≤ exp (1024*s^2) := by
      have h := (measurePreserving_eval (fun _ : Fin m => atomLaw) j).hasLaw.integral_comp
        (f:=fun z => exp (s*Y z)) ((hy.const_mul s).exp.aestronglyMeasurable)
      exact h.le.trans he.2
    refine (Finset.prod_le_prod₀ (fun j _ => mgf_nonneg) (fun j _ => single j)).trans_eq ?_
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.exp_nat_mul]
    congr 1
    dsimp [s]; rw [div_pow,sq_sqrt (by positivity)]
    field_simp

private theorem fourth_unit {m : ℕ} (hm : 0 < m) (X : Atom → ℝ) (hX : Measurable X)
    (dom : ∀ z, |X z| ≤ energy z) :
    MemLp (centeredSum (m:=m) X) 4 (seedLaw m) ∧
    lpNorm (centeredSum (m:=m) X) 4 (seedLaw m) ≤ markConstant := by
  let Y := centeredSum (m:=m) X
  have hY : Measurable Y := ((sampleAverage_meas hX).sub measurable_const).const_mul _
  have hp := scaled_mgf (m:=m) hm X hX dom (1/16) (by norm_num)
  have hn := scaled_mgf (m:=m) hm X hX dom (-1/16) (by norm_num)
  let e := fun ω => 24*16^4*(exp ((1/16)*Y ω)+exp ((-1/16)*Y ω))
  have hi : Integrable e (seedLaw m) := (hp.1.add hn.1).const_mul _
  have bound (ω : Seed m) : Y ω ^4 ≤ e ω := by
    have h := Real.pow_div_factorial_le_exp (|Y ω|/16) (by positivity) 4
    norm_num [div_pow,(by decide : Even 4).pow_abs] at h
    have ht : exp (|Y ω|/16) ≤ exp ((1/16)*Y ω)+exp ((-1/16)*Y ω) := by
      by_cases hy : 0 ≤ Y ω
      · rw [abs_of_nonneg hy,div_eq_inv_mul]; linarith [exp_pos ((-1/16)*Y ω)]
      · rw [abs_of_neg (lt_of_not_ge hy), show -Y ω/16=(-1/16)*Y ω by ring]; linarith [exp_pos ((1/16)*Y ω)]
    dsimp [e]; linarith
  have h4 : Integrable (fun ω => Y ω^4) (seedLaw m) :=
    hi.mono' (hY.pow_const 4).aestronglyMeasurable (ae_of_all _ fun ω => by
      simpa [Real.norm_eq_abs,(by decide : Even 4).pow_abs] using bound ω)
  have hM : MemLp Y 4 (seedLaw m) := by
    apply (integrable_norm_rpow_iff hY.aestronglyMeasurable (by norm_num : (4:ENNReal)≠0) (by norm_num)).1
    simpa [Real.norm_eq_abs, (by decide : Even 4).pow_abs] using h4
  have H := integral_mono h4 hi bound
  rw [show (∫ ω, e ω ∂seedLaw m) = (24*16^4)*(mgf Y (seedLaw m) (1/16) + mgf Y (seedLaw m) (-1/16)) by
    dsimp [e,mgf]; rw [integral_const_mul,integral_add hp.1 hn.1]] at H
  have hA : mgf Y (seedLaw m) (1/16) ≤ exp 4 := by norm_num at hp; exact hp.2
  have hB : mgf Y (seedLaw m) (-1/16) ≤ exp 4 := by norm_num at hn ⊢; exact hn.2
  have M : (∫ ω, Y ω ^4 ∂seedLaw m) ≤ 48*16^4*exp 4 := by linarith
  refine ⟨hM,?_⟩
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hY.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast,Real.norm_eq_abs,(by decide : Even 4).pow_abs]
  simpa only [one_div, Nat.cast_ofNat, markConstant] using Real.rpow_le_rpow (integral_nonneg (fun ω : Seed m => (by decide : Even 4).pow_nonneg (Y ω))) M (by norm_num : 0 ≤ (4:ℝ)⁻¹)

/-- Uniform fourth norm for centered sums with CLT normalization, including
Gaussian readout-weighted hidden marks. D can be any positive envelope scale. -/
theorem average_fourth {m : ℕ} (hm : 0 < m) (X : Atom → ℝ) (hX : Measurable X) {D : ℝ} (hD : 0 < D)
    (dom : ∀ z, |X z| ≤ D*atomEnergy z) :
    MemLp (centeredSum (m:=m) X) 4 (seedLaw m) ∧
    lpNorm (centeredSum (m:=m) X) 4 (seedLaw m) ≤ markConstant*D := by
  let f := fun z => D⁻¹*X z
  have hf : Measurable f := hX.const_mul D⁻¹
  have bound (z : Atom) : |f z| ≤ energy z := by
    rw [show |f z|=D⁻¹*|X z| by simp [f,abs_mul,abs_of_pos hD]]
    have hb := mul_le_mul_of_nonneg_left (dom z) (inv_nonneg.mpr hD.le)
    simpa [energy,Fin.sum_univ_three,atomEnergy,← mul_assoc,hD.ne'] using hb
  have h := fourth_unit (m:=m) hm f hf bound
  have eq : centeredSum (m:=m) X = D • centeredSum (m:=m) f := by
    ext ω
    simp only [Pi.smul_apply,smul_eq_mul,centeredSum,sampleAverage,f,←Finset.mul_sum,integral_const_mul]
    field_simp
  rw [eq]
  constructor
  · exact h.1.const_smul _
  · rw [lpNorm_const_smul,coe_nnnorm,Real.norm_eq_abs,abs_of_pos hD,mul_comm]
    exact mul_le_mul_of_nonneg_right h.2 hD.le


private def outputAtom (x : ℝ × ℝ) (z : Atom) :=
  z 0 * max (x.1*z 1+x.2*z 2) 0

private theorem outputAtom_mean (x : ℝ × ℝ) : ∫ z, outputAtom x z ∂atomLaw = 0 := by
  let f := fun w : ℝ × ℝ => max (x.1*w.1 + x.2*w.2) 0
  have ht := CircleInitializationConcentration.readoutSplit_preserving.integral_comp'
    (fun p : ℝ × (ℝ × ℝ) => p.1*f p.2)
  rw [integral_prod_mul (fun a : ℝ => a) f,integral_id_gaussianReal,zero_mul] at ht
  exact ht

theorem output_tail {m : ℕ} (hm : 0 < m) (x : ℝ × ℝ) (hx : UnitInput x) {R : ℝ}
    (hR : 0 ≤ R) (hR' : R ≤ 128*sqrt m) :
    (seedLaw m).real {ω | R ≤ |CircleFlowPath.output (1/sqrt m) ω x|} ≤ 2*exp (-R^2/4096) := by
  have hb (z : Atom) : |outputAtom x z| ≤ energy z := by
    let s : State 1 := fun p => z p.2
    let l := length s 0
    have h₁ : |z 0| ≤ l := CircleTangentDrift.readout_bound s 0
    have h₂ : |max (x.1*z 1+x.2*z 2) 0| ≤ l := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le ((le_abs_self _).trans (CircleTangentDrift.pre_bound s 0 x hx)) (sqrt_nonneg _)
    rw [outputAtom,abs_mul]
    apply (mul_le_mul h₁ h₂ (abs_nonneg _) (sqrt_nonneg _)).trans_eq
    rw [←sq,show l^2 = _ from length_sq s 0]; simp [energy,s,Fin.sum_univ_three]
  have hmeas : Measurable (outputAtom x) := by unfold outputAtom; fun_prop
  have hp : 0 < sqrt (m:ℝ) := by positivity
  have ha := two_sided hm (outputAtom x) hmeas hb (u:=R/sqrt m) (by positivity) ((div_le_iff₀ hp).2 hR')
  rw [outputAtom_mean] at ha
  have eq (ω : Seed m) : sampleAverage (outputAtom x) ω = CircleFlowPath.output (1/sqrt m) ω x / sqrt m := by
    unfold sampleAverage CircleFlowPath.output CircleFlowPath.pre outputAtom
    field_simp
    rw [sq_sqrt (by positivity),mul_comm]
  refine (measureReal_mono (show {ω : Seed m | R ≤ |CircleFlowPath.output (1/sqrt m) ω x|} ⊆ _ from ?_)).trans
    (ha.trans_eq ?_)
  · intro ω hw
    change R/sqrt m ≤ |sampleAverage (outputAtom x) ω-0|
    rw [eq, sub_zero,abs_div,abs_of_pos hp]
    exact div_le_div_of_nonneg_right hw hp.le
  · congr 2
    rw [div_pow, sq_sqrt (by positivity)]; field_simp

/-- The initial RMS grid residual is small whenever all grid predictions are.
The failure probability comes directly from the true independent Gaussian
neurons and is uniform in the choice of phase on the grid. -/
theorem initialRms_tail_exp {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {R : ℝ}
    (hR : 0 ≤ R) (hR' : R ≤ 128*sqrt m) :
    (seedLaw m).real {ω | 2+R < initialRms N m ω} ≤ 2*N*exp (-R^2/4096) := by
  let B (i : Fin N) := {ω : Seed m | R ≤ |CircleFlowPath.output (1/sqrt m) ω (circleInput N i)|}
  have sub : {ω : Seed m | 2+R < initialRms N m ω} ⊆ ⋃ i, B i := by
    intro ω hw
    by_contra h
    have bound (i : Fin N) : |CircleFlowPath.output (1/sqrt m) ω (circleInput N i)| ≤ R :=
      (lt_of_not_ge (fun hi => h (Set.mem_iUnion_of_mem i hi))).le
    let r := residual (circleInput N) (circleLabel N) (1/sqrt m) ω
    have hr (i : Fin N) : r i ^2 ≤ (2+R)^2 := by
      have hsub : |r i| ≤ 2+R := (abs_sub ..).trans ((add_le_add (bound i) (CircleFlowMoments.circle_label_abs N i)).trans_eq (add_comm _ _))
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hsub 2
    have sqb : initialRms N m ω ^2 ≤ (2+R)^2 := by
      change ‖rmsCoordinates r‖^2 ≤ _
      rw [rmsCoordinates_norm_sq,div_le_iff₀ (show 0 < (N:ℝ) by exact_mod_cast hN)]
      simpa [mul_comm] using Finset.sum_le_sum (fun (i:Fin N) (_:i ∈ Finset.univ) => hr i)
    exact (not_lt_of_ge ((sq_le_sq₀ (norm_nonneg _) (by linarith)).1 sqb)) hw
  refine (measureReal_mono sub).trans ((measureReal_iUnion_fintype_le B).trans
    ((Finset.sum_le_sum (fun i _ => output_tail hm _ (grid_unit i) hR hR')).trans_eq ?_))
  simp; ring

/-- Any fixed polynomial failure exponent is available once m is at least
(k+1) log N / 4. This holds eventually for m=N³² and every fixed k. -/
theorem initialRms_polynomial {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (k : ℕ)
    (width : ((k:ℝ)+1)*log N ≤ 4*m) :
    (seedLaw m).real {ω | 2+64*sqrt (((k:ℝ)+1)*log N) < initialRms N m ω} ≤ 2 / (N:ℝ)^k := by
  have n1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have nl : 0 ≤ log (N:ℝ) := log_nonneg n1
  have nr : 0 < (N:ℝ) := by positivity
  let a := ((k:ℝ)+1)*log N
  have ha : 0 ≤ a := mul_nonneg (by positivity) nl
  have hc : 64*sqrt a ≤ 128*sqrt m := by
    have h : sqrt a ≤ 2*sqrt m := by
      apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).1
      rw [sq_sqrt ha,mul_pow,sq_sqrt (by positivity)]; linarith
    linarith
  apply (initialRms_tail_exp hN hm (R:=64*sqrt a) (by positivity) hc).trans_eq
  rw [show -(64*sqrt a)^2/4096 = -a by rw [mul_pow,sq_sqrt ha]; ring,exp_neg]
  dsimp [a]
  rw [add_mul,one_mul,exp_add,Real.exp_nat_mul, exp_log nr]; field_simp



/-- Every prescribed inverse power on the paired width schedule. -/
theorem initialRms_schedule_tail {N : ℕ} (k : ℕ) (h : k+1 ≤ N) :
    (seedLaw (N^32)).real {ω | 2+64*sqrt (((k:ℝ)+1)*log N) < initialRms N (N^32) ω} ≤ 2/(N:ℝ)^k := by
  have hn : 0 < N := by omega
  have n1 : 1 ≤ (N:ℝ) := by exact_mod_cast hn
  apply initialRms_polynomial hn (by positivity)
  push_cast
  calc
    _ ≤ (N:ℝ)*N := mul_le_mul (by exact_mod_cast h) (log_le_self (Nat.cast_nonneg N)) (log_nonneg n1) (Nat.cast_nonneg _)
    _ ≤ (N:ℝ)^32 := by rw [←sq]; exact pow_le_pow_right₀ n1 (by decide)
    _ ≤ _ := by linarith [show (0:ℝ)≤(N:ℝ)^32 by positivity]

def finiteRms {ι : Type*} [Fintype ι] (v : ι → ℝ) :=
  sqrt ((∑ i, v i^2) / Fintype.card ι)

theorem finiteRms_fourth {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (F : ι → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ i, MemLp (F i) 4 μ ∧ lpNorm (F i) 4 μ ≤ C) :
    MemLp (fun ω => finiteRms (fun i => F i ω)) 4 μ ∧
    lpNorm (fun ω => finiteRms (fun i => F i ω)) 4 μ ≤ C := by
  let n := (Fintype.card ι:ℝ)
  have hn : 0<n := Nat.cast_pos.mpr Fintype.card_pos
  let r := fun ω => finiteRms (fun i => F i ω)
  have ha : AEStronglyMeasurable r μ := by
    have hs := memLp_finsetSum Finset.univ (fun i _ => CircleGaussianTracking.square_mem (hF i).1)
    have hsum := (hs.mul_const n⁻¹).aestronglyMeasurable
    simpa only [r,finiteRms,n,div_eq_mul_inv,Function.comp_def] using Real.continuous_sqrt.comp_aestronglyMeasurable hsum
  have cap (ω : Ω) : r ω^4 ≤ n⁻¹ * ∑ i, F i ω^4 := by
    have w := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun _ : ι => n⁻¹)
      (fun i => F i ω^2) (by intros; positivity) (by simp [n,Fintype.card_ne_zero])
      (fun _ _ => sq_nonneg _) 2
    simp only [←pow_mul,←Finset.mul_sum] at w
    change sqrt ((∑ i, F i ω^2)/n)^4 ≤ _
    rw [show (4:ℕ)=2*2 by decide,pow_mul, sq_sqrt (by positivity),div_eq_inv_mul]
    exact w
  have fi i : Integrable (fun ω => F i ω^4) μ := by
    have hf : MemLp (F i) (4:ℕ) μ := (hF i).1
    simpa [Real.norm_eq_abs,(by decide : Even 4).pow_abs] using hf.integrable_norm_pow'
  have hi := (integrable_finsetSum Finset.univ (fun i _ => fi i)).const_mul n⁻¹
  have hr : Integrable (fun ω => r ω^4) μ := hi.mono' (ha.pow _) (ae_of_all _ (fun ω => by
    simpa [Real.norm_eq_abs,(by decide : Even 4).pow_abs] using cap ω))
  have hm : MemLp r 4 μ := by
    apply (integrable_norm_rpow_iff ha (by norm_num : (4:ENNReal)≠0) (by norm_num)).1
    simpa [Real.norm_eq_abs,(by decide : Even 4).pow_abs] using hr
  have h := integral_mono hr hi cap
  rw [CircleGaussianTracking.fourth_integral hm,integral_const_mul,integral_finsetSum _ (fun i _ => fi i)] at h
  have ub (i : ι) : (∫ ω, F i ω ^4 ∂μ) ≤ C^4 := by
    rw [CircleGaussianTracking.fourth_integral (hF i).1]
    exact pow_le_pow_left₀ lpNorm_nonneg (hF i).2 4
  have h' := h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ub i)) (inv_nonneg.mpr hn.le))
  have he : n⁻¹ * (∑ _ : ι, C^4) = C^4 := by simp [n,Fintype.card_ne_zero]
  rw [he] at h'
  exact ⟨hm,(pow_le_pow_iff_left₀ lpNorm_nonneg hC (by decide : 4 ≠ 0)).mp h'⟩

private theorem avg_deviation {m : ℕ} (hm : 0 < m) (X : Atom → ℝ) (hX : Measurable X)
    (dom : ∀ z, |X z| ≤ 3*atomEnergy z) :
    let F := fun ω : Seed m => sampleAverage X ω - ∫ z, X z ∂atomLaw
    MemLp F 4 (seedLaw m) ∧ lpNorm F 4 (seedLaw m) ≤ (3*markConstant)/sqrt m := by
  have h := average_fourth hm X hX (by norm_num) dom
  have hp : 0 < sqrt (m:ℝ) := by positivity
  let f := fun ω : Seed m => sampleAverage X ω - ∫ z, X z ∂atomLaw
  have eq : f = (sqrt (m:ℝ))⁻¹ • centeredSum (m:=m) X := by
    ext ω; simp [f,centeredSum,hp.ne']
  change MemLp f 4 _ ∧ lpNorm f 4 _ ≤ _
  rw [eq]
  constructor
  · exact h.1.const_smul _
  · rw [lpNorm_const_smul,coe_nnnorm,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hp.le)
    simpa [mul_comm] using h.2

open CircleGridSpectrum CircleSpectrum

/-- Sum of normalized empirical Gram Frobenius and population-row RMS errors.
Both differences are computed from the actual initial gates and spectral centers. -/
def initialError (N m : ℕ) [NeZero N] (τ : ℝ) (ω : Seed m) :=
  finiteRms (fun q : Fin N × Fin N => gridGram τ ω (startGates ω) q.1 q.2 - sampledMatrix τ q.1 q.2) +
  finiteRms (fun j : Fin N => populationRow τ ω (startGates ω) j - k0 τ)

theorem initialError_fourth {N m : ℕ} [NeZero N] (hm : 0 < m) (τ : ℝ) (hτ : |τ| ≤ 2) :
    MemLp (initialError N m τ) 4 (seedLaw m) ∧
    lpNorm (initialError N m τ) 4 (seedLaw m) ≤ 6*markConstant/sqrt m := by
  let D := 3*markConstant/sqrt m
  have hD : 0 ≤ D := by dsimp [D,markConstant]; positivity
  let F := fun (q : Fin N × Fin N) (ω : Seed m) => gridGram τ ω (startGates ω) q.1 q.2 - sampledMatrix τ q.1 q.2
  let H := fun (i : Fin N) (ω : Seed m) => populationRow τ ω (startGates ω) i - k0 τ
  have hG (q : Fin N × Fin N) : MemLp (F q) 4 (seedLaw m) ∧ lpNorm (F q) 4 (seedLaw m) ≤ D := by
    let idx : InitIndex N := .inr (.inr (q.2,some q.1))
    let X := initTest N τ 0 idx
    have h := avg_deviation (m:=m) hm X (initTest_meas ..) (initTest_cap N τ 0 hτ idx)
    have eq (ω : Seed m) : F q ω = sampleAverage X ω - ∫ z, X z ∂atomLaw := by
      have hd := weightedAtom_initial hm τ (circleInput N q.1) (circleInput N q.2) ω
      change _ - sampledMatrix τ q.1 q.2 = _
      rw [←populationGram_sampled]
      exact congrArg (·-populationGram N τ q.1 q.2) hd
    rwa [show F q = _ from funext eq]
  have hR (i : Fin N) : MemLp (H i) 4 (seedLaw m) ∧ lpNorm (H i) 4 (seedLaw m) ≤ D := by
    let idx : InitIndex N := .inr (.inr (i,none))
    let X := initTest N τ 0 idx
    have h := avg_deviation (m:=m) hm X (initTest_meas ..) (initTest_cap N τ 0 hτ idx)
    have eq (ω : Seed m) : H i ω = sampleAverage X ω - ∫ z, X z ∂atomLaw := by
      dsimp [H]
      rw [CircleInitializationConcentration.angular_entry_initial hm,←populationMeanRow_constant (N:=N) τ i]
      rfl
    rwa [show H i = _ from funext eq]
  have g := finiteRms_fourth F D hD hG
  have r := finiteRms_fourth H D hD hR
  exact ⟨g.1.add r.1,(lpNorm_add_le g.1 (by norm_num)).trans ((add_le_add g.2 r.2).trans_eq (by dsimp [D];ring))⟩


theorem rowOp_le_rms {N : ℕ} (h : Fin N → ℝ) :
    ‖rowOp h‖ ≤ finiteRms h := by
  have eq : ‖rmsCoordinates h‖ = finiteRms h := by
    rw [←Real.sqrt_sq (norm_nonneg _),rmsCoordinates_norm_sq]
    simp [finiteRms]
  apply ContinuousLinearMap.opNorm_le_bound _ (sqrt_nonneg _)
  intro r
  exact (abs_real_inner_le_norm (rmsCoordinates h) r).trans_eq (congrArg (·*‖r‖) eq)

theorem gramOp_le_rms {N : ℕ} (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℝ) :
    ‖gramOp A‖ ≤ finiteRms (fun q : Fin N × Fin N => A q.1 q.2) := by
  let M := finiteRms (fun q : Fin N × Fin N => A q.1 q.2)
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hM : 0 ≤ M := sqrt_nonneg _
  have hsq : M^2 = (∑ i, ∑ j, A i j^2)/(N:ℝ)^2 := by
    change (sqrt _)^2 = _
    rw [sq_sqrt (by positivity),Fintype.sum_prod_type]
    simp [sq]
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro r
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).1
  rw [mul_pow,hsq,EuclideanSpace.real_norm_sq_eq]
  have each (i : Fin N) : ((gramOp A r) i)^2 ≤ ((∑ j, A i j^2)*‖r‖^2)/(N:ℝ)^2 := by
    rw [gramOp_apply,div_pow,EuclideanSpace.real_norm_sq_eq]
    exact div_le_div_of_nonneg_right (Finset.sum_mul_sq_le_sq_mul_sq _ _ _) (sq_nonneg _)
  apply (Finset.sum_le_sum (fun i _ => each i)).trans_eq
  rw [←Finset.sum_div,←Finset.sum_mul]; ring

theorem initial_operators_le {N m : ℕ} [NeZero N] (τ : ℝ) (ω : Seed m) :
    ‖gramOp (gridGram τ ω (startGates ω)) - gramOp (sampledMatrix (N:=N) τ)‖ +
    ‖rowOp (populationRow τ ω (startGates ω)) - rowOp (fun _ : Fin N => k0 τ)‖ ≤ initialError N m τ ω := by
  rw [← gramOp_sub,←rowOp_sub]
  exact add_le_add (gramOp_le_rms (Nat.pos_of_ne_zero (NeZero.ne N)) _) (rowOp_le_rms _)



theorem finiteRms_le {ι : Type*} [Fintype ι] [Nonempty ι] {C : ℝ} (hC : 0 ≤ C) (f : ι → ℝ)
    (hf : ∀ i, |f i| ≤ C) : finiteRms f ≤ C := by
  apply (Real.sqrt_le_iff).2 ⟨hC,?_⟩
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Fintype.card_pos (α:=ι)) : 0 < (Fintype.card ι:ℝ))).2
  refine (Finset.sum_le_sum (g:=fun _ => C^2) (fun i _ => ?_)).trans_eq ?_
  · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hf i) 2
  · simp [mul_comm]

theorem initialError_nonneg {N m : ℕ} [NeZero N] (τ : ℝ) (ω : Seed m) : 0 ≤ initialError N m τ ω :=
  add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)

theorem initialError_le_of_good {N m : ℕ} [NeZero N] {τ ρ u : ℝ} {ω : Seed m} (hu : 0 ≤ u)
    (G : GoodInit τ ρ u (sampledMatrix τ) (fun _ : Fin N => k0 τ) ω) :
    initialError N m τ ω ≤ 4*u := by
  let f := fun q : Fin N × Fin N => gridGram τ ω (startGates ω) q.1 q.2 - sampledMatrix τ q.1 q.2
  let r := fun j : Fin N => populationRow τ ω (startGates ω) j - k0 τ
  have a : finiteRms f ≤ 2*u := finiteRms_le (by positivity) f (fun q => G.gram q.1 q.2)
  have b : finiteRms r ≤ 2*u := finiteRms_le (by positivity) r G.mean
  change finiteRms f + finiteRms r ≤ _
  linarith

theorem paired_initialError_fourth {N m : ℕ} [NeZero N] (hm : 0 < m) :
    let B := fun ω => initialError N m (1/2) ω + initialError N m 2 ω
    MemLp B 4 (seedLaw m) ∧ lpNorm B 4 (seedLaw m) ≤ 12*markConstant/sqrt m := by
  have h := initialError_fourth (N:=N) hm (1/2) (by norm_num)
  have h' := initialError_fourth (N:=N) hm 2 (by norm_num)
  exact ⟨h.1.add h'.1, (lpNorm_add_le h.1 (by norm_num)).trans ((add_le_add h.2 h'.2).trans_eq (by ring))⟩

end CircleSharpInitialization
