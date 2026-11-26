module

public import CircleSharpTracking
public import CircleComparison
import all CircleComparison
import all CircleSharpInitialization
public import CircleSharpEvent
import all CircleGaussianTracking
import Mathlib.Tactic

/-! Fourth-moment products and the final unconditional error estimate on the
original Gaussian measure. The probability of the exceptional seeds multiplies
the actual flow fourth norm. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal
namespace CircleSharpMoments
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private instance : ENNReal.HolderTriple 4 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num⟩

omit [IsProbabilityMeasure μ] in
private theorem product_norm {b v : Ω → ℝ} (hb : MemLp b 4 μ) (hv : MemLp v 4 μ) :
    lpNorm (fun x => b x*v x) 2 μ ≤ lpNorm b 4 μ*lpNorm v 4 μ := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm (p:=4) (q:=4) (r:=2) (· * · : ℝ → ℝ → ℝ) 1
    continuous_mul hb.aestronglyMeasurable hv.aestronglyMeasurable
    (ae_of_all _ fun x => by simp)
  simp only [ENNReal.coe_one,one_mul] at h
  simpa only [ENNReal.toReal_mul,toReal_eLpNorm] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hb.eLpNorm_ne_top hv.eLpNorm_ne_top) h

private theorem probability_const (c : ℝ) (q : ENNReal) (hq : q ≠ 0) :
    lpNorm (fun _ : Ω => c) q μ = |c| := by
  rw [lpNorm_const hq (IsProbabilityMeasure.ne_zero _)]
  simp

omit [IsProbabilityMeasure μ] in
private theorem scale (c : ℝ) (f : Ω → ℝ) (q : ENNReal) :
    lpNorm (fun ω => c*f ω) q μ = |c| * lpNorm f q μ := lpNorm_const_smul c f μ

private theorem envelope {B V : Ω → ℝ} (hB : MemLp B 4 μ) (hV : MemLp V 4 μ)
    (w : ℝ) (hw : 0 ≤ w) :
    let E := fun x => 6*(B x*V x)+(44928*w)*((1+V x)*V x)+w
    MemLp E 2 μ ∧ lpNorm E 2 μ ≤
      6*lpNorm B 4 μ*lpNorm V 4 μ + 44928*w*(1+lpNorm V 4 μ)*lpNorm V 4 μ + w := by
  let BV := fun x => B x*V x
  let VV := fun x => (1+V x)*V x
  have h1 : MemLp (fun x => 1+V x) 4 μ := (memLp_const 1).add hV
  have hBV : MemLp BV 2 μ := hB.mul hV
  have hVV : MemLp VV 2 μ := h1.mul hV
  have norm1 : lpNorm (fun x => 1+V x) 4 μ ≤ 1+lpNorm V 4 μ := by
    simpa only [Pi.add_def,probability_const (μ:=μ) 1 4 (by norm_num),abs_one] using
      lpNorm_add_le (memLp_const (μ:=μ) (p:=4) (1:ℝ)) (g:=V) (by norm_num)
  have nBV : lpNorm BV 2 μ ≤ lpNorm B 4 μ*lpNorm V 4 μ := product_norm hB hV
  have nVV : lpNorm VV 2 μ ≤ (1+lpNorm V 4 μ)*lpNorm V 4 μ :=
    (product_norm h1 hV).trans (mul_le_mul_of_nonneg_right norm1 lpNorm_nonneg)
  have b1 := hBV.const_mul 6
  have b2 := hVV.const_mul (44928*w)
  have s := lpNorm_add_le b1 (g:=fun x => (44928*w)*VV x) (by norm_num)
  have q := lpNorm_add_le (b1.add b2) (g:=fun _ => w) (by norm_num)
  simp only [Pi.add_def,scale,abs_of_nonneg hw,abs_of_nonneg (show 0≤44928*w by positivity),
    abs_of_nonneg (by norm_num : (0:ℝ)≤6),probability_const (μ:=μ) w 2 (by norm_num)] at s q
  refine ⟨(b1.add b2).add (memLp_const w), ?_⟩
  change lpNorm (fun x => 6*BV x+44928*w*VV x+w) 2 μ ≤ _
  linarith [mul_le_mul_of_nonneg_left nVV (show 0≤44928*w from by positivity)]

omit [IsProbabilityMeasure μ] in
private theorem rms_eq {f : Ω → ℝ} (h : MemLp f 2 μ) :
    sqrt (∫ x, f x^2 ∂μ) = lpNorm f 2 μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) h.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  norm_cast
  simp [Real.sqrt_eq_rpow,one_div]

/-- Price of an exceptional set when the error bound on its complement
is a random variable correlated with the output. -/
theorem random_envelope_split {E D : Ω → ℝ} (hD : MemLp D 4 μ) (hE : MemLp E 2 μ)
    (posE : ∀ ω, 0 ≤ E ω) {G : Set Ω} (hG : MeasurableSet G)
    (good : ∀ ω ∈ G, |D ω| ≤ E ω) :
    sqrt (∫ ω, D ω^2 ∂μ) ≤ lpNorm E 2 μ + lpNorm D 4 μ*sqrt (sqrt (μ.real Gᶜ)) := by
  have d2 : MemLp D 2 μ := hD.mono_exponent (by norm_num)
  let A := G.indicator D
  let B := Gᶜ.indicator D
  have heq : D = A+B := by
    ext x
    by_cases hx : x∈G <;> simp [A,B,hx]
  have a : lpNorm A 2 μ ≤ lpNorm E 2 μ := by
    apply lpNorm_mono_real hE
    intro x
    by_cases hx : x∈G
    · simpa [A,hx,Real.norm_eq_abs] using good x hx
    · simpa [A,hx] using posE x
  have bad := CircleMoment.exceptional_second_moment (CircleGaussianTracking.square_mem hD) Gᶜ
  rw [CircleGaussianTracking.fourth_integral hD] at bad
  have b : lpNorm B 2 μ ≤ lpNorm D 4 μ * sqrt (sqrt (μ.real Gᶜ)) := by
    rw [← rms_eq (f:=B) (d2.indicator hG.compl.nullMeasurableSet)]
    have point (x : Ω) : B x^2 = Gᶜ.indicator (fun y => D y^2) x := by
      by_cases h : x∈Gᶜ <;> simp [B,h]
    simp_rw [point]
    rw [integral_indicator hG.compl]
    have h := sqrt_le_sqrt bad
    rw [sqrt_mul (sqrt_nonneg _),show lpNorm D 4 μ^4 = ((lpNorm D 4 μ)^2)^2 by ring,
      sqrt_sq (sq_nonneg _),sqrt_sq lpNorm_nonneg] at h
    exact h
  rw [rms_eq d2]
  calc
    _ = lpNorm (A+B) 2 μ := congrArg (fun f => lpNorm f 2 μ) heq
    _ ≤ _ := (lpNorm_add_le (d2.indicator hG.nullMeasurableSet) (by norm_num)).trans (add_le_add a b)


private theorem collect_bounds {n b v d cb cv cd p : ℝ} (hn : 1 ≤ n)
    (nv : 0 ≤ v) (ncb : 0 ≤ cb) (ncv : 0 ≤ cv) (ncd : 0 ≤ cd)
    (hb : b ≤ cb/n^16) (hv : v ≤ cv*sqrt n) (hd : d ≤ cd*n*sqrt n) (hp : p ≤ 14/n^68) :
    6*b*v + 44928*(1/n^16)*(1+v)*v + 1/n^16 + d*sqrt (sqrt p) ≤
      (6*cb*cv + 44928*(cv+cv^2) + 1 + 2*cd)/n^15 := by
  have nx : 0 < n := by linarith
  have ns := sqrt_nonneg n
  have hs : sqrt n ≤ n := (sqrt_le_iff.mpr ⟨nx.le,by nlinarith [mul_nonneg (sub_nonneg.mpr hn) nx.le]⟩)
  have hvs : v ≤ cv*n := hv.trans (mul_le_mul_of_nonneg_left hs ncv)
  have hsq : v^2 ≤ cv^2*n := by
    simpa only [mul_pow,sq_sqrt nx.le] using pow_le_pow_left₀ nv hv 2
  have hh : (1+v)*v ≤ (cv+cv^2)*n := by nlinarith
  have hp' : sqrt (sqrt p) ≤ 2/n^17 := by
    have h0 : 14/n^68 ≤ ((2/n^17)^2)^2 := by
      calc
        _ ≤ 16/n^68 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
        _ = _ := by field_simp; norm_num
    have h := sqrt_le_sqrt (sqrt_le_sqrt (hp.trans h0))
    simpa only [sqrt_sq (by positivity : 0 ≤ (2/n^17)^2),sqrt_sq (by positivity : 0 ≤ 2/n^17)] using h
  have hds : d ≤ cd*n^2 := hd.trans (by rw [sq,mul_assoc]; gcongr)
  have prod := mul_le_mul hb hvs nv (div_nonneg ncb (by positivity))
  have vv := mul_le_mul_of_nonneg_left hh (show 0≤44928*(1/n^16) by positivity)
  have exc := mul_le_mul hds hp' (sqrt_nonneg _) (by positivity)
  have algebra : 6*(cb/n^16*(cv*n)) + 44928*(1/n^16)*((cv+cv^2)*n) +
      n/n^16 + (cd*n^2)*(2/n^17) = (6*cb*cv+44928*(cv+cv^2)+1+2*cd)/n^15 := by
    field_simp
  rw [← algebra]
  have hsmall := div_le_div_of_nonneg_right hn (by positivity : 0≤n^16)
  linarith

open CircleFlowMoments CircleFlowTracking CircleGaussianTracking CircleSharpInitialization
open CircleEscapeBridge CircleSpectralPathLength CircleComparison CircleSharpTracking

/-- An absolute constant, independent of the grid, choice of flow and hidden
rate throughout [1/2,2]. Its individual factors are fourth-moment bounds
on centered Gram errors, frozen residual path length and the nonlinear flow. -/
def trackingConstant : ℝ :=
  6*(6*markConstant)*budgetConstant + 44928*(budgetConstant+budgetConstant^2)+1+2*horizonMomentConstant

set_option maxHeartbeats 400000 in
/-- Long-horizon unconditional sharp RMS theorem for the actual network,
compared with the fitted population kernel reference on the same Gaussian
seed. The quantifier covers every measurable valid flow, including equal-rate
gradient flow. Existence of such learners is proved by learner_exists. -/
theorem sharp_tracking (n : ℕ) (hN : 36864 ≤ n+1) (ho : Odd (n+1))
    {τ : ℝ} (hτ : 1/2 ≤ τ) (hτ' : τ ≤ 2) (F : Benchmark n τ) :
    sqrt (∫ ω, (trained n F ω - matched n τ ω)^2 ∂seedLaw ((n+1)^32)) ≤
      trackingConstant / ((n:ℝ)+1)^15 := by
  let N := n+1
  let m := N^32
  let x := ((n:ℝ)+1)
  let μ := seedLaw m
  let B := initialError N m τ
  let V := seedBudget ho m
  let D := fun ω => trained n F ω - matched n τ ω
  let w := 1/x^16
  have hx : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hxp : 0 < x := by linarith
  have hm : 0 < m := pow_pos (Nat.succ_pos n) _
  have hxN : (N:ℝ) = x := Nat.cast_add_one n
  have hmx : sqrt (m:ℝ) = x^16 := by
    rw [show (m:ℝ)=x^32 by dsimp [m]; rw [Nat.cast_pow,hxN],show x^32=(x^16)^2 by ring,sqrt_sq (by positivity)]
  have hpos : 0 < τ := by linarith
  have τabs : |τ| ≤ 2 := abs_le.mpr ⟨by linarith,hτ'⟩
  have hb := initialError_fourth (N:=N) hm τ τabs
  have hv := seedBudget_mem hm ho
  have wb := weight_bounds n hpos.le
  have hd := horizon_fourth (N:=N) (Nat.succ_pos n) hpos hτ' wb.1 wb.2 F.path F.start
    (F.flow _ (Nat.cast_nonneg _)) (F.endpoint _ (Nat.cast_nonneg _))
  dsimp only at hd
  rw [hxN] at hd
  change MemLp D 4 μ ∧ lpNorm D 4 μ ≤ horizonMomentConstant*x*sqrt x at hd
  obtain ⟨G,meas,prob,good⟩ := gaussian_spectral_endpoint n 68 hN (by omega) ho τ hτ hτ'
  let E := fun ω => 6*(B ω*V ω)+(44928*w)*((1+V ω)*V ω)+w
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hE := envelope hb.1 hv w hw
  have posB (ω : Seed m) : 0 ≤ B ω := by
    dsimp only [B,initialError,finiteRms]; positivity
  have posV (ω : Seed m) : 0 ≤ V ω := seedBudget_nonneg ho m ω
  have g (ω : Seed m) (pass : ω∈G) : |D ω| ≤ E ω := by
    have ft := F.flow (horizon x) (Nat.cast_nonneg _) ω
    have hh := good ω pass (F.path ω) (F.start ω) ft
    change |D ω| ≤ 6*B ω*V ω+44928*(1+V ω)*V ω/x^16+1/x^16 at hh
    exact hh.trans_eq (by dsimp [E,w]; ring)
  have ep (ω : Seed m) : 0 ≤ E ω := by
    have bp := posB ω
    have vp := posV ω
    dsimp only [E]
    positivity
  have bound := random_envelope_split hd.1 hE.1 ep meas g
  apply bound.trans ((add_le_add hE.2 le_rfl).trans ?_)
  change 6*lpNorm B 4 μ*lpNorm V 4 μ+44928*(1/x^16)*(1+lpNorm V 4 μ)*lpNorm V 4 μ+1/x^16+
    lpNorm D 4 μ*sqrt (sqrt (μ.real Gᶜ)) ≤ _
  have bbound : lpNorm B 4 μ ≤ (6*markConstant)/x^16 := hb.2.trans_eq (by rw [hmx])
  have vbound : lpNorm V 4 μ ≤ budgetConstant*sqrt x :=
    (seedBudget_lp4 hm ho).trans_eq (by rw [hxN])
  have dbound : lpNorm D 4 μ ≤ horizonMomentConstant*x*sqrt x := hd.2
  have cpos : 0 ≤ horizonMomentConstant := by
    by_contra! neg
    have v := lpNorm_nonneg (f:=D) (p:=4) (μ:=μ)
    exact (not_lt_of_ge (v.trans dbound)) (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos neg hxp)
      (sqrt_pos.mpr hxp))
  exact collect_bounds hx lpNorm_nonneg
    (by dsimp [markConstant]; positivity) budgetConstant_nonneg cpos bbound vbound dbound prob

end CircleSharpMoments
