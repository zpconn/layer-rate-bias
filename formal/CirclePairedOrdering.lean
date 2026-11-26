module

public import CirclePairedCoefficient
public import CircleSphereBand
import all CircleSphereBand
public import CircleReadoutMixing
public import CircleMixingEnvelopes
public import CircleDiscreteMoments
public import CircleFiniteCoefficient
public import CircleScoreMargin
public import CircleSharpMoments
public import CircleSharpTracking
import all CirclePairedCoefficient
import all CircleSharpMoments
import all CircleFiniteCoefficient
import all CircleScoreMargin
import all CircleGaussianTracking
import all CircleFlowMoments
import all CircleEscapeBridge
import all CircleSharpTracking
import all CircleSpectralPathLength
import all CircleResidualSpectrum
import all CircleSharpInitialization
import all CircleGaussianBernstein
import all CircleInitializationConcentration
import all CircleFlowPath
import Mathlib.Tactic

/-! Ordering of actual same-seed circle flows, including ties in the error event. -/

public section
noncomputable section
namespace CirclePairedOrdering
open Real MeasureTheory Set Filter Topology CircleEscapeBridge CircleFlowPath CircleSpectrum
  CircleGaussianTracking CirclePairedCoefficient CircleFiniteCoefficient CircleScoreMargin CircleFlowTracking

def coefficient (n : ℕ) := ((n:ℝ)+1)^2*(weight (1/2) n-weight 2 n)

def difference (n : ℕ) (z : Family (n+1)) (ω : Seed ((n+1)^32)) :=
  ((n:ℝ)+1)^2*(endpoint n z false ω-endpoint n z true ω)

def miss (n : ℕ) (z : Family (n+1)) : Set (Seed ((n+1)^32)) :=
  {ω | difference n z ω * score (n+1) ((n+1)^32) ω ≤ 0}

theorem coefficient_pos (n : ℕ) : 0<coefficient n :=
  mul_pos (by positivity) (weight_difference_pos n)

theorem coefficient_eventually : ∀ᶠ n : ℕ in atTop, π^2/80 ≤ coefficient n := by
  have h := CircleLayerRates.coefficient_limit.eventually (eventually_ge_nhds
    (show π^2/80<π^2/40 by nlinarith [sq_pos_of_pos pi_pos]))
  exact h

theorem score_eq (N m : ℕ) (ω : Seed m) : score N m ω = 1-gridMean N m ω := by
  simp only [score,gridMean,CircleFlowMoments.output_eq_complex]
  ring

private theorem identity (n : ℕ) (z : Family (n+1)) (ω : Seed ((n+1)^32)) :
    difference n z ω - coefficient n * score (n+1) ((n+1)^32) ω =
    ((n:ℝ)+1)^2*(discrepancy n z false ω-discrepancy n z true ω) := by
  simp only [difference,coefficient,discrepancy,endpoint,reference,benchmarkRate,
    Bool.false_eq_true,ite_false,ite_true,score]
  ring

private theorem wrong_forces_error {D X c : ℝ} (hc : 0<c) (h : D*X≤0) :
    c*|X|≤|D-c*X| := by
  apply (sq_le_sq₀ (mul_nonneg hc.le (abs_nonneg X)) (abs_nonneg _)).1
  rw [mul_pow,sq_abs,sq_abs]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hc.le h,sq_nonneg D]

/-- If both endpoint errors are bounded on the same event, then every
wrongly ordered pair there has a small grid score. -/
theorem event_miss (n : ℕ) (z : Family (n+1)) (G : Set (Seed ((n+1)^32))) (e δ : ℝ)
    (hδ : 0≤δ) (hδ' : δ≤1/2)
    (hcap : 2*((n:ℝ)+1)^2*e ≤ coefficient n*δ)
    (hG : ∀ ω∈G, ∀ q, |discrepancy n z q ω|≤e) :
    (seedLaw ((n+1)^32)).real (miss n z) ≤
      (seedLaw ((n+1)^32)).real Gᶜ + 2*δ*densityBound := by
  have hh : miss n z ⊆ Gᶜ ∪ {ω | |1-gridMean (n+1) ((n+1)^32) ω|≤δ} := by
    intro ω hw
    by_cases hg : ω∈G
    · right
      change |1-gridMean (n+1) ((n+1)^32) ω|≤δ
      rw [←score_eq]
      apply le_of_mul_le_mul_left _ (coefficient_pos n)
      apply (wrong_forces_error (coefficient_pos n) hw).trans
      rw [identity,abs_mul,abs_of_nonneg (sq_nonneg _)]
      apply le_trans _ hcap
      have h1 := (abs_sub _ _).trans (add_le_add (hG ω hg false) (hG ω hg true))
      nlinarith only [mul_le_mul_of_nonneg_left h1 (sq_nonneg ((n:ℝ)+1))]
    · exact Or.inl hg
  exact (measureReal_mono hh).trans ((measureReal_union_le _ _).trans
    (add_le_add le_rfl (gridMean_near_tie _ _ hδ hδ')))

theorem event_margin (n : ℕ) (z : Family (n+1)) (G : Set (Seed ((n+1)^32))) (e δ : ℝ)
    (hcap : 2*((n:ℝ)+1)^2*e < coefficient n*δ)
    (hG : ∀ ω∈G, ∀ q, |discrepancy n z q ω|≤e) :
    (seedLaw ((n+1)^32)).real (miss n z ∩ {ω | δ≤|score (n+1) ((n+1)^32) ω|}) ≤
      (seedLaw ((n+1)^32)).real Gᶜ := by
  refine measureReal_mono ?_
  intro ω h hg
  have h1 := (abs_sub _ _).trans (add_le_add (hG ω hg false) (hG ω hg true))
  have h2 := wrong_forces_error (coefficient_pos n) h.1
  rw [identity,abs_mul,abs_of_nonneg (sq_nonneg ((n:ℝ)+1))] at h2
  have hm : δ≤|score (n+1) ((n+1)^32) ω| := h.2
  nlinarith only [mul_le_mul_of_nonneg_left h1 (sq_nonneg ((n:ℝ)+1)),
    mul_le_mul_of_nonneg_left hm (coefficient_pos n).le,hcap,h2]

private theorem score_measurable (N m : ℕ) : Measurable (score N m) := by
  simp_rw [funext (score_eq N m)]
  unfold gridMean CircleFlowPath.output CircleFlowPath.pre
  fun_prop

theorem fixed_margin (n : ℕ) (hn : 3≤n+1) (z : Family (n+1))
    (meas : ∀ q, Measurable fun ω => z q ω (horizon (n+1)))
    (hm : ∀ q, MemLp (discrepancy n z q) 2 (seedLaw ((n+1)^32))) {δ : ℝ} (hδ : 0<δ) :
    (seedLaw ((n+1)^32)).real (miss n z ∩ {ω | δ≤|score (n+1) ((n+1)^32) ω|}) ≤
      (((n:ℝ)+1)^2*(rmsError n z false+rmsError n z true)/(coefficient n*δ))^2 := by
  let μ := seedLaw ((n+1)^32)
  let X := score (n+1) ((n+1)^32)
  let D := difference n z
  let a := ((n:ℝ)+1)^2
  have hd : Measurable D := measurable_const.mul ((CircleFlowMoments.mean_measurable.comp (meas false)).sub
    (CircleFlowMoments.mean_measurable.comp (meas true)))
  have hx : Measurable X := score_measurable _ _
  have he : MemLp (fun ω => D ω - coefficient n*X ω) 2 μ := by
    have h : (fun ω => D ω-coefficient n*X ω)=a • (discrepancy n z false-discrepancy n z true) := funext (identity n z)
    rw [h]
    exact ((hm false).sub (hm true)).const_smul _
  have hi : Integrable (fun ω => (D ω-coefficient n*X ω)^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using (he.integrable_norm_pow (by decide : 2≠0))
  have E := CircleLayerRates.sign_error_mass μ D X (coefficient n) δ (coefficient_pos n) hδ
    (miss n z ∩ {ω | δ≤|X ω|}) ((measurableSet_le (hd.mul hx) measurable_const).inter
      (measurableSet_le measurable_const (continuous_abs.measurable.comp hx))) (fun ω hw => ⟨hw.2,by rw [mul_comm]; exact hw.1⟩) hi
  apply E.trans
  rw [div_pow]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have h := scaled_reference_error n hn z hm
  have hnon : 0≤ ∫ ω, (D ω-coefficient n*X ω)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have h' := sq_le_sq₀ (sqrt_nonneg _) (show 0≤a*(rmsError n z false+rmsError n z true) from
    mul_nonneg (sq_nonneg _) (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _))) |>.2 h
  change (√(∫ ω, (D ω-coefficient n*X ω)^2 ∂μ))^2 ≤ _ at h'
  rwa [sq_sqrt hnon] at h'

theorem total_from_rms (n : ℕ) (hn : 3≤n+1) (z : Family (n+1))
    (meas : ∀ q, Measurable fun ω => z q ω (horizon (n+1)))
    (hm : ∀ q, MemLp (discrepancy n z q) 2 (seedLaw ((n+1)^32))) {δ : ℝ} (hδ : 0<δ) (hu : δ≤1/2) :
    (seedLaw ((n+1)^32)).real (miss n z) ≤
      (((n:ℝ)+1)^2*(rmsError n z false+rmsError n z true)/(coefficient n*δ))^2+2*δ*densityBound := by
  let X := score (n+1) ((n+1)^32)
  have hs : miss n z ⊆ (miss n z ∩ {ω | δ≤|X ω|}) ∪ {ω | |1-gridMean (n+1) ((n+1)^32) ω|≤δ} := by
    intro ω hw
    by_cases h : δ≤|X ω|
    · exact Or.inl ⟨hw,h⟩
    · right; change |1-gridMean _ _ ω|≤δ;rw [←score_eq]; exact le_of_lt (lt_of_not_ge h)
  exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans
    (add_le_add (fixed_margin n hn z meas hm hδ) (gridMean_near_tie _ _ hδ.le hu)))

open Real MeasureTheory Set Finset CircleEscapeBridge CircleSharpInitialization CircleResidualSpectrum
 CircleSpectralPathLength CircleInitializationConcentration CircleGaussianBernstein

private theorem centered_tail {m : ℕ} (hm : 0<m) (X : Atom → ℝ) (hX : Measurable X)
    {D R : ℝ} (hd : 0<D) (hR : 0≤R) (hu : R≤128*√(m:ℝ))
    (dom : ∀ z, |X z|≤D*atomEnergy z) :
    (seedLaw m).real {ω | D*R≤|centeredSum X ω|}≤2*exp (-(R^2)/4096) := by
  let f (z : Atom) := D⁻¹*X z
  have hdom (z : Atom) : |f z|≤energy z := by
    rw [show |f z|=D⁻¹*|X z| by dsimp only [f];rw [abs_mul,abs_of_pos (inv_pos.mpr hd)]]
    have beq : atomEnergy z=energy z := by simp [atomEnergy,energy,Fin.sum_univ_three]
    rw [←beq]
    exact (mul_le_mul_of_nonneg_left (dom z) (inv_nonneg.mpr hd.le)).trans_eq (by field_simp)
  have hm0 : 0<√(m:ℝ) := by positivity
  have h := two_sided hm f (hX.const_mul _) hdom (u:=R/√m) (by positivity) ((div_le_iff₀ hm0).2 hu)
  have scale (ω : Seed m) : centeredSum X ω = D*(√m*(sampleAverage f ω-∫z, f z ∂atomLaw)) := by
    simp only [centeredSum,sampleAverage,f,←Finset.mul_sum,integral_const_mul]
    field_simp
  apply (measureReal_mono (show {ω : Seed m | D*R≤|centeredSum X ω|}⊆_ from ?_)).trans (h.trans_eq ?_)
  · intro ω hw
    change D*R≤|centeredSum X ω| at hw
    rw [scale,abs_mul,abs_of_pos hd,abs_mul,abs_of_pos hm0] at hw
    apply (div_le_iff₀ hm0).mpr
    linarith only [le_of_mul_le_mul_left hw hd]
  · congr 2
    rw [div_pow,sq_sqrt (Nat.cast_nonneg _)]
    field_simp

variable {N m : ℕ} [NeZero N]

private theorem component_tail (hm : 0<m) (r : ZMod N) (p : ℂ →L[ℝ] ℝ) (hp : ∀ z, |p z|≤‖z‖)
    {D R : ℝ} (hd : 0<D) (hR : 0≤R) (hu : R≤128*√(m:ℝ))
    (hunit : ∀ w, ‖unitMode r w‖≤D*‖w‖) :
    (seedLaw m).real {ω | D*R≤|p (outMode r ω)|} ≤ 2*exp (-(R^2)/4096) := by
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
  have eq : (fun ω : Seed m => p (outMode r ω)) = centeredSum X := by
    funext ω
    have hz : (∫ z, X z ∂atomLaw)=0 := mean_zero F
    simp only [outMode, map_smul,map_sum,centeredSum,hz,sub_zero,sampleAverage,F,X,smul_eq_mul]
  change (seedLaw m).real {ω | D*R≤|(fun z : Seed m => p (outMode r z)) ω|} ≤ _
  rw [eq]
  exact centered_tail hm X hmX hd hR hu dom

private theorem out_tail (hm : 0<m) (r : ZMod N) {D R : ℝ} (hd : 0<D) (hR : 0≤R) (hu : R≤128*√(m:ℝ))
    (hunit : ∀ w, ‖unitMode r w‖≤D*‖w‖) :
    (seedLaw m).real {ω | 2*(D*R)<‖outMode r ω‖} ≤ 4*exp (-(R^2)/4096) := by
  have hr := component_tail hm r Complex.reCLM Complex.abs_re_le_norm hd hR hu hunit
  have hi := component_tail hm r Complex.imCLM Complex.abs_im_le_norm hd hR hu hunit
  apply (measureReal_mono (show {ω : Seed m | 2*(D*R)<‖outMode r ω‖}⊆
    {ω | D*R≤|Complex.reCLM (outMode r ω)|}∪{ω | D*R≤|Complex.imCLM (outMode r ω)|} from ?_)).trans
    ((measureReal_union_le _ _).trans ((add_le_add hr hi).trans_eq (by ring)))
  intro ω hw
  change 2*(D*R)<‖outMode r ω‖ at hw
  change D*R≤|(outMode r ω).re| ∨ D*R≤|(outMode r ω).im|
  by_contra! hh
  linarith [Complex.norm_le_abs_re_add_abs_im (outMode r ω),hh.1,hh.2]

def tailScale : ℝ := 4*(1+aliasCap)

private theorem tailScale_pos : 0<tailScale := by unfold tailScale; linarith [aliasCap_pos]

private theorem shell_envelope (ho : Odd N) (r : ZMod N) :
    (∀ w, ‖unitMode r w‖≤(tailScale/((2:ℝ)^shell ho r)^2)*‖w‖) ∧
      ‖labelMode r‖≤2*(tailScale/((2:ℝ)^shell ho r)^2) := by
  let k := representative ho r
  let D := (2:ℝ)^(shell ho r)
  have hD : 0<D := by dsimp [D]; positivity
  have hspec := rep_spec ho r
  have hd : D≤(k.natAbs:ℝ)+1 := by dsimp [D]; exact_mod_cast (shell_bounds ho r).1
  by_cases hs : r=0 ∨ r=1 ∨ r= -1
  · have hsmall : k.natAbs≤1 := hspec.2.2.1 hs
    have hh : (k.natAbs:ℝ) ≤ 1 := by exact_mod_cast hsmall
    have hp : D^2≤4 := by nlinarith [sq_le_sq₀ hD.le (by norm_num : (0:ℝ)≤2) |>.2 (show D≤2 by linarith)]
    have b : 1 ≤ tailScale/D^2 := (le_div_iff₀ (sq_pos_of_pos hD)).mpr (by unfold tailScale;linarith [aliasCap_pos])
    exact ⟨fun w => (unitMode_le r w).trans (le_mul_of_one_le_left (norm_nonneg _) b),
      (labelMode_le r).trans (by linarith)⟩
  have hn : r≠0 ∧ r≠1 ∧ r≠ -1 := by tauto
  have hkn : 2≤k.natAbs := by
    by_contra! h
    have hh : k.natAbs=0 ∨ k.natAbs=1 := by omega
    rcases hh with hz | h1
    · have hz' := Int.natAbs_eq_zero.mp hz
      exact hn.1 ((show (k:ZMod N)=r from hspec.1).symm.trans (by rw [hz']; simp))
    · rcases Int.natAbs_eq_iff.mp h1 with hp | hp
      · exact hn.2.1 ((show (k:ZMod N)=r from hspec.1).symm.trans (by rw [hp]; simp))
      · exact hn.2.2 ((show (k:ZMod N)=r from hspec.1).symm.trans (by rw [hp]; simp))
  have cap : aliasCap/(1+|(k:ℝ)|)^2≤tailScale/D^2 := by
    rw [Nat.cast_natAbs,Int.cast_abs] at hd
    calc
      _ ≤ aliasCap/D^2 := div_le_div_of_nonneg_left aliasCap_pos.le (by positivity)
        (pow_le_pow_left₀ hD.le (by linarith) _)
      _ ≤ _ := div_le_div_of_nonneg_right (by unfold tailScale;linarith [aliasCap_pos]) (sq_nonneg _)
  refine ⟨fun w => (unitMode_high ho hn.2.1 hn.2.2 hspec.1 (hspec.2.2.2 hn.1 hn.2.1 hn.2.2) hkn hspec.2.1 w).trans
    (mul_le_mul_of_nonneg_right cap (norm_nonneg _)),?_⟩
  rw [labelMode_zero hn.1 hn.2.1 hn.2.2,norm_zero]
  exact mul_nonneg (by norm_num) (div_nonneg tailScale_pos.le (sq_nonneg _))

private theorem shell_tail (ho : Odd N) (hm : 0<m) (r : ZMod N) {R : ℝ} (hR : 0≤R) (hu : R≤128*√(m:ℝ)) :
    (seedLaw m).real {ω | (2*tailScale*(1+R))/((2:ℝ)^shell ho r)^2<‖initialCoeff N m r ω‖} ≤ 4*exp (-(R^2)/4096) := by
  let D := tailScale/((2:ℝ)^shell ho r)^2
  have hh := shell_envelope ho r
  have h := out_tail hm r (show 0<D from div_pos tailScale_pos (by positivity)) hR hu hh.1
  apply (measureReal_mono _).trans h
  intro ω hw
  change (2*tailScale*(1+R))/((2:ℝ)^shell ho r)^2<‖initialCoeff N m r ω‖ at hw
  rw [raw_decompose hm] at hw
  change 2*(D*R)<‖outMode r ω‖
  have heq : (2*tailScale*(1+R))/((2:ℝ)^shell ho r)^2=2*D+2*(D*R) := by dsimp [D]; ring
  rw [heq] at hw
  linarith [norm_sub_le (outMode r ω) (labelMode r),hh.2]

def tailBudgetConstant : ℝ := 8*(tailScale/shellConstant)*√5*√2

private theorem budget_of_modes (ho : Odd N) (z : Seed m) {R : ℝ} (hr : 0≤R)
    (modes : ∀ r, ‖initialCoeff N m r z‖ ≤ (2*tailScale*(1+R))/((2:ℝ)^shell ho r)^2) :
    seedBudget ho m z ≤ tailBudgetConstant*(1+R)*√(N:ℝ) := by
  let μ := Measure.dirac ()
  have h := dyadic_lp4 (μ:=μ) (N+1).log2 (shell ho) (fun r (_ : Unit) => initialCoeff N m r z)
    (fun _ => memLp_const _) (2*tailScale*(1+R)) shellConstant
    (mul_nonneg (mul_nonneg (by norm_num) tailScale_pos.le) (by linarith)) shellConstant_pos (fun r => by
      simpa [μ,lpNorm_const' (show (4:ENNReal)≠0 by norm_num) (show (4:ENNReal)≠⊤ by norm_num)] using modes r) (shell_count ho)
  change lpNorm (fun _:Unit => seedBudget ho m z) 4 μ≤_ at h
  rw [lpNorm_const' (show (4:ENNReal)≠0 by norm_num) (show (4:ENNReal)≠⊤ by norm_num),Real.norm_eq_abs,abs_of_nonneg (seedBudget_nonneg _ _ _)] at h
  simp [μ] at h
  have hn := NeZero.pos N
  have hk : (2:ℝ)^((N+1).log2) ≤ 2*(N:ℝ) := by
    exact_mod_cast (Nat.log2_self_le (Nat.succ_ne_zero N)).trans (show N+1≤2*N by omega)
  have hroot := sqrt_le_sqrt hk
  rw [sqrt_mul (by norm_num : (0:ℝ)≤2)] at hroot
  apply h.trans
  have hpos : 0≤4*(2*tailScale*(1+R)/shellConstant)*√5 := by
    exact mul_nonneg (mul_nonneg (by norm_num) (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) tailScale_pos.le)
      (by linarith)) shellConstant_pos.le)) (sqrt_nonneg _)
  convert mul_le_mul_of_nonneg_left hroot hpos using 1; unfold tailBudgetConstant; ring

/-- High-confidence fourth-norm budget obtained by controlling all actual modes with
their own alias scale; the logarithmic cost is only from the probability threshold. -/
theorem seedBudget_tail (ho : Odd N) (hm : 0<m) {R : ℝ} (hr : 0≤R) (hu : R≤128*√(m:ℝ)) :
    (seedLaw m).real {ω | tailBudgetConstant*(1+R)*√(N:ℝ)<seedBudget ho m ω}≤
      (N:ℝ)*(4*exp (-(R^2)/4096)) := by
  let B (r : ZMod N) := {ω : Seed m | 2*tailScale*(1+R)/((2:ℝ)^shell ho r)^2<‖initialCoeff N m r ω‖}
  have hs : {ω : Seed m | tailBudgetConstant*(1+R)*√(N:ℝ)<seedBudget ho m ω}⊆⋃ r, B r := by
    intro ω hw
    by_contra! hx
    have good (r : ZMod N) : ‖initialCoeff N m r ω‖≤(2*tailScale*(1+R))/((2:ℝ)^shell ho r)^2 := by
      have hh : ω∉B r := fun hh => hx (Set.mem_iUnion.mpr ⟨r,hh⟩)
      exact le_of_not_gt hh
    exact (not_lt_of_ge (budget_of_modes ho ω hr good)) hw
  refine (measureReal_mono hs).trans ((measureReal_iUnion_fintype_le B).trans ?_)
  calc
    _ ≤ ∑ _r : ZMod N, 4*exp (-(R^2)/4096) := sum_le_sum (fun r _ => shell_tail ho hm r hr hu)
    _ = _ := by simp [ZMod.card]

def tailThreshold (N k : ℕ) := 64*√(((k:ℝ)+1)*log (N:ℝ))

theorem seedBudget_power (ho : Odd N) (k : ℕ) (hk : k+1≤N) :
    (seedLaw (N^32)).real {ω | tailBudgetConstant*(1+tailThreshold N k)*√(N:ℝ)<seedBudget ho (N^32) ω} ≤
      4/(N:ℝ)^k := by
  have hp := NeZero.pos N
  have hn : 1≤(N:ℝ) := by exact_mod_cast hp
  have na : 0<(N:ℝ) := by positivity
  have a0 : 0≤((k:ℝ)+1)*log N := mul_nonneg (by positivity) (log_nonneg hn)
  have kN : (k:ℝ)+1≤N := by exact_mod_cast hk
  have hh : ((k:ℝ)+1)*log N≤(N:ℝ)^2 := by
    rw [sq];exact mul_le_mul kN ((log_le_sub_one_of_pos na).trans (by linarith)) (log_nonneg hn) (by positivity)
  have hm : 0<N^32 := pow_pos hp _
  have hs : √(((k:ℝ)+1)*log N)≤√(((N^32:ℕ):ℝ)) := by
    apply sqrt_le_sqrt;push_cast;exact hh.trans (pow_le_pow_right₀ hn (by decide : 2≤32))
  have h := seedBudget_tail ho hm (R:=tailThreshold N k) (by unfold tailThreshold;positivity)
    (by unfold tailThreshold; linarith [sqrt_nonneg (((N^32:ℕ):ℝ))])
  apply h.trans_eq
  rw [tailThreshold,mul_pow,sq_sqrt a0]
  rw [show -((64:ℝ)^2*(((k:ℝ)+1)*log N))/4096 = -(((k:ℝ)+1)*log N) by ring,exp_neg]
  rw [add_mul,one_mul,exp_add,Real.exp_nat_mul,exp_log na];field_simp

open CircleComparison CircleSharpMoments

def paths (n : ℕ) (F : ∀ q, Benchmark n (benchmarkRate q)) : Family (n+1) := fun q => (F q).path

theorem actual_scaled_rms (n : ℕ) (hN : 36864≤n+1) (ho : Odd (n+1))
    (F : ∀ q, Benchmark n (benchmarkRate q)) :
    √(∫ ω, (difference n (paths n F) ω - coefficient n*score (n+1) ((n+1)^32) ω)^2 ∂seedLaw ((n+1)^32))
      ≤ 2*trackingConstant/((n:ℝ)+1)^13 := by
  let z := paths n F
  have hs (q : Bool) : MemLp (discrepancy n z q) 2 (seedLaw ((n+1)^32)) :=
    discrepancy_mem n z q (F q).start ((F q).flow _ (Nat.cast_nonneg _)) ((F q).endpoint _ (Nat.cast_nonneg _))
  have each (q : Bool) : rmsError n z q≤trackingConstant/((n:ℝ)+1)^15 :=
    sharp_tracking n hN ho (rate_bounds q).1 (rate_bounds q).2 (F q)
  have hn0 : 0<(n:ℝ)+1 := by positivity
  apply (scaled_reference_error n (by omega) z hs).trans
  calc
    _ ≤ ((n:ℝ)+1)^2*(trackingConstant/((n:ℝ)+1)^15+trackingConstant/((n:ℝ)+1)^15) :=
      mul_le_mul_of_nonneg_left (add_le_add (each false) (each true)) (sq_nonneg _)
    _ = _ := by field_simp; ring

open CircleSharpTracking
theorem fixed_margin_high_confidence (n k : ℕ) (hN : 36864≤n+1) (hk : k+17≤n+1) (ho : Odd (n+1))
    (F : ∀ q, Benchmark n (benchmarkRate q)) (δ : ℝ)
    (sep : 2*pathConstant/((n:ℝ)+1)<coefficient n*δ) :
    (seedLaw ((n+1)^32)).real (miss n (paths n F) ∩ {ω | δ≤|score (n+1) ((n+1)^32) ω|}) ≤
      44/((n:ℝ)+1)^k := by
  obtain ⟨G,_,prob,inh⟩ := joint_fit_original_horizon n k hN hk ho
  have hn : 0<(n:ℝ)+1 := by positivity
  apply (event_margin n (paths n F) G (pathConstant/((n:ℝ)+1)^3) δ ?_ ?_).trans prob
  · apply lt_of_eq_of_lt _ sep; field_simp
  · intro ω hg q
    have hq : benchmarkRate q=1/2 ∨ benchmarkRate q=1 ∨ benchmarkRate q=2 := by cases q <;> simp [benchmarkRate]
    exact (inh ω hg _ hq ((F q).path ω) ((F q).start ω) ((F q).flow _ (Nat.cast_nonneg _) ω)).2

private def Vcap (N k : ℕ) := tailBudgetConstant*(1+tailThreshold N k)*√(N:ℝ)
private def Bcap (N k : ℕ) := 768*√(((k:ℝ)+2)*log (N:ℝ))/(N:ℝ)^16
def endpointCap (N k : ℕ) := 6*Bcap N k*Vcap N k+44928*(1+Vcap N k)*Vcap N k/(N:ℝ)^16+1/(N:ℝ)^16

/-- With any prescribed inverse-power failure, both nonlinear endpoints are
controlled by the same explicit logarithmic cap for the actual Gaussian design. -/
theorem paired_likely_cap (n k : ℕ) (hN : 36864≤n+1) (hk : k+17≤n+1) (ho : Odd (n+1))
    (F : ∀ q, Benchmark n (benchmarkRate q)) :
    ∃ G : Set (Seed ((n+1)^32)), MeasurableSet G ∧
      (seedLaw ((n+1)^32)).real Gᶜ≤52/((n:ℝ)+1)^k ∧
      ∀ ω∈G, ∀ q, |discrepancy n (paths n F) q ω|≤endpointCap (n+1) k := by
  let N := n+1
  let m := N^32
  let μ := seedLaw m
  let U := seedBudget ho m
  have s (q : Bool) := gaussian_spectral_endpoint n k hN hk ho (benchmarkRate q) (rate_bounds q).1 (rate_bounds q).2
  choose G mg pG inner using s
  let B (q : Bool) := {ω : Seed m | Bcap N k < initialError N m (benchmarkRate q) ω}
  let V := {ω : Seed m | Vcap N k<U ω}
  let bad := ((G false)ᶜ∪(G true)ᶜ)∪((B false∪B true)∪V)
  have pb (q : Bool) : μ.real (B q)≤10/((n:ℝ)+1)^k := by
    simpa [B,Bcap,N,m,μ,Nat.cast_add,Nat.cast_one] using CircleDiscreteMoments.operator_error_tail (n+1) k
      (by omega) (by omega) (benchmarkRate q) (by cases q <;> norm_num [benchmarkRate])
  have pv : μ.real V ≤ 4/((n:ℝ)+1)^k := by simpa only [μ,N,m,Nat.cast_add,Nat.cast_one,V,Vcap,U] using seedBudget_power ho k (by omega)
  refine ⟨(toMeasurable μ bad)ᶜ,(measurableSet_toMeasurable μ bad).compl,?_,?_⟩
  · rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    change μ.real (((G false)ᶜ∪(G true)ᶜ)∪((B false∪B true)∪V)) ≤ _
    apply (measureReal_union_le _ _).trans
    apply (add_le_add (measureReal_union_le _ _) ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))).trans
    apply (add_le_add (add_le_add (pG false) (pG true)) (add_le_add (add_le_add (pb false) (pb true)) pv)).trans_eq
    ring
  · intro ω h q
    have hh : ω∉bad := fun hg => h (subset_toMeasurable μ bad hg)
    have good : (ω∈G false ∧ ω∈G true) ∧ (ω∉B false ∧ ω∉B true) ∧ ω∉V := by
      simpa [bad,not_or,and_assoc] using hh
    have hG : ω∈G q := by cases q <;> tauto
    have hB : initialError N m (benchmarkRate q) ω≤Bcap N k := by cases q; exact le_of_not_gt good.2.1.1; exact le_of_not_gt good.2.1.2
    have hV : U ω≤Vcap N k := le_of_not_gt good.2.2
    have hU := seedBudget_nonneg ho m ω
    have hB0 := initialError_nonneg (N:=N) (benchmarkRate q) ω
    apply (inner q ω hG ((F q).path ω) ((F q).start ω) ((F q).flow _ (Nat.cast_nonneg _) ω)).trans
    change 6*initialError N m (benchmarkRate q) ω*U ω+44928*(1+U ω)*U ω/((n:ℝ)+1)^16+1/((n:ℝ)+1)^16 ≤ _
    unfold endpointCap
    push_cast
    have vN : 0≤Vcap (n+1) k := hU.trans hV
    have bN : 0≤Bcap (n+1) k := hB0.trans hB
    gcongr

open CircleSphereBand CircleReadoutMixing CircleInitializationConcentration
open scoped ENNReal

private theorem fiber_bound {m : ℕ} {A : Set (Seed m)} (hA : MeasurableSet A) (b : Triple m→Atom)
    (r : Triple m→ℝ) (hn : ∀ p, 0≤r p) (hi : Integrable r (tripleLaw m))
    (bound : ∀ p x, mixedSeed (direction x) p∈A → |1-project (b p) x|≤r p) :
    (seedLaw m).real A ≤ 4*∫p, r p ∂tripleLaw m := by
  rw [mix_fubini_real m atomLaw direction measurable_direction direction_unit A hA, ←integral_const_mul]
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => measureReal_nonneg)) (hi.const_mul _)
  exact ae_of_all _ fun p => (measureReal_mono (fun (x : Atom) hx => bound p x hx)).trans
    (projection_band (b p) (hn p))

private def env (B V : ℝ) (n : ℝ) := 6*(B*V)+(44928*(1/n^16))*((1+V)*V)+1/n^16

private def costConstant (cB cV : ℝ) := 6*cB*cV+44928*(cV+cV^2)+1

private theorem env_cost {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B V : Ω → ℝ} (hb : MemLp B 4 μ) (hv : MemLp V 4 μ) {x cB cV : ℝ} (hx : 1≤x)
    (hB : 0≤cB) (hV : 0≤cV) (bb : lpNorm B 4 μ ≤ cB/x^16) (vv : lpNorm V 4 μ ≤ cV*√x) :
    Integrable (fun ω => env (B ω) (V ω) x) μ ∧
    (∫ω,env (B ω) (V ω) x ∂μ) ≤ costConstant cB cV/x^15 := by
  have xp : 0<x := by linarith
  have h := CircleSharpMoments.envelope hb hv (1/x^16) (by positivity)
  let E := fun ω => env (B ω) (V ω) x
  have h2 : MemLp E 2 μ := h.1
  have h1 : MemLp E 1 μ := h2.mono_exponent (by norm_num)
  have cap := CircleSharpMoments.collect_bounds (d:=0) (cd:=0) (p:=0) hx lpNorm_nonneg hB hV le_rfl bb vv
    (by simp) (by positivity)
  refine ⟨h1.integrable (by norm_num),?_⟩
  calc
    _ ≤ ∫ω,‖E ω‖ ∂μ := integral_mono (h1.integrable (by norm_num)) (h1.integrable (by norm_num)).norm (fun _ => le_abs_self _)
    _ = lpNorm E 1 μ := (lpNorm_one_eq_integral_norm h1.aestronglyMeasurable).symm
    _ ≤ lpNorm E 2 μ := by
      rw [←toReal_eLpNorm,←toReal_eLpNorm]
      exact ENNReal.toReal_mono h2.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
    _ ≤ _ := h.2.trans (by simpa only [zero_mul,mul_zero,add_zero,costConstant] using cap)

private theorem miss_measurable (n : ℕ) (F : ∀q, Benchmark n (benchmarkRate q)) : MeasurableSet (miss n (paths n F)) := by
  apply measurableSet_le _ measurable_const
  apply Measurable.mul _ (score_measurable _ _)
  exact measurable_const.mul ((CircleFlowMoments.mean_measurable.comp ((F false).endpoint _ (Nat.cast_nonneg _))).sub
    (CircleFlowMoments.mean_measurable.comp ((F true).endpoint _ (Nat.cast_nonneg _))))

private theorem good_pair (n : ℕ) (hN : 36864≤n+1) (ho : Odd (n+1))
    (F : ∀q, Benchmark n (benchmarkRate q)) :
    ∃ G : Set (Seed ((n+1)^32)), MeasurableSet G ∧ (seedLaw ((n+1)^32)).real Gᶜ ≤ 28/((n:ℝ)+1)^13 ∧
    ∀ ω∈G, ∀q, |discrepancy n (paths n F) q ω| ≤ env (initialError (n+1) ((n+1)^32) (benchmarkRate q) ω)
      (seedBudget ho ((n+1)^32) ω) ((n:ℝ)+1) := by
  have s (q : Bool) := gaussian_spectral_endpoint n 13 hN (by omega) ho (benchmarkRate q) (rate_bounds q).1 (rate_bounds q).2
  choose G hG prob along using s
  refine ⟨G false∩G true,(hG _).inter (hG _),?_,?_⟩
  · rw [compl_inter]
    exact ((measureReal_union_le _ _).trans (add_le_add (prob false) (prob true))).trans_eq (by ring)
  · intro ω hg q
    have hq : ω∈G q := by cases q;exact hg.1;exact hg.2
    have h := along q ω hq ((F q).path ω) ((F q).start ω) ((F q).flow _ (Nat.cast_nonneg _) ω)
    apply h.trans_eq
    unfold env
    ring

private theorem cancel_width (N e c : ℝ) (hc : c≠0) :
    N^2*(e+e)=c*((2*N^2/c)*e) := by field_simp; ring

private theorem simplify_cost (N K c : ℝ) (hn : N≠0) (hc : c≠0) :
    28/N^13+4*((2*N^2/c)*(K/N^15))=(28+8*K/c)/N^13 := by field_simp; ring

set_option maxHeartbeats 500000 in
/-- If all mixed readouts have a direction-independent first-moment bound for
their tracking errors, averaging over the sphere controls the full sign error. -/
private theorem angular_order (n : ℕ) (hN : 36864≤n+1) (ho : Odd (n+1)) (F : ∀q, Benchmark n (benchmarkRate q))
    (a : Triple ((n+1)^32)→Atom) (B V : Triple ((n+1)^32)→ℝ)
    (inn : ∀ p x, gridMean (n+1) ((n+1)^32) (mixedSeed (direction x) p)=project (a p) x)
    (hB : ∀ p x q, initialError (n+1) ((n+1)^32) (benchmarkRate q) (mixedSeed (direction x) p)≤B p)
    (hV : ∀ p x, seedBudget ho ((n+1)^32) (mixedSeed (direction x) p)≤V p)
    (hmB : MemLp B 4 (tripleLaw ((n+1)^32))) (hmV : MemLp V 4 (tripleLaw ((n+1)^32)))
    (cB cV : ℝ) (b0 : 0≤cB) (v0 : 0≤cV)
    (bb : lpNorm B 4 (tripleLaw ((n+1)^32)) ≤ cB/((n:ℝ)+1)^16)
    (vv : lpNorm V 4 (tripleLaw ((n+1)^32)) ≤ cV*√((n:ℝ)+1)) :
    (seedLaw ((n+1)^32)).real (miss n (paths n F)) ≤
      (28 + 8*costConstant cB cV/coefficient n)/((n:ℝ)+1)^13 := by
  let N := (n:ℝ)+1
  let m := (n+1)^32
  let ν := tripleLaw m
  let μ := seedLaw m
  let E (p : Triple m) := env (B p) (V p) N
  let M := miss n (paths n F)
  have nt : 1≤N := by dsimp [N];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have np : 0<N := by linarith
  have bnon (p : Triple m) : 0≤B p := (initialError_nonneg (benchmarkRate false) _).trans (hB p 0 false)
  have vnon (p : Triple m) : 0≤V p := (seedBudget_nonneg _ _ _).trans (hV p 0)
  have enon (p : Triple m) : 0≤E p := by dsimp [E,env]; have := bnon p; have := vnon p; positivity
  let s := 2*N^2/coefficient n
  have sp : 0<s := by dsimp [s];exact div_pos (by positivity) (coefficient_pos n)
  obtain ⟨G,hG,pG,along⟩ := good_pair n hN ho F
  have mM : MeasurableSet M := miss_measurable n F
  have hi := env_cost hmB hmV nt b0 v0 bb vv
  have hCG : μ.real (M∩G) ≤ 4*(∫p, s*E p ∂ν) := by
    apply fiber_bound (mM.inter hG) a (fun p => s*E p) (fun p => mul_nonneg sp.le (enon p)) (hi.1.const_mul s)
    intro p x hx
    let ω := mixedSeed (direction x) p
    let X := score (n+1) m ω
    have wrong := wrong_forces_error (coefficient_pos n) hx.1
    rw [identity,abs_mul,abs_of_nonneg (sq_nonneg ((n:ℝ)+1))] at wrong
    have ee (q : Bool) : |discrepancy n (paths n F) q ω|≤E p := by
      apply (along ω hx.2 q).trans
      have xV := hV p x
      have xB := hB p x q
      have aNN := initialError_nonneg (N:=n+1) (benchmarkRate q) ω
      have bNN := seedBudget_nonneg ho m ω
      dsimp only [E,env]
      have vN := vnon p
      have bN := bnon p
      gcongr
    have hh := (abs_sub _ _).trans (add_le_add (ee false) (ee true))
    have main : coefficient n*|X|≤N^2*(E p+E p) :=
      wrong.trans (mul_le_mul_of_nonneg_left hh (sq_nonneg _))
    change |1-project (a p) x|≤s*E p
    rw [←inn,←score_eq]
    apply le_of_mul_le_mul_left _ (coefficient_pos n)
    exact main.trans_eq (cancel_width N (E p) (coefficient n) (coefficient_pos n).ne')
  rw [integral_const_mul] at hCG
  have sub : M ⊆ Gᶜ ∪ (M∩G) := fun ω hw => by by_cases hh : ω∈G;exact Or.inr ⟨hw,hh⟩;exact Or.inl hh
  apply (measureReal_mono sub).trans ((measureReal_union_le _ _).trans _)
  apply (add_le_add pG (hCG.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi.2 sp.le) (by norm_num)))).trans_eq
  change 28/N^13+4*(s*(costConstant cB cV/N^15))=_
  exact simplify_cost N (costConstant cB cV) (coefficient n) np.ne' (coefficient_pos n).ne'

open CircleMixingEnvelopes

/-- Explicit finite-grid constant from the two readout-error envelopes and
the common residual envelope. -/
def angularConstant := 6*(216*markConstant)*(6*budgetConstant)+44928*(6*budgetConstant+(6*budgetConstant)^2)+1

private theorem angularConstant_nonneg : 0≤angularConstant := by
  have hm : 0≤markConstant := by unfold markConstant;positivity
  have hv := budgetConstant_nonneg
  unfold angularConstant
  positivity

/-- The trained sign, including trained ties, is predicted with unconditional
failure at most a constant times N⁻¹³ on every sufficiently large odd grid.
The displayed finite-N coefficient is strictly positive. The two learners may
be any measurable choices of their respective full nonlinear flows. -/
theorem actual_wrong_probability (n : ℕ) (hN : 36864≤n+1) (ho : Odd (n+1))
    (F : ∀q, Benchmark n (benchmarkRate q)) :
    (seedLaw ((n+1)^32)).real (miss n (paths n F)) ≤
      (28+8*angularConstant/coefficient n)/((n:ℝ)+1)^13 := by
  let N := n+1
  let m := N^32
  let a (p : Triple m) (j : Fin 3) := gridMean N m (mixedSeed (Pi.single j 1) p)
  let b (q : Bool) := mixError N m (benchmarkRate q)
  let B := b false + b true
  let V := mixBudget ho m
  have hm : 0<m := pow_pos (Nat.succ_pos _) _
  have bi (q : Bool) := mixError_fourth (N:=N) hm (benchmarkRate q) (by cases q <;> norm_num [benchmarkRate])
  have vi := mixBudget_fourth ho hm
  have w : √(m:ℝ)=((n:ℝ)+1)^16 := by
    dsimp only [m,N]
    push_cast
    rw [show ((n:ℝ)+1)^32=(((n:ℝ)+1)^16)^2 by ring,sqrt_sq (by positivity)]
  have hB (p : Triple m) (q : Bool) : b q p ≤ B p := by
    have x := mixError_nonneg (N:=N) (benchmarkRate false) p
    have y := mixError_nonneg (N:=N) (benchmarkRate true) p
    cases q
    · exact le_add_of_nonneg_right y
    · exact le_add_of_nonneg_left x
  apply angular_order n hN ho F a B V (fun p x => by simpa only [project,a,N,m] using gridMean_mix N m p (direction x))
    (fun p x q => (mixError_dominates hm (benchmarkRate q) p (direction x) (direction_unit x)).trans (hB p q))
    (fun p x => mixBudget_dominates ho p (direction x) (direction_unit x)) ((bi false).1.add (bi true).1) vi.1
    (216*markConstant) (6*budgetConstant) (mul_nonneg (by norm_num) (by unfold markConstant;positivity))
    (mul_nonneg (by norm_num) budgetConstant_nonneg)
  · apply (lpNorm_add_le (bi false).1 (by norm_num)).trans
    apply (add_le_add (bi false).2 (bi true).2).trans_eq
    rw [w]
    ring
  · simpa only [N,Nat.cast_add,Nat.cast_one] using vi.2

/-- One absolute coefficient works simultaneously for every pair of valid measurable
learners on each sufficiently large odd grid. -/
theorem actual_wrong_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ _ho : Odd (n+1), ∀ F : ∀q, Benchmark n (benchmarkRate q),
      (seedLaw ((n+1)^32)).real (miss n (paths n F)) ≤
        (28+8*angularConstant/(π^2/80))/((n:ℝ)+1)^13 := by
  filter_upwards [eventually_ge_atTop 36864,coefficient_eventually] with n hn hc ho F
  apply (actual_wrong_probability n (by omega) ho F).trans
  exact div_le_div_of_nonneg_right (add_le_add_right (div_le_div_of_nonneg_left
    (mul_nonneg (by norm_num) angularConstant_nonneg) (by positivity) hc) _) (by positivity)

theorem fixed_margin_eventually (k : ℕ) {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ n : ℕ in atTop, ∀ _ho : Odd (n+1), ∀ F : ∀q, Benchmark n (benchmarkRate q),
      (seedLaw ((n+1)^32)).real (miss n (paths n F) ∩ {ω | δ≤|score (n+1) ((n+1)^32) ω|}) ≤
        44/((n:ℝ)+1)^k := by
  have grow : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have lim : Tendsto (fun n : ℕ => 2*pathConstant/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using (tendsto_inv_atTop_zero.comp grow).const_mul (2*pathConstant)
  have small := lim.eventually (eventually_lt_nhds (show (0:ℝ)<(π^2/80)*δ by positivity))
  filter_upwards [eventually_ge_atTop 36864,eventually_ge_atTop (k+17),coefficient_eventually,small] with n hn hk hc hsep ho F
  exact fixed_margin_high_confidence n k (by omega) (by omega) ho F δ
    (hsep.trans_le (mul_le_mul_of_nonneg_right hc hd.le))

private theorem elementary_log_cap (x t b d B V : ℝ) (hx : 1≤x) (ht : 0≤t) (hb : 0≤b) (hd : 0≤d)
    (nn : 0≤V) (bcap : B≤d*(1+t)/x^16) (vcap : V≤(b*(1+t))*√x) :
    6*B*V+44928*(1+V)*V/x^16+1/x^16 ≤
      (2*costConstant d b)*(1+t^2)/x^15 := by
  let T := 1+t
  have ht1 : 1≤T := by dsimp [T]; linarith
  have ht2 : T≤T^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (zero_le_one.trans ht1)]
  have ts : 1≤T^2 := ht1.trans ht2
  have hh := CircleSharpMoments.collect_bounds (d:=0) (p:=0) (cd:=0) hx nn
    (mul_nonneg hd (zero_le_one.trans ht1)) (mul_nonneg hb (zero_le_one.trans ht1)) le_rfl bcap vcap (by simp) (by positivity)
  simp only [zero_mul,mul_zero,add_zero] at hh
  calc
    _ = 6*B*V+44928*(1/x^16)*(1+V)*V+1/x^16 := by ring
    _ ≤ _ := hh
    _ ≤ costConstant d b * T^2/x^15 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      dsimp only [costConstant]
      nlinarith only [mul_le_mul_of_nonneg_left ht2 hb,ts]
    _ ≤ _ := by
      have hT : T^2≤2*(1+t^2) := by dsimp [T];nlinarith [sq_nonneg (t-1)]
      have hK : 0≤costConstant d b := by unfold costConstant;positivity
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith only [mul_le_mul_of_nonneg_left hT hK]

def confidenceConstant (k : ℕ) := 2*costConstant (768*√((k:ℝ)+2))
  (tailBudgetConstant*(1+64*√((k:ℝ)+1)))

theorem endpointCap_le (N k : ℕ) (hn : 1≤N) :
    endpointCap N k ≤ confidenceConstant k*(1+log (N:ℝ))/(N:ℝ)^15 := by
  let t := √(log (N:ℝ))
  let b := tailBudgetConstant*(1+64*√((k:ℝ)+1))
  let d := 768*√((k:ℝ)+2)
  have hN : 1≤(N:ℝ) := by exact_mod_cast hn
  have hz := log_nonneg hN
  have hp : 0≤tailBudgetConstant := by unfold tailBudgetConstant; exact mul_nonneg (mul_nonneg (mul_nonneg
    (by norm_num) (div_nonneg tailScale_pos.le shellConstant_pos.le)) (sqrt_nonneg _)) (sqrt_nonneg _)
  have hb : 0≤b := by dsimp [b]; positivity
  have hd : 0≤d := by dsimp [d]; positivity
  have hv : 0≤Vcap N k := by dsimp [Vcap,tailThreshold];positivity
  have hB : Bcap N k≤d*(1+t)/(N:ℝ)^16 := by
    dsimp only [Bcap,d,t]
    rw [sqrt_mul (show 0≤(k:ℝ)+2 by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sqrt_nonneg ((k:ℝ)+2)]
  have hV : Vcap N k≤(b*(1+t))*√(N:ℝ) := by
    dsimp only [Vcap,b,tailThreshold,t]
    rw [sqrt_mul (show 0≤(k:ℝ)+1 by positivity)]
    apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hp
    nlinarith [sqrt_nonneg ((k:ℝ)+1),sqrt_nonneg (log (N:ℝ))]
  have h := elementary_log_cap (N:ℝ) t b d (Bcap N k) (Vcap N k) hN (sqrt_nonneg _) hb hd hv hB hV
  simpa only [endpointCap,confidenceConstant,d,b,t,sq_sqrt hz] using h
end CirclePairedOrdering
