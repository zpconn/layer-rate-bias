module

public import CircleGDLimits
public import CircleSharpGD
public import CircleSharpMoments
import all CircleSharpMoments
import all CircleDiscreteMoments
import all CircleTruncatedBudget
import all CircleSpectralPathLength
import all CircleGaussianTracking
import all CircleGDLimits
import all CircleCapMoments
import all CircleSeedIntegrability
import all CircleEscapeBridge
import all CircleShortGDTails
import Mathlib.Tactic

/-! Sharp stopped and infinite-reference moments for the original unit-step
and once-capped circle learners under the full product Gaussian seed law. -/
public section
noncomputable section
namespace CircleSharpGDMoments
open Real MeasureTheory Set CircleEscapeBridge CircleCapMoments CircleKernelGD CircleSharpInitialization
open CircleSharpMoments CircleSharpGD CircleTruncatedBudget CircleSpectralPathLength CircleSeedIntegrability

private theorem split_mse {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D L : Ω → ℝ} {E : Set Ω} {K : ℝ} (me : MeasurableSet E) (hL : MemLp L 2 μ)
    (hD : Integrable (fun z => D z^2) μ) (good : ∀z∈E, |D z| ≤ L z)
    (nn : 0≤K) (bad : (∫ z in Eᶜ, D z^2 ∂μ)≤K^2) :
    sqrt (∫ z, D z^2 ∂μ) ≤ lpNorm L 2 μ + K := by
  have h := setIntegral_mono_on hD.integrableOn hL.integrable_sq.integrableOn me
    (fun z hz => (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (good z hz) 2))
  have all : (∫ z in E, L z^2 ∂μ) ≤ ∫ z, L z^2 ∂μ := by
    apply setIntegral_le_integral hL.integrable_sq
    exact ae_of_all _ fun z => sq_nonneg _
  have sum : (∫ z, D z^2 ∂μ)≤ (∫ z, L z^2 ∂μ)+K^2 := by
    rw [←integral_add_compl me hD]
    exact add_le_add (h.trans all) bad
  rw [←CircleSharpMoments.rms_eq hL]
  apply sqrt_le_iff.mpr ⟨by positivity,?_⟩
  nlinarith only [sum,sq_sqrt (integral_nonneg (μ:=μ) (fun z => sq_nonneg (L z))),mul_nonneg (sqrt_nonneg (∫ z,L z^2 ∂μ)) nn]

def areaConstant := budgetConstant+truncConstant

def errorConstant := 36*markConstant*areaConstant+44928*(areaConstant+areaConstant^2)+66

/-- Square-root time growth saturates at N rather than the fitting time. -/
def shape (N T : ℕ) := min (N:ℝ) (sqrt (T+1:ℕ))

private theorem shape_one {N : ℕ} (hn : 0<N) (T : ℕ) : 1≤shape N T :=
  le_min (by exact_mod_cast hn) (one_le_sqrt.mpr (by exact_mod_cast Nat.succ_pos T))

private theorem norm_budget {N m : ℕ} [NeZero N] (odd : Odd N) (hm : 0<m) (T : ℕ) :
    lpNorm (truncatedBudget odd m T) 4 (seedLaw m) ≤ areaConstant*sqrt (shape N T) := by
  have cg : 0≤truncConstant := lpNorm_nonneg.trans (by
    have b := budget_lp4 odd hm 0
    simpa using b)
  have h := lpNorm_mono_real (seedBudget_mem hm odd) (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (budget_nonneg odd m T z)]
    exact full_cap odd m T z)
  have g := h.trans (seedBudget_lp4 hm odd)
  have t := budget_lp4 odd hm T
  rcases le_total (N:ℝ) (sqrt (T+1:ℕ)) with q|q
  · rw [shape,min_eq_left q]
    exact g.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right cg) (sqrt_nonneg _))
  · rw [shape,min_eq_right q]
    exact t.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left budgetConstant_nonneg) (sqrt_nonneg _))

private theorem collect {N T : ℕ} (hn : 0<N) {b v : ℝ} (vb : 0≤v)
    (hb : b≤6*markConstant/(N:ℝ)^16) (hv : v≤areaConstant*sqrt (shape N T)) (cg : 0≤areaConstant) :
    6*b*v+44928*(1/(N:ℝ)^16)*(1+v)*v+1/(N:ℝ)^16+65/(N:ℝ)^16 ≤ errorConstant*shape N T/(N:ℝ)^16 := by
  let q := shape N T
  have q1 : 1≤q := shape_one hn T
  have hq : 0≤q := zero_le_one.trans q1
  have sq : sqrt q≤q := (sqrt_le_iff.mpr ⟨hq,by nlinarith only [mul_nonneg hq (sub_nonneg.mpr q1)]⟩)
  have v₁ := hv.trans (mul_le_mul_of_nonneg_left sq cg)
  change v≤areaConstant*sqrt q at hv
  have v₂ : v^2 ≤ areaConstant^2*q := by simpa only [mul_pow,sq_sqrt hq] using pow_le_pow_left₀ vb hv 2
  have vv : (1+v)*v ≤ (areaConstant+areaConstant^2)*q := by nlinarith only [v₁,v₂]
  have mb : 0≤markConstant := by unfold markConstant;positivity
  have bv := mul_le_mul hb v₁ vb (show 0≤6*markConstant/(N:ℝ)^16 by positivity)
  have w := mul_le_mul_of_nonneg_left vv (show 0≤44928*(1/(N:ℝ)^16) by positivity)
  change _ ≤ errorConstant*q/(N:ℝ)^16
  calc
    _ ≤ 6*((6*markConstant/(N:ℝ)^16)*(areaConstant*q))+
        44928*(1/(N:ℝ)^16)*((areaConstant+areaConstant^2)*q)+66*q/(N:ℝ)^16 := by
      have coef := mul_le_mul_of_nonneg_right q1 (show 0≤66/(N:ℝ)^16 by positivity)
      ring_nf at bv w coef ⊢
      linarith only [bv,w,coef]
    _ = _ := by unfold errorConstant;ring

private theorem tail_with_rejection {N : ℕ} (hn : 0<N) {p : ℝ} (h : p≤15/(N:ℝ)^158) :
    1044*(N^32:ℕ)*sqrt p + 1/(N:ℝ)^32 ≤ (65/(N:ℝ)^16)^2 := by
  have n1 : (1:ℝ)≤N := by exact_mod_cast hn
  have np : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have s := sqrt_le_sqrt h
  rw [sqrt_div (by norm_num),show (N:ℝ)^158=((N:ℝ)^79)^2 by ring,sqrt_sq (by positivity)] at s
  have s4 : sqrt 15≤4 := sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  push_cast
  have u := mul_le_mul_of_nonneg_left (s.trans (div_le_div_of_nonneg_right s4 (by positivity)))
    (show 0≤1044*(N:ℝ)^32 by positivity)
  have c : 1044*(N:ℝ)^32*(4/(N:ℝ)^79) = 4176/(N:ℝ)^47 := by field_simp;norm_num
  have b := (u.trans_eq c).trans (div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_right₀ n1 (by decide : 32≤47)))
  apply (add_le_add b (le_refl _)).trans
  rw [←add_div,div_pow,←pow_mul]
  norm_num
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

private theorem tail_sq {N : ℕ} (hn : 0<N) {p : ℝ} (h : p≤15/(N:ℝ)^158) :
    1044*(N^32:ℕ)*sqrt p ≤ (65/(N:ℝ)^16)^2 :=
  (le_add_of_nonneg_right (by positivity)).trans (tail_with_rejection hn h)

private theorem stopped_bounds (n T : ℕ) : 0≤stoppedWeight n T ∧ stoppedWeight n T≤1 := by
  have w := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  have g := gamma_bounds (N:=n+1)
  have z : 0≤gamma (n+1) := (show (0:ℝ)≤3/π^2 by positivity).trans g.1
  have lo := pow_nonneg (sub_nonneg.mpr g.2) T
  have hi := pow_le_one₀ (sub_nonneg.mpr g.2) (sub_le_self _ z) (n:=T)
  exact ⟨mul_nonneg w.1 (sub_nonneg.mpr hi),(mul_le_of_le_one_left (sub_nonneg.mpr hi) w.2).trans (sub_le_self _ lo)⟩

private theorem rms_bound (n T : ℕ) (odd : Odd (n+1)) (Y : Seed ((n+1)^32)→ℝ)
    (Dint : Integrable (fun z => (Y z-reference (n+1) ((n+1)^32) (stoppedWeight n T) z)^2) (seedLaw ((n+1)^32)))
    (E : Set (Seed ((n+1)^32))) (me : MeasurableSet E)
    (cap : ∀z∈E, let B := initialError (n+1) ((n+1)^32) 1 z
                  let V := truncatedBudget odd ((n+1)^32) T z
                  |Y z-reference (n+1) ((n+1)^32) (stoppedWeight n T) z| ≤
                    6*B*V+44928*(1+V)*V/((n+1:ℕ):ℝ)^16)
    (tail : (∫ z in Eᶜ, (Y z-reference (n+1) ((n+1)^32) (stoppedWeight n T) z)^2 ∂seedLaw ((n+1)^32)) ≤
      (65/((n+1:ℕ):ℝ)^16)^2) :
    sqrt (∫ z, (Y z-reference (n+1) ((n+1)^32) (stoppedWeight n T) z)^2 ∂seedLaw ((n+1)^32)) ≤
      errorConstant*shape (n+1) T/((n+1:ℕ):ℝ)^16 := by
  let N := n+1
  let m := N^32
  let B := initialError N m 1
  let V := truncatedBudget odd m T
  let μ := seedLaw m
  let w := 1/(N:ℝ)^16
  have hn : 0<N := Nat.succ_pos n
  have hm : 0<m := pow_pos hn 32
  have hb := initialError_fourth (N:=N) hm 1 (by norm_num)
  have hv := budget_mem odd hm T
  have nw : 0≤w := by unfold w;positivity
  have env := CircleSharpMoments.envelope hb.1 hv w nw
  let L := fun z => 6*(B z*V z)+(44928*w)*((1+V z)*V z)+w
  have good (z) (hz : z∈E) : |Y z-reference N m (stoppedWeight n T) z|≤L z := by
    apply (cap z hz).trans
    change 6*B z*V z+44928*(1+V z)*V z/(N:ℝ)^16 ≤ _
    dsimp only [L,w]
    change 0≤1/(N:ℝ)^16 at nw
    ring_nf at nw ⊢
    linarith only [nw]
  have bound := split_mse me env.1 Dint good (by positivity : 0≤65/(N:ℝ)^16) tail
  apply bound.trans ((add_le_add env.2 le_rfl).trans ?_)
  have width : sqrt (m:ℝ) = (N:ℝ)^16 := by unfold m;push_cast; rw [show (N:ℝ)^32=((N:ℝ)^16)^2 by ring,sqrt_sq (by positivity)]
  have cg : 0≤truncConstant := lpNorm_nonneg.trans (by simpa using budget_lp4 odd hm 0)
  have bb : lpNorm B 4 μ≤6*markConstant/(N:ℝ)^16 := hb.2.trans_eq (by rw [width])
  exact collect hn lpNorm_nonneg bb (norm_budget odd hm T) (add_nonneg budgetConstant_nonneg cg)

/-- The exact stopped same-seed RMS across all initializations is bounded
by C min(N, sqrt(T+1))/N¹⁶ for the once-capped learner through 385 N³.
The constant is absolute and the width is exactly N³². -/
theorem capped_stopped_sharp (n T : ℕ) (hN : 12000000≤n+1) (odd : Odd (n+1)) (ht : T≤385*(n+1)^3) :
    let N := n+1
    sqrt (∫ z, (cappedY N (N^32) T z-reference N (N^32) (stoppedWeight n T) z)^2 ∂seedLaw (N^32)) ≤
      errorConstant*shape N T/(N:ℝ)^16 := by
  intro N
  let m := N^32
  let A := screen N m
  let b := stoppedWeight n T
  have nn : 0<N := Nat.succ_pos n
  have hm := pow_pos nn 32
  have hlarge : 12000000≤N := hN
  have hb := stopped_bounds n T
  have hsteps := CircleDiscreteMoments.cap_steps hlarge ht
  obtain ⟨E,me,p,inside⟩ := gaussian_stopped n 158 T (by omega) (by omega) odd
  have am : MeasurableSet A := screen_measurable N m (by omega) odd hm
  let μ := seedLaw m
  have bad : μ.real (E∩A)ᶜ≤15/(N:ℝ)^158 := by
    rw [compl_inter]
    exact ((measureReal_union_le _ _).trans (add_le_add p (CircleDiscreteMoments.reject_pow N hlarge odd))).trans_eq (by ring)
  have sqint := (cappedSq_mem N m T (by omega) odd hm hsteps b hb.1 hb.2).integrable one_le_two
  apply rms_bound n T odd (cappedY N m T) sqint (E∩A) (me.inter am) _ ((exceptional_mse N m T (by omega) odd hm
    hsteps b hb.1 hb.2 (E∩A)ᶜ).trans (tail_sq nn bad))
  intro z hz
  have eq := CircleInitializationCheck.trajectory_on_check N m _ hz.2 (initial z)
  have yes : cappedY N m T z = trainedMean (path N m 1) T z := by
    unfold cappedY rate
    rw [eq]
    rfl
  rw [yes]
  exact inside z hz.1

open CircleFlowTracking CircleSpectrum CircleResidualSpectrum

private theorem mode_nonneg : 0≤modeConstant := CircleSpectralPathLength.modeConstant_nonneg

private theorem constant_nonneg : 0≤errorConstant := by
  have mc : 0≤markConstant := by unfold markConstant;positivity
  have tc : 0≤truncConstant := by
    have := CircleSpectralPathLength.shellConstant_pos
    unfold truncConstant
    positivity [mode_nonneg]
  have ac : 0≤areaConstant := add_nonneg budgetConstant_nonneg tc
  unfold errorConstant
  positivity

/-- The difference to the infinite-time reference has a separate constant
grid-mode transient. The paired reference uses the same Gaussian seed. -/
theorem capped_full_sharp (n T : ℕ) (hN : 12000000≤n+1) (odd : Odd (n+1)) (ht : T≤385*(n+1)^3) :
    let N := n+1
    sqrt (∫ z, (cappedY N (N^32) T z-reference N (N^32) (weight 1 n) z)^2 ∂seedLaw (N^32)) ≤
      errorConstant*shape N T/(N:ℝ)^16 + (1-gamma N)^T*modeConstant := by
  intro N
  have h := CircleComparison.change_reference_bound (N:=N) (m:=N^32) (by omega) (pow_pos (Nat.succ_pos n) 32)
    (cappedY N (N^32) T) (CircleGDLimits.cap_mem hN odd ht) (weight 1 n) (stoppedWeight n T)
  apply h.trans (add_le_add (capped_stopped_sharp n T hN odd ht) (mul_le_mul_of_nonneg_right _ mode_nonneg))
  have wt := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  have p := pow_nonneg (sub_nonneg.mpr (gamma_bounds (N:=N)).2) T
  rw [stoppedWeight,show weight 1 n*(1-(1-gamma (n+1))^T)-weight 1 n = -(weight 1 n*(1-gamma N)^T) by ring,
    abs_neg,abs_of_nonneg (mul_nonneg wt.1 p)]
  exact mul_le_of_le_one_left p wt.2

/-- Actual once-capped GD at M: full-reference paired RMS O(sqrt(log N)/N¹⁶). -/
theorem capped_medium_sharp (n : ℕ) (hN : 12000000≤n+1) (odd : Odd (n+1)) :
    let N := n+1
    let M := medium (N:ℝ)
    sqrt (∫ z, (cappedY N (N^32) M z-reference N (N^32) (weight 1 n) z)^2 ∂seedLaw (N^32)) ≤
      (errorConstant+modeConstant)*sqrt (2+60*log N)/(N:ℝ)^16 := by
  intro N M
  have hn : (1:ℝ)≤N := by exact_mod_cast (Nat.succ_pos n)
  have np : (0:ℝ)<N := by linarith
  have ht : M≤385*N^3 := by simpa [M,N] using (CircleGDLimits.benchmark_times n).2.1
  have mid : shape N M ≤ sqrt (2+60*log N) := by
    apply (min_le_right _ _).trans (sqrt_le_sqrt ?_)
    have h := (Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0:ℝ)≤60) (log_nonneg hn))).le
    change (M:ℝ)≤60*log N+1 at h
    push_cast;linarith only [h]
  have x1 : 1≤sqrt (2+60*log N) := one_le_sqrt.mpr (by linarith [log_nonneg hn])
  have d := (medium_transient (N:=N)).trans (div_le_div_of_nonneg_left zero_le_one (by positivity) (pow_le_pow_right₀ hn (by decide : 16≤18)))
  have small : (1-gamma N)^M*modeConstant ≤ modeConstant*sqrt (2+60*log N)/(N:ℝ)^16 := by
    exact ((mul_le_mul_of_nonneg_right d mode_nonneg).trans_eq (by ring : 1/(N:ℝ)^16*modeConstant=modeConstant/(N:ℝ)^16)).trans
      (div_le_div_of_nonneg_right (le_mul_of_one_le_right mode_nonneg x1) (by positivity))
  exact ((capped_full_sharp n M hN odd ht).trans (add_le_add (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left mid constant_nonneg) (by positivity)) small)).trans_eq (by ring)

/-- Actual once-capped GD at H: full-reference paired RMS O(N⁻¹⁵). -/
theorem capped_horizon_sharp (n : ℕ) (hN : 12000000≤n+1) (odd : Odd (n+1)) :
    let N := n+1
    let H := horizon (N:ℝ)
    sqrt (∫ z, (cappedY N (N^32) H z-reference N (N^32) (weight 1 n) z)^2 ∂seedLaw (N^32)) ≤
      (errorConstant+modeConstant)/(N:ℝ)^15 := by
  intro N H
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.succ_pos n)
  have ht : H≤385*N^3 := by simpa [H,N] using (CircleGDLimits.benchmark_times n).2.2.2
  have th : 15≤6*N^2 := le_trans (by decide : (15:ℕ)≤6*3^2) (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left (by dsimp [N];omega) 2))
  have d := horizon_transient (N:=N) (by omega) 15 th
  exact ((capped_full_sharp n H hN odd ht).trans (add_le_add (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (min_le_left ..) constant_nonneg) (by positivity))
    (mul_le_mul_of_nonneg_right d mode_nonneg))).trans_eq (by field_simp;ring)

/-- Transfer every paired MSE estimate to the actual standard-Gaussian
acceptance-conditioned law. The price is the exact lower probability bound
for passing the once-only curvature check. -/
theorem accepted_transfer (n T : ℕ) (hN : 12000000≤n+1) (odd : Odd (n+1)) (ht : T≤385*(n+1)^3)
    (b : ℝ) (hb : 0≤b) (hb' : b≤1) :
    let N := n+1
    let m := N^32
    sqrt (∫ z, (trainedMean (path N m 1) T z-reference N m b z)^2 ∂CircleGDLimits.acceptedLaw n) ≤
      sqrt (∫ z, (cappedY N m T z-reference N m b z)^2 ∂seedLaw m)/sqrt (1-exp (-(m:ℝ)/240)) := by
  intro N m
  have prob := conditional_mse N m T (by omega) odd (pow_pos (Nat.succ_pos n) 32)
    (CircleDiscreteMoments.cap_steps hN ht) b hb hb'
  have eq : (∫ z, (trainedMean (path N m 1) T z-reference N m b z)^2 ∂CircleGDLimits.acceptedLaw n) =
      (∫ z in screen N m, fixedSq N m T b z ∂seedLaw m)/(seedLaw m).real (screen N m) := by
    change (∫ z, (trainedMean (path N m 1) T z-reference N m b z)^2 ∂((seedLaw m) (screen N m))⁻¹ • (seedLaw m).restrict (screen N m)) = _
    rw [integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,div_eq_inv_mul]
    rfl
  rw [eq]
  exact (sqrt_le_sqrt prob).trans_eq (sqrt_div (integral_nonneg (fun z => sq_nonneg _)) _)

open CircleShortGDTails

private theorem rejected_short32 (N : ℕ) (hN : 12000000 ≤ N) :
    sqrt (fourthBound (N^32) (earlyCap N))*exp (-((N^32:ℕ):ℝ)/480) ≤ 1/(N:ℝ)^32 := by
  have h1 : 1 ≤ N := le_trans (by decide) hN
  have n1 : (1:ℝ) ≤ N := by exact_mod_cast h1
  have np : 0 < (N:ℝ) := by linarith
  have nl : (12000000:ℝ) ≤ N := by exact_mod_cast hN
  have f := fourthBound (N^32) (earlyCap N)
  have hb := CircleShortGDTails.log_fourthBound N h1
  have hp : 0 < fourthBound (N^32) (earlyCap N) := by unfold fourthBound momentDegree; positivity
  have g : (N:ℝ)^7 ≥ 11520000 := by linarith [le_self_pow₀ n1 (by norm_num : 7 ≠ 0)]
  have bound : 12000*(N:ℝ)^25 ≤ (N:ℝ)^32/960 := by
    nlinarith [mul_le_mul_of_nonneg_right g (by positivity : 0 ≤ (N:ℝ)^25)]
  have root : sqrt (fourthBound (N^32) (earlyCap N)) ≤ exp ((N:ℝ)^32/960) := by
    apply sqrt_le_iff.mpr
    refine ⟨(exp_pos _).le,?_⟩
    rw [← exp_log hp,← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
    nlinarith only [hb,bound,pow_nonneg np.le 32]
  rw [Nat.cast_pow]
  apply (mul_le_mul_of_nonneg_right root (exp_pos _).le).trans
  rw [← exp_add,show (N:ℝ)^32/960 + -((N:ℝ)^32)/480 = -((N:ℝ)^32/960) by ring,exp_neg,one_div]
  apply inv_anti₀ (by positivity : (0:ℝ) < (N:ℝ)^32)
  nth_rw 1 [← exp_log (by positivity : (0:ℝ) < (N:ℝ)^32)]
  apply exp_le_exp.mpr
  rw [log_pow]
  norm_num
  have g2 : (N:ℝ)^2 ≤ (N:ℝ)^32 := pow_le_pow_right₀ n1 (by norm_num)
  nlinarith [log_le_sub_one_of_pos np,mul_le_mul_of_nonneg_right nl np.le]

/-- Even on the unconditioned seed law, the true unit-step learner at S
tracks its finite-time reference to the same order as the capped algorithm. -/
theorem ordinary_short_sharp (n : ℕ) (hN : 12000000≤n+1) (odd : Odd (n+1)) :
    let N := n+1
    let T := earlyCap N
    sqrt (∫ z, (trainedMean (path N (N^32) 1) T z-reference N (N^32) (stoppedWeight n T) z)^2 ∂seedLaw (N^32)) ≤
      errorConstant*shape N T/(N:ℝ)^16 := by
  intro N T
  let m := N^32
  let b := stoppedWeight n T
  have hn : 0<N := Nat.succ_pos n
  have hm : 0<m := pow_pos hn 32
  have hbig : 12000000≤N := hN
  have hb := stopped_bounds n T
  have hi := ((trained_memLp N m T 1 2 (by norm_num)).sub (reference_memLp N m b 2 (by norm_num))).integrable_sq
  obtain ⟨E,me,p,good⟩ := gaussian_stopped n 158 T (by omega) (by omega) odd
  apply rms_bound n T odd (trainedMean (path N m 1) T) hi E me good
  have tail := CircleShortGDTails.exceptional_mse N m T (by omega) odd hm (earlyCap_width N (by omega)) hb.1 hb.2 Eᶜ me.compl
  have p15 := p.trans (div_le_div_of_nonneg_right (by norm_num : (14:ℝ)≤15) (by positivity))
  exact (tail.trans (add_le_add (le_refl _) (rejected_short32 N hN))).trans (tail_with_rejection hn p15)

/-- The unrestricted original learner at S versus the infinite-time reference,
including the finite-time constant-mode contribution. -/
theorem ordinary_short_full (n : ℕ) (hN : 12000000≤n+1) (odd : Odd (n+1)) :
    let N := n+1
    let T := earlyCap N
    sqrt (∫ z, (trainedMean (path N (N^32) 1) T z-reference N (N^32) (weight 1 n) z)^2 ∂seedLaw (N^32)) ≤
      errorConstant*shape N T/(N:ℝ)^16 + modeConstant/(N:ℝ)^3 := by
  intro N T
  have base := CircleComparison.change_reference_bound (N:=N) (m:=N^32) (by omega) (pow_pos (Nat.succ_pos n) 32)
    _ (trained_memLp N (N^32) T 1 2 (by norm_num)) (weight 1 n) (stoppedWeight n T)
  have w := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  have gm := gamma_bounds (N:=N)
  have p := pow_nonneg (sub_nonneg.mpr gm.2) T
  have tr : |stoppedWeight n T-weight 1 n| ≤ 1/(N:ℝ)^3 := by
    rw [stoppedWeight,show weight 1 n*(1-(1-gamma (n+1))^T)-weight 1 n = -(weight 1 n*(1-gamma N)^T) by ring,
      abs_neg,abs_of_nonneg (mul_nonneg w.1 p)]
    exact (mul_le_of_le_one_left p w.2).trans (short_transient (N:=N))
  exact base.trans (add_le_add (ordinary_short_sharp n hN odd)
    ((mul_le_mul_of_nonneg_right tr mode_nonneg).trans_eq (by ring)))

/-- Medium and fitting horizons under the conditioned standard Gaussian law.
The exact denominator is common to the two physical update counts. -/
theorem accepted_benchmarks_sharp (n : ℕ) (hN : 12000000≤n+1) (odd : Odd (n+1)) :
    let N := n+1
    let m := N^32
    let rms := fun T => sqrt (∫ z, (trainedMean (path N m 1) T z-reference N m (weight 1 n) z)^2 ∂CircleGDLimits.acceptedLaw n)
    let p := sqrt (1-exp (-(m:ℝ)/240))
    rms (medium N) ≤ ((errorConstant+modeConstant)*sqrt (2+60*log N)/(N:ℝ)^16)/p ∧
    rms (horizon N) ≤ ((errorConstant+modeConstant)/(N:ℝ)^15)/p := by
  intro N m rms p
  have times := CircleGDLimits.benchmark_times n
  have wm := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  have mtime : medium N≤385*(n+1)^3 := by simpa [N] using times.2.1
  have htime : horizon N≤385*(n+1)^3 := by simpa [N] using times.2.2.2
  exact ⟨(accepted_transfer n (medium N) hN odd mtime _ wm.1 wm.2).trans
    (div_le_div_of_nonneg_right (capped_medium_sharp n hN odd) (sqrt_nonneg _)),
    (accepted_transfer n (horizon N) hN odd htime _ wm.1 wm.2).trans
    (div_le_div_of_nonneg_right (capped_horizon_sharp n hN odd) (sqrt_nonneg _))⟩

end CircleSharpGDMoments
