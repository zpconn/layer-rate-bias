module

public import CircleDiscreteTracking
public import CircleSharpEvent
public import CircleShortGDTails
import all CircleSeedIntegrability
import all CircleEscapeBridge
import all CircleCapMoments
import all CircleKernelGD
import all CircleGaussianTracking
import all CircleShortGDTails
import all CircleSharpEvent
import all CircleDiscreteTracking
import all CircleActualTracking
import Mathlib.Tactic

/-! Gaussian specialization for the original, simultaneous unit-step learner. -/
public section
noncomputable section
namespace CircleDiscreteMoments
open Real MeasureTheory Set CircleEscapeBridge CircleTangentDrift CircleActualTracking
open CircleGridSpectrum CircleSpectrum CircleDiscreteTracking CircleKernelGD
open CircleGaussianTracking CircleSharpInitialization CircleSharpEvent CircleShortGDTails
open CircleSeedIntegrability

/-- The RMS of the initial Gram and row errors obeys the logarithmic,
inverse-square-root-width concentration bound at every fixed confidence power. -/
theorem operator_error_tail (N k : ℕ) [NeZero N] (hN : 192≤N) (hk : k+2≤N)
    (τ : ℝ) (hτ : |τ|≤2) :
    (seedLaw (N^32)).real {z | 768*sqrt (((k:ℝ)+2)*log N)/(N:ℝ)^16 < initialError N (N^32) τ z}
      ≤ 10/(N:ℝ)^k := by
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  have one : (1:ℝ)≤N := by exact_mod_cast (NeZero.pos N)
  have nh : (192:ℝ)≤N := by exact_mod_cast hN
  let L := ((k:ℝ)+2)*log N
  let u := 192*sqrt L/(N:ℝ)^16
  have lp : 0≤L := mul_nonneg (by positivity) (log_nonneg one)
  have ls : sqrt L ≤ (N:ℝ) := by
    have lc := CircleSharpEvent.log_cost N (k+2) hk (NeZero.pos N)
    push_cast at lc
    exact (sqrt_le_sqrt lc).trans_eq (sqrt_sq np.le)
  have hu : 0≤u := by dsimp [u]; positivity
  have hu' : u≤1 := by
    apply (div_le_one (by positivity : 0<(N:ℝ)^16)).2
    exact ((mul_le_mul nh ls (sqrt_nonneg _) np.le).trans_eq (by ring : (N:ℝ)*N=N^2)).trans
      (pow_le_pow_right₀ one (by decide : 2≤16))
  have h := CircleGaussianBernstein.goodInit_exponential (N:=N) (pow_pos (NeZero.pos N) 32)
    (ρ:=0) (u:=u) hτ le_rfl zero_le_one hu hu'
  have incl : {z | 768*sqrt (((k:ℝ)+2)*log N)/(N:ℝ)^16 < initialError N (N^32) τ z} ⊆
      {z | ¬GoodInit τ 0 u (sampledMatrix τ) (fun _ : Fin N => k0 τ) z} := by
    intro z hz hg
    have b := initialError_le_of_good hu hg
    exact (not_lt.mpr (b.trans_eq (by dsimp [u,L]; ring))) hz
  apply ((measureReal_mono (μ:=seedLaw (N^32)) incl).trans h).trans
  have eq : -((N^32:ℕ):ℝ)*u^2/36864 = -(↑(k+2):ℝ)*log N := by
      push_cast; dsimp [u]; rw [div_pow,mul_pow,sq_sqrt lp]; dsimp [L]; field_simp; ring
  rw [eq, neg_mul, exp_neg, exp_nat_mul, exp_log np]
  have hb : ((N:ℝ)+1)^2+1 ≤ 5*(N:ℝ)^2 := by nlinarith [sq_nonneg ((N:ℝ)-1)]
  apply (mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ)≤2*((N:ℝ)^(k+2))⁻¹)).trans_eq
  rw [pow_add]; field_simp;ring

/-- One measurable initialization event supplies the true discrete bootstrap,
including its RMS envelope. Its complement has any requested fixed inverse
power under the unrestricted standard Gaussian seed law. -/
theorem design_event (N k : ℕ) [NeZero N] (hN : 36864 ≤ N) (hk : k+2≤N) :
    ∃ E : Set (Seed (N^32)), MeasurableSet E ∧ (seedLaw (N^32)).real Eᶜ ≤ 12/(N:ℝ)^k ∧
      ∀ z ∈ E, (GoodInit 1 (designRadius N) (designTolerance N) (sampledMatrix 1) (fun _ : Fin N => k0 1) z) ∧
        ‖gridR N z‖ ≤ 66*(N:ℝ) ∧ ‖gridR N z‖≤(N:ℝ)^2 := by
  have nr : (36864:ℝ)≤N := by exact_mod_cast hN
  have d : (32:ℝ)≤N := by linarith
  have np : (0:ℝ)<N := by linarith
  have hρ : 0 ≤ designRadius N := by unfold designRadius; positivity
  let I := {z : Seed (N^32) | ¬GoodInit 1 (designRadius N) (designTolerance N) (sampledMatrix 1) (fun _ : Fin N => k0 1) z}
  let R := {z : Seed (N^32) | 2+64*sqrt (((k:ℝ)+1)*log N) < initialRms N (N^32) z}
  let μ := seedLaw (N^32)
  have i : μ.real I ≤ 10/(N:ℝ)^k := initialization_power N k hN hk (by norm_num) hρ (design_bounds d).1
  have r : μ.real R ≤ 2/(N:ℝ)^k := initialRms_schedule_tail (N:=N) k (by omega)
  refine ⟨(toMeasurable μ (I∪R))ᶜ,(measurableSet_toMeasurable _ _).compl,?_,?_⟩
  · change μ.real ((toMeasurable μ (I∪R))ᶜ)ᶜ ≤ _
    rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    exact ((measureReal_union_le _ _).trans (add_le_add i r)).trans_eq (by ring)
  · intro z hz
    have h : z ∉ I∪R := fun H => hz (subset_toMeasurable _ _ H)
    have g : z∉I ∧ z∉R := by simpa only [Set.mem_union,not_or] using h
    have ls : sqrt (((k:ℝ)+1)*log N) ≤ (N:ℝ) := by
      have lc := CircleSharpEvent.log_cost N (k+1) (by omega) (by omega)
      push_cast at lc
      exact (sqrt_le_sqrt lc).trans_eq (sqrt_sq np.le)
    have hz' : ‖gridR N z‖ ≤ 2+64*sqrt (((k:ℝ)+1)*log N) := le_of_not_gt g.2
    refine ⟨not_not.mp g.1,by linarith,?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr nr) np.le]

/-- At the paper horizon H, the original fixed unit step fits the full
training grid with RMS at most N⁻³ at any prescribed polynomial confidence. -/
theorem gaussian_horizon_fit (N k : ℕ) [NeZero N] (hN : 36864 ≤ N) (hk : k+2≤N) (odd : Odd N) :
    (seedLaw (N^32)).real {z | 1/(N:ℝ)^3 < ‖gridR N (iterate N z (CircleFlowTracking.horizon N))‖} ≤ 12/(N:ℝ)^k := by
  obtain ⟨E,_,prob,good⟩ := design_event N k hN hk
  apply (measureReal_mono (μ:=seedLaw (N^32)) (s₂:=Eᶜ) (fun ⦃z⦄ hz hg => ?_)).trans prob
  obtain ⟨G,_,init⟩ := good z hg
  exact (not_lt.mpr (design_trajectory (by omega) odd z G init).2.1) hz

private theorem early_le (N : ℕ) (one : (1:ℝ)≤N) : (earlyCap N:ℝ)≤17*(N:ℝ) := by
    have pp : π^2≤16 := by nlinarith [mul_nonneg (sub_nonneg.mpr pi_lt_four.le) (show 0≤4+π by positivity)]
    have h := (Nat.ceil_lt_add_one (mul_nonneg (sq_nonneg π) (log_nonneg one))).le
    change (earlyCap N:ℝ)≤π^2*log N+1 at h
    linarith [mul_le_mul pp (log_le_self (Nat.cast_nonneg N)) (log_nonneg one) (by norm_num : (0:ℝ)≤16)]

/-- Under the original unconditioned Gaussian law, the true simultaneous GD
mean at the logarithmic cap tracks the exactly stopped same-seed kernel
reference with mean-square error of order N⁻¹⁰. -/
theorem early_stopped_mse (n : ℕ) (hN : 12000000 ≤ n+1) (odd : Odd (n+1)) :
    let N := n+1
    let t := earlyCap N
    ∫ z, (rawError N (N^32) t (stoppedWeight n t) z)^2 ∂seedLaw (N^32) ≤
      ((198*66*17:ℝ)^2+1044*sqrt 12+1)/(N:ℝ)^10 := by
  intro N t
  let μ := seedLaw (N^32)
  let b := stoppedWeight n t
  let F := rawError N (N^32) t b
  have np : (0:ℝ)<N := by dsimp [N];positivity
  have one : (1:ℝ)≤N := by dsimp [N];push_cast;linarith
  have nh : (12000000:ℕ)≤N := hN
  have odd' : Odd N := odd
  have w := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  have gm := gamma_bounds (N:=N)
  have g0 : 0≤gamma N := (show (0:ℝ)≤3/π^2 by positivity).trans gm.1
  have hb : 0≤b ∧ b≤1 := by
    have p0 := pow_nonneg (sub_nonneg.mpr gm.2) t
    have p1 := pow_le_one₀ (sub_nonneg.mpr gm.2) (sub_le_self _ g0) (n:=t)
    exact ⟨mul_nonneg w.1 (sub_nonneg.mpr p1),(mul_le_of_le_one_left (sub_nonneg.mpr p1) w.2).trans (sub_le_self _ p0)⟩
  obtain ⟨E,me,prob,good⟩ := design_event N 158 (by omega) (by omega)
  have bad := early_bad_mse N nh odd' hb.1 hb.2 (by norm_num : (0:ℝ)≤12) Eᶜ me.compl prob
  have htime := early_le N one
  let B := (198*66*17:ℝ)/(N:ℝ)^5
  have Fbound (z) (hz : z ∈ E) : |F z| ≤ B := by
    obtain ⟨G,R,R0⟩ := good z hz
    have tr := stopped_tracking n (by omega) odd z (by simpa [N] using G) (by simpa [N] using R0) t
    change |F z| ≤ 3*(66/(N:ℝ)^7)*‖gridR N z‖*t at tr
    apply tr.trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left R (show 0≤3*(66/(N:ℝ)^7) by positivity))
      htime (Nat.cast_nonneg _) (by positivity)).trans_eq (by unfold B;field_simp;ring)
  have hi : Integrable (fun z => F z^2) μ :=
    ((trained_memLp N (N^32) t 1 2 (by norm_num)).sub (reference_memLp N (N^32) b 2 (by norm_num))).integrable_sq
  change (∫ z, F z^2 ∂μ) ≤ _
  rw [← integral_add_compl me hi]
  have gg := setIntegral_mono_on hi.integrableOn (integrable_const (B^2)).integrableOn me
    (fun z hz => (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (Fbound z hz) 2))
  have gb : (∫ z in E, F z^2 ∂μ) ≤ B^2 := by
    simpa [setIntegral_const,smul_eq_mul] using gg.trans (by
      simpa [setIntegral_const,smul_eq_mul] using (mul_le_of_le_one_left (sq_nonneg B) (measureReal_le_one (μ:=μ) (s:=E))))
  exact (add_le_add gb bad).trans_eq (by dsimp [B];field_simp;ring)

open CircleCapMoments

private theorem cap_steps {N t : ℕ} (hN : 12000000≤N) (ht : t ≤ 385*N^3) : 200*t≤N^32 := by
  calc
    200*t ≤ 200*(385*N^3) := Nat.mul_le_mul_left _ ht
    _ ≤ N*N^3 := by rw [←Nat.mul_assoc];exact Nat.mul_le_mul_right _ (by omega)
    _ = N^4 := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

private theorem reject_pow (N : ℕ) (hN : 12000000≤N) (odd : Odd N) :
    (seedLaw (N^32)).real (screen N (N^32))ᶜ ≤ 1/(N:ℝ)^158 := by
  have r := reject_probability N (N^32) (by omega) odd (pow_pos (by omega) _)
  have e : (screen N (N^32))ᶜ = {ω | 1 < CircleCapInduction.curvature (CircleEscape.gridPoint N) (initial ω)} := by
    ext; simp [screen]
  rw [e]
  apply r.trans
  push_cast
  rw [neg_div]
  apply CircleSharpEvent.exp_inverse_power (Nat.cast_pos.mpr (by omega)) 158
  have n : (12000000:ℝ)≤N := by exact_mod_cast hN
  have l := CircleSharpEvent.log_cost N 158 (by omega) (by omega)
  apply l.trans
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<240)]
  exact ((mul_le_mul_of_nonneg_left (show (240:ℝ)≤N by linarith) (sq_nonneg _)).trans_eq
    (by ring : (N:ℝ)^2*N=N^3)).trans (pow_le_pow_right₀ (by linarith : (1:ℝ)≤N) (by decide : 3≤32))

private theorem cap_tail_arithmetic {N : ℕ} (hn : 0<N) {p : ℝ} (hp : p≤13/(N:ℝ)^158) :
    1044*(N^32:ℕ)*sqrt p ≤ 1044*sqrt 13/(N:ℝ)^6 := by
  have np : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have ns : (1:ℝ)≤N := by exact_mod_cast hn
  have sb := sqrt_le_sqrt hp
  rw [sqrt_div (by norm_num), show (N:ℝ)^158=((N:ℝ)^79)^2 by ring,sqrt_sq (by positivity)] at sb
  push_cast
  apply (mul_le_mul_of_nonneg_left sb (by positivity : 0≤1044*(N:ℝ)^32)).trans
  calc
    _ = 1044*sqrt 13/(N:ℝ)^47 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ ns (by decide : 6≤47))

/-- For the whole Gaussian law, the once-capped learner tracks the exactly
stopped reference at every step through 385 N³, in particular S, M and H.
On the acceptance event, the same endpoint bound holds for ordinary GD
after division by the acceptance probability. -/
theorem capped_stopped_mse (n : ℕ) (hN : 12000000≤n+1) (odd : Odd (n+1)) (t : ℕ)
    (ht : t≤385*(n+1)^3) :
    let N := n+1
    let b := stoppedWeight n t
    ∫ z, cappedSq N (N^32) t b z ∂seedLaw (N^32) ≤
      ((198*66*385:ℝ)^2+1044*sqrt 13)/(N:ℝ)^6 := by
  intro N b
  let μ := seedLaw (N^32)
  let A := screen N (N^32)
  have nh : (12000000:ℕ)≤N := hN
  have hn : 0<N := by omega
  have hm := pow_pos hn 32
  have np : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have wt := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  have gm := gamma_bounds (N:=N)
  have g0 : 0≤gamma N := (show (0:ℝ)≤3/π^2 by positivity).trans gm.1
  have p0 := pow_nonneg (sub_nonneg.mpr gm.2) t
  have p1 := pow_le_one₀ (sub_nonneg.mpr gm.2) (sub_le_self _ g0) (n:=t)
  have hb : 0≤b ∧ b≤1 := ⟨mul_nonneg wt.1 (sub_nonneg.mpr p1),
    (mul_le_of_le_one_left (sub_nonneg.mpr p1) wt.2).trans (sub_le_self _ p0)⟩
  obtain ⟨E,me,prob,good⟩ := design_event N 158 (by omega) (by omega)
  have mA : MeasurableSet A := screen_measurable _ _ (by omega) odd hm
  have fail : μ.real (E∩A)ᶜ ≤ 13/(N:ℝ)^158 := by
    rw [compl_inter]
    exact ((measureReal_union_le _ _).trans (add_le_add prob (reject_pow N nh odd))).trans_eq (by ring)
  have bad := (exceptional_mse N (N^32) t (by omega) odd hm (cap_steps nh ht) b hb.1 hb.2 (E∩A)ᶜ).trans
    (cap_tail_arithmetic hn fail)
  let B := (198*66*385:ℝ)/(N:ℝ)^3
  have pass (z) (hz : z∈E∩A) : cappedSq N (N^32) t b z ≤ B^2 := by
    obtain ⟨G,R,R0⟩ := good z hz.1
    have tr := stopped_tracking n (by omega) odd z (by simpa [N] using G) (by simpa [N] using R0) t
    have tB : (t:ℝ)≤385*(N:ℝ)^3 := by exact_mod_cast ht
    have ub : |rawError N (N^32) t b z| ≤ B := tr.trans ((mul_le_mul (mul_le_mul_of_nonneg_left R
      (show 0≤3*(66/(N:ℝ)^7) by positivity)) tB (Nat.cast_nonneg _) (by positivity)).trans_eq
      (by unfold B;field_simp;ring))
    have eq := CircleInitializationCheck.trajectory_on_check N (N^32) _ hz.2 (initial z)
    change (CircleEscape.populationMean _ (CircleInitializationCheck.train _ _ (CircleCapMoments.rate _ _ _) _ _) - _)^2 ≤ _
    rw [CircleCapMoments.rate,eq]
    simpa only [sq_abs,rawError,trainedMean,CircleSeedIntegrability.path] using pow_le_pow_left₀ (abs_nonneg _) ub 2
  have hi := (cappedSq_mem N (N^32) t (by omega) odd hm (cap_steps nh ht) b hb.1 hb.2).integrable one_le_two
  rw [← integral_add_compl (me.inter mA) hi]
  have gg := setIntegral_mono_on hi.integrableOn (integrable_const (B^2)).integrableOn (me.inter mA) pass
  have gb : (∫ z in E∩A, cappedSq N (N^32) t b z ∂μ) ≤ B^2 := gg.trans (by
    simpa [setIntegral_const,smul_eq_mul] using (mul_le_of_le_one_left (sq_nonneg B) (measureReal_le_one (μ:=μ) (s:=E∩A))))
  exact (add_le_add gb bad).trans_eq (by dsimp [B];field_simp)

end CircleDiscreteMoments
