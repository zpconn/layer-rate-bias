module

public import CircleDiscreteMoments
public import CircleFourthEigen
import all CircleFourthEigen
import all CircleSharpTracking
import all CircleActualTracking
import all CircleTangentDrift
import all CircleKernelGD
import all CircleFlowPath
import all CircleSpectralPathLength
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Short-time Fourier projections of ordinary continuous gradient flow. -/
public section
noncomputable section
namespace CircleShortFlowProjection
open Real MeasureTheory Set Filter CircleFlowPath CircleTangentDrift CircleActualTracking CircleSharpTracking
open CircleEscapeBridge CircleGridSpectrum

/-- In normalized grid coordinates the full residual differs from the
frozen solution by at most 66 T / N⁵ on the calibrated deterministic
initialization event. This bound holds at every finite physical time. -/
theorem residual_frozen {N : ℕ} [NeZero N] (hN : 32 ≤ N) (odd : Odd N) {T : ℝ} (ht : 0 ≤ T)
    (z : ℝ → State (N^32)) (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt ((N^32:ℕ):ℝ)) 1 T z)
    (G : GoodInit 1 (designRadius N) (designTolerance N) (sampledMatrix 1) (fun _ : Fin N => CircleSpectrum.k0 1) (z 0))
    (init : ‖gridR N (z 0)‖ ≤ (N:ℝ)^2) (nz : ∀ j, 0 < length (z 0) j) :
    ‖gridR N (z T)-CircleSpectralPathLength.referencePath 1
      (residual (circleInput N) (circleLabel N) (1/sqrt ((N^32:ℕ):ℝ)) (z 0)) T‖ ≤ 66*T/(N:ℝ)^5 := by
  let r := fun s => gridR N (z s)
  let f := CircleSpectralPathLength.referencePath 1
    (residual (circleInput N) (circleLabel N) (1/sqrt ((N^32:ℕ):ℝ)) (z 0))
  let K := gramOp (sampledMatrix (N:=N) 1)
  let e := 2*(30*designRadius N+3*designTolerance N)
  have d : (32:ℝ) ≤ N := by exact_mod_cast hN
  have np : (0:ℝ)<N := by linarith
  have hn : 0<N := by omega
  have hm := pow_pos hn 32
  have hp : 0 < designRadius N := by unfold designRadius; positivity
  have hu : 0 ≤ designTolerance N := by unfold designTolerance; positivity
  have hk : 0 < designDecay N := by unfold designDecay; positivity
  obtain ⟨rs,ecap,sc,budget⟩ := design_bounds d
  have width : sqrt ((N^32:ℕ):ℝ) = (N:ℝ)^16 := by
    push_cast; rw [show (N:ℝ)^32=((N:ℝ)^16)^2 by ring,sqrt_sq (by positivity)]
  have gap (v : EuclideanSpace ℝ (Fin N)) := gramOp_gap (by omega : 3≤N) odd 1 (by norm_num) (by norm_num) v
  have bd : 4*(N:ℝ)^2/(sqrt ((N^32:ℕ):ℝ)*designDecay N) < designRadius N/2 := by rw [width]; exact budget
  have conf := actual_confinement F G hn hm (by norm_num) ht hk hp rs hu
    (fun v => (mul_le_mul_of_nonneg_right sc (sq_nonneg _)).trans (gap v)) init nz bd
  have start : r 0 = f 0 := (CircleSpectralPathLength.referencePath_zero 1 _).symm
  have df (s : ℝ) : HasDerivAt f (-(K (f s))) s :=
    CircleSpectralPathLength.referencePath_deriv 1 (by norm_num) (by norm_num) _ s
  have rac := actual_grid_ac F
  have fac := CircleSharpTracking.frozen_ac K df T
  have ac : AbsolutelyContinuousOnInterval (fun s => ‖r s-f s‖) 0 T :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval (rac.fun_sub fac)
  have ar : IntervalIntegrable (fun s => ‖r s‖) volume 0 T := rac.continuousOn.norm.intervalIntegrable
  have non : 0 ≤ e := by dsimp [e]; positivity
  have h := frozen_error_balance r f K (lam:=0) ht non ac ar start
    (fun v => (mul_nonneg (by positivity : 0≤1/(π*(N:ℝ))^2) (sq_nonneg _)).trans' (by simp) |>.trans (gap v)) (by
      filter_upwards [ae_grid_hilbert_ode F] with s hs hst
      obtain ⟨g,ad,dr⟩ := hs (by rwa [uIcc_of_le ht])
      refine ⟨_,dr,df s,?_⟩
      rw [norm_sub_rev]
      exact (G.track_ops hn hm (by norm_num) hp.le rs hu (conf s hst).1 ad).1)
  simp only [zero_mul,add_zero] at h
  have bound (s : ℝ) (hs : s ∈ Icc 0 T) : ‖r s‖ ≤ (N:ℝ)^2 := by
    apply (conf s hs).2.trans
    exact mul_le_of_le_one_right (sq_nonneg _) (exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hk.le hs.1)))
  have int := intervalIntegral.integral_mono_on ht ar (intervalIntegrable_const) bound
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at int
  exact h.trans ((mul_le_mul ecap int (intervalIntegral.integral_nonneg ht (fun _ _ => norm_nonneg _))
    (by positivity)).trans_eq (by field_simp))

/-- Every normalized real eigenfunctional sees the exact population exponential
up to the nonlinear short-time error. -/
theorem eigenmode_tracking {N : ℕ} [NeZero N] (hN : 32 ≤ N) (odd : Odd N) {T : ℝ} (ht : 0 ≤ T)
    (p : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) {γ : ℝ} (hp : ‖p‖ ≤ 1) (hγ : 0 < γ)
    (eig : ∀ v, p (gramOp (sampledMatrix (N:=N) 1) v) = γ*p v)
    (z : ℝ → State (N^32)) (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt ((N^32:ℕ):ℝ)) 1 T z)
    (G : GoodInit 1 (designRadius N) (designTolerance N) (sampledMatrix 1) (fun _ : Fin N => CircleSpectrum.k0 1) (z 0))
    (init : ‖gridR N (z 0)‖ ≤ (N:ℝ)^2) (nz : ∀ j, 0 < length (z 0) j) :
    |p (gridR N (z T))-exp (-(γ*T))*p (gridR N (z 0))| ≤ 66*T/(N:ℝ)^5 := by
  let a := residual (circleInput N) (circleLabel N) (1/sqrt ((N^32:ℕ):ℝ)) (z 0)
  let f := CircleSpectralPathLength.referencePath 1 a
  have f0 : f 0 = gridR N (z 0) := CircleSpectralPathLength.referencePath_zero 1 a
  have e := frozen_mode f (gramOp (sampledMatrix (N:=N) 1)) p ht hγ
    (CircleSpectralPathLength.referencePath_deriv 1 (by norm_num) (by norm_num) a) eig
  rw [f0] at e
  rw [← e,←map_sub,←Real.norm_eq_abs]
  exact (p.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hp).trans
    (residual_frozen hN odd ht z F G init nz))

/-- A fit before or at either logarithmic cap forces the fourth-mode
projection of the original seed to lie in a 1/N interval around zero. The
same Borel event works at every real time up through the larger cap. -/
theorem short_fit_forces_fourth :
    ∀ᶠ N : ℕ in atTop, ∀ (hn : 0 < N) (_odd : Odd N),
      let : NeZero N := ⟨hn.ne'⟩
      ∃ G : Set (Seed (N^32)), MeasurableSet G ∧
        (seedLaw (N^32)).real Gᶜ ≤ 12/(N:ℝ)^2 ∧
        ∀ ω ∈ G, ∀ T : ℝ, 0 ≤ T → T ≤ (CircleKernelGD.medium (N:ℝ) : ℝ) →
          ∀ z : ℝ → State (N^32), z 0 = ω →
            IsFlow (circleInput N) (circleLabel N) (1/sqrt ((N^32:ℕ):ℝ)) 1 T z →
            ‖gridR N (z T)‖ ≤ 1/(N:ℝ)^3 →
            |(CircleResidualSpectrum.initialCoeff N (N^32) (4:ZMod N) ω).re| ≤ 1/(N:ℝ) := by
  filter_upwards [eventually_ge_atTop 36864,CircleFourthEigen.fourth_eigen_lt] with N hN eigcap hn odd
  let : NeZero N := ⟨hn.ne'⟩
  let μ := seedLaw (N^32)
  let Z := {ω : Seed (N^32) | ¬ ∀ j, 0 < length ω j}
  obtain ⟨G,_,pg,good⟩ := CircleDiscreteMoments.design_event N 2 hN (by omega)
  have zz : μ.real Z = 0 := by
    rw [measureReal_def,(ae_iff.mp (CircleInitializationConcentration.length_pos_ae (N^32)) : μ Z = 0)]
    simp
  let B := Gᶜ ∪ Z
  refine ⟨(toMeasurable μ B)ᶜ,(measurableSet_toMeasurable μ B).compl,?_,?_⟩
  · change μ.real ((toMeasurable μ B)ᶜ)ᶜ ≤ _
    rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    exact (measureReal_union_le (μ:=μ) Gᶜ Z).trans (by rw [zz,add_zero];exact pg)
  · intro ω hg T ht htime z start F fit
    have notbad : ω∉B := fun h => hg (subset_toMeasurable μ B h)
    have both : ω∈G ∧ ω∉Z := by simpa only [B,mem_union,not_or,mem_compl_iff,not_not] using notbad
    obtain ⟨g,_,r⟩ := good ω both.1
    have nz : ∀ j, 0 < length ω j := not_not.mp both.2
    let γ := CircleSpectralPathLength.eigen 1 (4:ZMod N)
    let p := CircleFourthEigen.fourthRow N
    have np : 0 < (N:ℝ) := Nat.cast_pos.mpr hn
    have high : 36864 ≤ (N:ℝ) := by exact_mod_cast hN
    have γpos : 0 < γ := (by positivity : 0 < 1/(π*(N:ℝ))^2).trans_le
      (tangent_gap (by omega) odd 1 (by norm_num) (by norm_num) 4)
    have cg : γ < 1/100 := eigcap
    have pc : ‖p‖ ≤ 1 := CircleFourthEigen.fourthRow_contract
    subst ω
    have track := eigenmode_tracking (by omega) odd ht p pc γpos (CircleFourthEigen.fourthRow_gram 1 (by norm_num) (by norm_num)) z F g r nz
    have logpos : 1 ≤ log N := by
      exact (by linarith [Real.log_three_gt_d9] : 1≤log 3).trans (log_le_log (by norm_num) (by linarith))
    have time : T ≤ 60*log N+1 := htime.trans
      (Nat.ceil_lt_add_one (by linarith : 0 ≤ 60*log N)).le
    have lsurv : γ*T ≤ log N := by
      have h := mul_le_mul cg.le time ht (by norm_num : (0:ℝ)≤1/100)
      linarith
    have inv : 1/(N:ℝ) ≤ exp (-(γ*T)) := by
      rw [exp_neg,one_div]
      exact inv_anti₀ (exp_pos _) ((exp_le_exp.mpr lsurv).trans_eq (exp_log np))
    have tf : T ≤ 61*N := by linarith [log_le_self np.le]
    have price : 66*T/(N:ℝ)^5 ≤ 4026/(N:ℝ)^4 := by
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left tf (by norm_num : (0:ℝ) ≤ 66)) (by positivity : 0≤(N:ℝ)^5)).trans_eq
      field_simp
      norm_num
    have final : |p (gridR N (z T))| ≤ 1/(N:ℝ)^3 := (p.le_opNorm _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) pc).trans fit)
    let A := p (gridR N (z 0))
    have aa : (1/(N:ℝ))*|A| ≤ 1/(N:ℝ)^3 + 4026/(N:ℝ)^4 := by
      apply (mul_le_mul_of_nonneg_right inv (abs_nonneg _)).trans
      rw [←abs_of_pos (exp_pos (-(γ*T))),←abs_mul]
      have err := (abs_sub _ _).trans (add_le_add final (track.trans price))
      dsimp only [A]
      rw [show exp (-(γ*T))*p (gridR N (z 0))=p (gridR N (z T))-(p (gridR N (z T))-exp (-(γ*T))*p (gridR N (z 0))) by ring]
      exact err
    have shrink : 1/(N:ℝ)^3+4026/(N:ℝ)^4 ≤ (1/(N:ℝ))*(1/(N:ℝ)) := by
      field_simp
      nlinarith [mul_nonneg (sub_nonneg.mpr high) np.le]
    have force : |A| ≤ 1/(N:ℝ) := le_of_mul_le_mul_left (aa.trans shrink) (by positivity)
    change |CircleFourthEigen.fourthRow N (rmsCoordinates (CircleSpectralPathLength.rawResidual N (N^32) (z 0)))| ≤ _ at force
    rwa [CircleFourthEigen.fourthRow_rms,CircleSpectralPathLength.normalizedCoeff_raw] at force

end CircleShortFlowProjection
