module

public import CircleGaussianBernstein
import all CircleGaussianBernstein
import all CircleInitializationConcentration
import all CircleTangentDrift
import all CircleGaussianMargin
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-! Simultaneous weighted activation margins at every allowable radius,
including a radius chosen after observing the initialization. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology
namespace CircleUniformMargins
open CircleEscapeBridge CircleInitializationConcentration CircleTangentDrift CircleFlowPath
private theorem energy_eq (z : Atom) : CircleGaussianBernstein.energy z = atomEnergy z := by
  simp [CircleGaussianBernstein.energy,atomEnergy,Fin.sum_univ_three]
private theorem expEnergy : Integrable (fun z => exp (atomEnergy z/8)) atomLaw ∧
    (∫ z, exp (atomEnergy z/8) ∂atomLaw) ≤ 2 := by
  have h := CircleGaussianBernstein.energy_mgf
  simp_rw [energy_eq] at h
  constructor
  · by_contra hi
    rw [integral_undef hi] at h
    exact (ne_of_gt (pow_pos (sqrt_pos.mpr (by norm_num : (0:ℝ)<4/3)) 3)) h.symm
  · rw [h]
    have sqr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4/3)
    have ub : sqrt (4/3:ℝ) ≤ 5/4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ub (sq_nonneg (sqrt (4/3:ℝ)))]

private def partialExp (n : ℕ) (s : ℝ) := ∑ k ∈ Finset.range n, (s/8)^k / k.factorial

private theorem partial_limit (A : Set Atom) :
    Tendsto (fun n => ∫ z in A, partialExp n (atomEnergy z) ∂atomLaw) atTop
      (𝓝 (∫ z in A, exp (atomEnergy z/8) ∂atomLaw)) := by
  refine tendsto_integral_of_dominated_convergence _ ?_ expEnergy.1.restrict ?_ ?_
  · intro n
    unfold partialExp atomEnergy
    fun_prop
  · intro n
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ partialExp n (atomEnergy z) from
      Finset.sum_nonneg fun k _ => div_nonneg (pow_nonneg (by linarith [atomEnergy_nonneg z]) _) (by positivity))]
    exact Real.sum_le_exp_of_nonneg (by linarith [atomEnergy_nonneg z]) n
  · filter_upwards with z
    have h := (NormedSpace.expSeries_div_hasSum_exp (atomEnergy z/8)).tendsto_sum_nat
    simpa only [partialExp,← Real.exp_eq_exp_ℝ] using h

/-- Under a fixed directional margin the distribution of the squared Gaussian
length, exponentially reweighted at 1/8, still assigns the band mass ρ. -/
theorem marked_exp (ρ : ℝ) (hρ : 0 ≤ ρ) (hu : ρ ≤ 1) (x : ℝ × ℝ) (hx : x.1^2+x.2^2=1) :
    (∫ z, exp (marginAtom ρ x z/8) ∂atomLaw) =
      1 + ρ*((∫ z, exp (atomEnergy z/8) ∂atomLaw)-1) := by
  let A : Set Atom := {z | |x.1*z 1+x.2*z 2| ≤ ρ*sqrt (atomEnergy z)}
  have meas : MeasurableSet A := by dsimp [A,atomEnergy]; apply measurableSet_le <;> fun_prop
  have moment (k : ℕ) : (∫ z in A, atomEnergy z^k ∂atomLaw) = ρ*∫ z, atomEnergy z^k ∂atomLaw := by
    rw [← integral_indicator meas]
    have h := marked_energy ρ k hρ hu x hx
    simpa only [CircleGaussianMargin.mark,A,indicator,mem_ofPred_eq] using h
  have part (n : ℕ) : (∫ z in A, partialExp n (atomEnergy z) ∂atomLaw) =
      ρ*(∫ z, partialExp n (atomEnergy z) ∂atomLaw) := by
    have eq (k : ℕ) (z : Atom) : (atomEnergy z/8)^k/k.factorial =
        ((8:ℝ)^k * k.factorial)⁻¹ * (atomEnergy z)^k := by rw [div_pow]; ring
    simp only [partialExp,eq]
    rw [integral_finsetSum _ (fun k _ => ((energy_pow_integrable k).const_mul _).restrict),
      integral_finsetSum _ (fun k _ => (energy_pow_integrable k).const_mul _),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul,integral_const_mul,moment]
    ring
  have full := partial_limit (univ : Set Atom)
  simp only [Measure.restrict_univ] at full
  have band := tendsto_nhds_unique (partial_limit A) ((full.const_mul ρ).congr fun i => (part i).symm)
  have zero := moment 0
  simp only [pow_zero, integral_const, smul_eq_mul, mul_one, probReal_univ,measureReal_restrict_apply_univ]
    at zero
  have e (z : Atom) : exp (marginAtom ρ x z/8) =
      1 + A.indicator (fun p => exp (atomEnergy p/8)-1) z := by
    by_cases hz : z ∈ A
    · rw [indicator_of_mem hz]
      change |x.1*z 1+x.2*z 2| ≤ ρ*sqrt (atomEnergy z) at hz
      simp [marginAtom,hz]
    · rw [indicator_of_notMem hz]
      change ¬ |x.1*z 1+x.2*z 2| ≤ ρ*sqrt (atomEnergy z) at hz
      simp [marginAtom,hz]
  simp_rw [e]
  have hi : Integrable (fun z => exp (atomEnergy z/8)-1) atomLaw := expEnergy.1.sub (integrable_const 1)
  rw [integral_add (integrable_const 1) (hi.indicator meas),
    integral_const,integral_indicator meas,integral_sub expEnergy.1.restrict (integrable_const 1),
    integral_const,band]
  simp [zero]
  ring

private theorem exp_margin_cap (ρ : ℝ) (x : ℝ × ℝ) (z : Atom) :
    exp (marginAtom ρ x z/8) ≤ exp (atomEnergy z/8) := by
  apply exp_le_exp.mpr
  linarith [margin_cap ρ x z,le_abs_self (marginAtom ρ x z)]

private theorem angular_mgf (ρ : ℝ) (hρ : 0 ≤ ρ) (hu : ρ ≤ 1) :
    (∫ z, exp ((∫ t, marginAtom ρ (phase t) z ∂angularLaw)/8) ∂atomLaw) ≤ exp ρ := by
  let M (t : ℝ) (z : Atom) := marginAtom ρ (phase t) z
  let V (p : ℝ × Atom) := exp (M p.1 p.2 / 8)
  have meas : Measurable V := ((angle_margin_meas ρ).div_const 8).exp
  have prodI : Integrable V (angularLaw.prod atomLaw) := (expEnergy.1.comp_snd angularLaw).mono'
    meas.aestronglyMeasurable (ae_of_all _ fun p => by
      change |exp (_/8)| ≤ exp (_/8)
      rw [abs_of_pos (exp_pos _)]
      exact exp_margin_cap ..)
  have avgE := integral_prod_symm V prodI
  rw [integral_prod _ prodI] at avgE
  have hM (z : Atom) : Integrable (fun t => M t z) angularLaw := by
    apply (integrable_const (atomEnergy z)).mono'
      ((angle_margin_meas ρ).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ fun t => margin_cap .. 
  have mJ (z : Atom) : exp ((∫ t, M t z ∂angularLaw)/8) ≤ ∫ t, V (t,z) ∂angularLaw := by
    have hv : Integrable (fun t => exp (M t z/8)) angularLaw :=
      (integrable_const (exp (atomEnergy z/8))).mono'
        (meas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (ae_of_all _ fun t => by simpa [abs_of_pos (exp_pos _)] using exp_margin_cap ρ (phase t) z)
    rw [← integral_div]
    exact convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _ => trivial)
      ((hM z).div_const 8) hv
  have i1 : Integrable (fun z => exp ((∫ t, M t z ∂angularLaw)/8)) atomLaw := by
    apply expEnergy.1.mono' ((angle_test_meas (angle_margin_meas ρ)).div_const 8).exp.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have h := angle_cap (k:=1) (fun t a => by simpa using margin_cap ρ (phase t) a) z
    have w := (le_abs_self _).trans h
    change (∫ t, M t z ∂angularLaw)/8 ≤ atomEnergy z/8
    linarith
  apply (integral_mono i1 prodI.integral_prod_right mJ).trans
  rw [← avgE]
  have eq (t : ℝ) : (∫ z, V (t,z) ∂atomLaw) = 1+ρ*((∫ z, exp (atomEnergy z/8) ∂atomLaw)-1) :=
    marked_exp ρ hρ hu (phase t) (Real.cos_sq_add_sin_sq _)
  simp_rw [eq]
  simp only [integral_const,probReal_univ,one_smul]
  linarith [mul_le_mul_of_nonneg_left expEnergy.2 hρ,add_one_le_exp ρ]

def test {N : ℕ} (ρ : ℝ) (j : Option (Fin N)) (z : Atom) : ℝ :=
  match j with
  | none => ∫ t, marginAtom ρ (phase t) z ∂angularLaw
  | some j => marginAtom ρ (circleInput N j) z

private theorem test_meas {N : ℕ} (ρ : ℝ) (j : Option (Fin N)) : Measurable (test ρ j) := by
  cases j with
  | none => exact angle_test_meas (angle_margin_meas ρ)
  | some j => exact margin_meas _ measurable_const measurable_id

private theorem test_cap {N : ℕ} (ρ : ℝ) (j : Option (Fin N)) (z : Atom) : test ρ j z ≤ atomEnergy z := by
  cases j with
  | none =>
    have h := angle_cap (k:=1) (fun t a => by simpa using margin_cap ρ (phase t) a) z
    simpa [test] using (le_abs_self _).trans h
  | some j => exact (le_abs_self _).trans (margin_cap ..)

theorem fixed_radius {N m : ℕ} (hm : 0 < m) (j : Option (Fin N)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hu : ρ ≤ 1) : (seedLaw m).real {ω | 16*ρ ≤ sampleAverage (test ρ j) ω} ≤ exp (-(m:ℝ)*ρ) := by
  have mg : mgf (test ρ j) atomLaw (1/8) ≤ exp ρ := by
    simp only [mgf,one_div_mul_eq_div]
    cases j with
    | none => exact angular_mgf ρ hρ hu
    | some j =>
      change (∫ z, exp (marginAtom ρ (circleInput N j) z/8) ∂atomLaw) ≤ exp ρ
      rw [marked_exp ρ hρ hu _ (unit_grid_eq j)]
      linarith [mul_le_mul_of_nonneg_left expEnergy.2 hρ,add_one_le_exp ρ]
  have hi : Integrable (fun z => exp ((1/8:ℝ)*test ρ j z)) atomLaw := by
    apply expEnergy.1.mono' ((test_meas ρ j).const_mul _).exp.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    linarith [test_cap ρ j z]
  exact (CircleGaussianBernstein.empirical_chernoff hm _ (test_meas ρ j)
    (u:=16*ρ) (by norm_num : 0 ≤ (1/8:ℝ)) hi mg).trans_eq (by ring_nf)

private def radius {K : ℕ} (i : Fin K) : ℝ := ((i:ℕ)+1:ℝ)/K

/-- Measurable event imposing simultaneous tests at a finite mesh of radii.
Interpolation in the radius is deterministic, uniformly for every seed. -/
def marginMesh (N m K : ℕ) : Set (Seed m) :=
  {ω | ∀ i : Fin K, ∀ j : Option (Fin N), sampleAverage (test (radius i) j) ω < 16*radius i}

theorem measurable_marginMesh (N m K : ℕ) : MeasurableSet (marginMesh N m K) := by
  simp only [marginMesh,ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    measurableSet_lt (sampleAverage_meas (test_meas (radius i) j)) measurable_const

theorem mesh_failure (N m K : ℕ) (hm : 0 < m) (hK : 0 < K) :
    (seedLaw m).real (marginMesh N m K)ᶜ ≤ K*(N+1:ℝ)*exp (-(m:ℝ)/K) := by
  let bad (p : Fin K × Option (Fin N)) := {ω : Seed m | 16*radius p.1 ≤ sampleAverage (test (radius p.1) p.2) ω}
  have kr : 0 < (K:ℝ) := by exact_mod_cast hK
  have prob (p : Fin K × Option (Fin N)) : (seedLaw m).real (bad p) ≤ exp (-(m:ℝ)/K) := by
    have hn : (p.1.val:ℝ)+1 ≤ K := by exact_mod_cast p.1.isLt
    have r0 : 0 ≤ radius p.1 := by dsimp [radius]; positivity
    have r1 : radius p.1 ≤ 1 := (div_le_one kr).mpr hn
    apply (fixed_radius hm p.2 _ r0 r1).trans
    apply exp_le_exp.mpr
    have hlow : 1/(K:ℝ) ≤ radius p.1 := by
      dsimp [radius]; apply div_le_div_of_nonneg_right _ kr.le
      linarith [Nat.cast_nonneg p.1.val (α:=ℝ)]
    have h := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg m)
    simpa only [div_eq_mul_inv,one_mul,neg_mul] using neg_le_neg h
  have sub : (marginMesh N m K)ᶜ ⊆ ⋃ (q : Fin K × Option (Fin N)), bad q := by
    intro ω h
    by_contra h'
    apply h
    intro i j
    exact lt_of_not_ge (fun hx => h' (mem_iUnion_of_mem (i,j) hx))
  refine (measureReal_mono sub).trans ((measureReal_iUnion_fintype_le bad).trans
    ((Finset.sum_le_sum (fun i _ => prob i)).trans_eq ?_))
  simp [Fintype.card_option]

private theorem test_mono {N : ℕ} {ρ r : ℝ} (h : ρ ≤ r) (j : Option (Fin N)) (z : Atom) :
    test ρ j z ≤ test r j z := by
  have point (x : ℝ × ℝ) : marginAtom ρ x z ≤ marginAtom r x z := by
    unfold marginAtom
    split_ifs with p q
    all_goals first | exact le_rfl | exact atomEnergy_nonneg z |
      exact (q (p.trans (mul_le_mul_of_nonneg_right h (sqrt_nonneg _)))).elim
  cases j with
  | some j => exact point _
  | none =>
    have int (t : ℝ) : Integrable (fun u => marginAtom t (phase u) z) angularLaw :=
      (integrable_const (atomEnergy z)).mono'
        ((angle_margin_meas t).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (ae_of_all _ fun u => margin_cap ..)
    exact integral_mono (int _) (int _) fun u => point _

theorem uniform_margins (N m K : ℕ) (hK : 0 < K) {ω : Seed m} (good : ω ∈ marginMesh N m K)
    (ρ : ℝ) (hρ : 1/(K:ℝ) ≤ ρ) (hρ' : ρ ≤ 1) :
    (∀ j : Fin N, marginMass ω ρ (circleInput N j) ≤ 32*ρ) ∧ angularMargin ω ρ ≤ 32*ρ := by
  have kr : (0:ℝ)<K := by exact_mod_cast hK
  have rho0 := lt_of_lt_of_le (one_div_pos.mpr kr) hρ
  let k := ⌈ρ*(K:ℝ)⌉₊
  have hkpos : 0 < k := Nat.ceil_pos.mpr (mul_pos rho0 kr)
  have hk : k ≤ K := Nat.ceil_le.mpr (by nlinarith [mul_le_mul_of_nonneg_right hρ' kr.le])
  let i : Fin K := ⟨k-1,by omega⟩
  have i1 : i.val+1=k := by dsimp [i]; omega
  have heq : radius i = (k:ℝ)/K := by dsimp [radius]; congr 1; exact_mod_cast i1
  have hlow : ρ ≤ radius i := by rw [heq]; exact (le_div_iff₀ kr).mpr (Nat.le_ceil _)
  have hhi : radius i ≤ 2*ρ := by
    rw [heq]; apply (div_le_iff₀ kr).mpr
    have r := Nat.ceil_lt_add_one (mul_nonneg rho0.le kr.le)
    change (k:ℝ) < ρ*K+1 at r
    linarith [(div_le_iff₀ kr).mp hρ]
  have each (j : Option (Fin N)) : sampleAverage (test ρ j) ω ≤ 32*ρ := by
    have mono : sampleAverage (test ρ j) ω ≤ sampleAverage (test (radius i) j) ω :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => test_mono hlow j (fun k => ω (n,k))))
        (inv_nonneg.mpr (Nat.cast_nonneg m))
    exact mono.trans ((good i j).le.trans (by linarith))
  constructor
  · intro j
    rw [margin_initial]; exact each (some j)
  · rw [angle_margin_initial]; exact each none

/-- At width N³² a single radius mesh costs at most N¹⁶(N+1)exp(−N¹⁶).
It controls all radii in [1/√m,1] for both fixed and seed-dependent choices. -/
theorem design_margins (N : ℕ) (hN : 0 < N) :
    ∃ G : Set (Seed (N^32)), MeasurableSet G ∧
      (seedLaw (N^32)).real Gᶜ ≤ (N:ℝ)^16*(N+1)*exp (-(N:ℝ)^16) ∧
      ∀ ω ∈ G, ∀ ρ : ℝ, 1/(N:ℝ)^16 ≤ ρ → ρ ≤ 1 →
        (∀ j : Fin N, marginMass ω ρ (circleInput N j) ≤ 32*ρ) ∧ angularMargin ω ρ ≤ 32*ρ := by
  refine ⟨_,measurable_marginMesh N (N^32) (N^16),?_,?_⟩
  · have h := mesh_failure N (N^32) (N^16) (by positivity) (by positivity)
    push_cast at h
    convert h using 4
    field_simp
  · intro ω h ρ lo hi
    exact uniform_margins N (N^32) (N^16) (by positivity) h ρ (by simpa using lo) hi
end CircleUniformMargins
