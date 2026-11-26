module

public import CircleInitialResidualSecond
public import CircleSignedRates
public import CircleSignedRow
public import CircleInitializationConcentration
import all CircleInitializationConcentration
import all CircleSignedRow
import all CircleSignedAngular
import all CircleFlowPath
import all CircleTangentDrift
import all CircleEscapeBridge
import all CircleGridSpectrum
import all CircleActualTracking
import Mathlib.Tactic

/-! Exact finite-sample confidence thresholds for the odd-circle learner. -/
@[expose] public section
noncomputable section
namespace CircleFiniteConfidence
open Real MeasureTheory ProbabilityTheory Set CircleEscapeBridge CircleFlowPath CircleTangentDrift
open CircleInitializationConcentration CircleGridSpectrum CircleSpectrum CircleActualTracking
set_option maxHeartbeats 1200000
open scoped InnerProductSpace
variable {N m : ℕ}

def rowScale (N : ℕ) (δ : ℝ) := sqrt (90*(N:ℝ)/δ)
def gridScale (N : ℕ) (δ : ℝ) := (N:ℝ)*sqrt (90/δ)
def signedScale (N : ℕ) (b δ : ℝ) := (6/(N:ℝ)+1-b)*rowScale N δ

structure InitialBounds (n m : ℕ) (δ A : ℝ) (z : Seed m) : Prop where
  residual : ‖gridR (n+1) z‖ ≤ sqrt (12/δ)
  energy : meanEnergy z ≤ 4
  gridMargin : ∀ i : Fin (n+1), marginMass z (A/sqrt m) (circleInput _ i) ≤ 6*(A/sqrt m)
  angular : angularMargin z (A/sqrt m) ≤ 6*(A/sqrt m)
  gram : ∀ i j : Fin (n+1), |gridGram 1 z (startGates z) i j-sampledMatrix 1 i j| ≤ gridScale (n+1) δ/sqrt m
  mean : ∀ j : Fin (n+1), |populationRow 1 z (startGates z) j-k0 1| ≤ rowScale (n+1) δ/sqrt m
  signed : ∀ j : Fin (n+1), |CircleSignedRow.mixedRow (n+1) (weight 1 n) z z (CircleEscape.gridPoint _ j)| ≤
    signedScale (n+1) (weight 1 n) δ/sqrt m

private theorem sharp_atom {x y : ℝ × ℝ} (hx : UnitInput x) (hy : UnitInput y) (z : Atom) :
    |weightedAtom 1 x y z| ≤ atomEnergy z := by
  let X : ℂ := ⟨x.1,x.2⟩
  let Y : ℂ := ⟨y.1,y.2⟩
  have unit (u : ℝ × ℝ) (h : UnitInput u) : ‖(⟨u.1,u.2⟩:ℂ)‖≤1 := by
    apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [Complex.sq_norm,Complex.normSq_apply,one_pow]
    exact (by simpa only [UnitInput,sq] using h)
  have h := atom_cap X Y (unit _ hx) (unit _ hy) z
  have eq : weightedAtom 1 x y z=tangentAtom X Y z := by
    simp only [weightedAtom,tangentAtom,CircleEscape.feature,CircleEscape.gate,actualGate,
      Complex.inner,Complex.mul_re,Complex.conj_re,Complex.conj_im,X,Y,
      mul_neg,sub_neg_eq_add,one_mul,dot,sq]
    ring
  exact eq ▸ h

private def gm (i j : Fin N) := weightedAtom 1 (circleInput N i) (circleInput N j)
private def pm (j : Fin N) (z : Atom) := ∫ t, weightedAtom 1 (phase t) (circleInput N j) z ∂angularLaw
private def sm (b : ℝ) (j : Fin N) (z : Atom) := pm j z-b*((∑ i, gm i j z)/N)

private theorem gm_meas (i j : Fin N) : Measurable (gm i j) :=
  weighted_meas 1 measurable_const measurable_const measurable_id
private theorem pm_meas (j : Fin N) : Measurable (pm j) := angle_test_meas (angle_weighted_meas 1 _)
private theorem sm_meas (b : ℝ) (j : Fin N) : Measurable (sm b j) :=
  (pm_meas j).sub (measurable_const.mul ((Finset.measurable_fun_sum _ (fun i _ => gm_meas i j)).div_const _))
private theorem gm_cap (i j : Fin N) (z : Atom) : |gm i j z| ≤ 1*atomEnergy z := by
  simpa only [one_mul,gm] using sharp_atom (grid_unit i) (grid_unit j) z
private theorem pm_cap (j : Fin N) (z : Atom) : |pm j z| ≤ 1*atomEnergy z := by
  exact angle_cap (fun t q => (sharp_atom (phase_unit t) (grid_unit j) q).trans_eq (one_mul _).symm) z
private theorem gm_eq (hm : 0<m) (i j : Fin N) (z : Seed m) : gridGram 1 z (startGates z) i j = sampleAverage (gm i j) z :=
  weightedAtom_initial hm 1 _ _ _
private theorem pm_eq (hm : 0<m) (j : Fin N) (z : Seed m) : populationRow 1 z (startGates z) j = sampleAverage (pm j) z :=
  angular_entry_initial hm 1 j z
private theorem sm_eq (hm : 0<m) (b : ℝ) (j : Fin N) (z : Seed m) :
    CircleSignedRow.mixedRow N b z z (CircleEscape.gridPoint N j)=sampleAverage (sm b j) z := by
  rw [CircleSignedRow.mixedRow_eq _ _ hm]
  change populationRow 1 z (startGates z) j - b*((∑ i : Fin N, gridGram 1 z (startGates z) i j)/N)=_
  simp_rw [gm_eq hm,pm_eq hm]
  simp only [sampleAverage,sm,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_div]
  rw [Finset.sum_comm (s:=Finset.univ (α:=Fin N))]
  ring

private theorem sm_cap {b : ℝ} (hn : 3≤N) (odd : Odd N) (hb : 0≤b) (hu : b≤1) (j : Fin N) (z : Atom) :
    |sm b j z| ≤ (6/(N:ℝ)+1-b)*atomEnergy z := by
  let seed : Seed 1 := fun q => z q.2
  let w : ℂ := ⟨z 1,z 2⟩
  let y := CircleEscape.gridPoint N j
  have eq := (sm_eq (by decide : 0<1) b j seed).symm
  have e : sampleAverage (sm b j) seed = sm b j z := by simp [sampleAverage,seed]
  rw [e] at eq
  rw [eq]
  have h := CircleSignedRates.summand_bound hn odd hb hu w y (z 0) (CircleEscape.grid_norm N j).le
  have swap := real_inner_comm (CircleSignedAngular.signedGate N b w) y
  rw [←swap,Complex.sq_norm,Complex.normSq_apply] at h
  simpa [CircleSignedRow.mixedRow,CircleSignedRow.mixedAtom,CircleSignedRow.unitFeature,CircleSignedRow.unitGate,
    CircleSignedRow.hiddenWeight,initial,w,seed,atomEnergy,sq,add_assoc] using h

private theorem sm_zero (n : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (j : Fin (n+1)) :
    ∫ z, sm (weight 1 n) j z ∂atomLaw = 0 := by
  let N := n+1
  let b := weight 1 n
  have p := (energy_dominated (pm_meas j) (pm_cap j)).1.integrable (by norm_num)
  have g (i : Fin N) := (energy_dominated (gm_meas i j) (gm_cap i j)).1.integrable (by norm_num)
  have hgf : (∫ z, (∑ i, gm i j z)/N ∂atomLaw)=(∑ i : Fin N, sampledMatrix 1 i j)/N := by
    rw [integral_div,integral_finsetSum _ (fun i _ => g i)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (congrFun (populationGram_sampled (N:=N) 1) i) j
  have hi := (integrable_finsetSum Finset.univ (fun (i : Fin N) _ => g i)).div_const (N:ℝ)
  have pp : (∫ z, pm j z ∂atomLaw)=k0 1 := populationMeanRow_constant 1 j
  change (∫ z, pm j z-b*((∑ i, gm i j z)/N) ∂atomLaw)=0
  rw [integral_sub p (hi.const_mul b),integral_const_mul,hgf,pp, sampled_column 1 (by norm_num) (by norm_num)]
  have ng := tangent_gap hn odd 1 (by norm_num) (by norm_num) (0:ZMod N)
  have nz : aliasValue (tangentCoeff 1) (0:ZMod N) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) ng)
  dsimp only [b]
  rw [weight_from_grid_alias n hn odd 1 (by norm_num) (by norm_num)]
  field_simp
  ring


private def angularMark (ρ : ℝ) (z : Atom) := ∫ t, marginAtom ρ (phase t) z ∂angularLaw

private theorem margin_mem (ρ : ℝ) (x : ℝ × ℝ) : MemLp (marginAtom ρ x) 2 atomLaw :=
  (energy_dominated (margin_meas _ measurable_const measurable_id) (fun z => (margin_cap ρ x z).trans_eq (one_mul _).symm)).1

private theorem angular_mem (ρ : ℝ) : MemLp (angularMark ρ) 2 atomLaw :=
  (energy_dominated (angle_test_meas (angle_margin_meas ρ)) (angle_cap (fun t z => (margin_cap ρ (phase t) z).trans_eq (one_mul _).symm))).1

private theorem angular_second {ρ : ℝ} (hp : 0≤ρ) (hu : ρ≤1) : (∫ z, angularMark ρ z^2 ∂atomLaw) ≤ 15*ρ := by
  let f := fun p : ℝ × Atom => marginAtom ρ (phase p.1) p.2
  have hme : Measurable f := angle_margin_meas ρ
  have h2 : Integrable (fun p => f p^2) (angularLaw.prod atomLaw) := by
    apply ((energy_pow_integrable 2).comp_snd angularLaw).mono' (hme.pow_const 2).aestronglyMeasurable
    refine ae_of_all _ fun p => ?_
    have h := pow_le_pow_left₀ (abs_nonneg _) (margin_cap ρ (phase p.1) p.2) 2
    change |(marginAtom ρ (phase p.1) p.2)^2| ≤ atomEnergy p.2^2
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using h
  have cmp (z : Atom) : (angularMark ρ z)^2 ≤ ∫ t, f (t,z)^2 ∂angularLaw := by
    have me := hme.comp (measurable_id.prodMk (measurable_const (a:=z)))
    have hm : MemLp (fun t => f (t,z)) 2 angularLaw :=
      (memLp_const (atomEnergy z)).mono' me.aestronglyMeasurable (ae_of_all _ fun t => margin_cap ρ _ _)
    have h := variance_nonneg (fun t => f (t,z)) angularLaw
    rw [variance_eq_sub hm] at h
    exact sub_nonneg.mp h
  apply (integral_mono (angular_mem ρ).integrable_sq h2.integral_prod_right cmp).trans
  rw [(integral_integral_swap h2).symm]
  have a (t : ℝ) : (∫ z, f (t,z)^2 ∂atomLaw)=15*ρ := (margin_moments ρ hp hu (phase t) (Real.cos_sq_add_sin_sq (2*π*t))).2
  simp_rw [a];simp

private theorem margin_failure (N m : ℕ) (hm : 0<m) {ρ : ℝ} (hp : 0<ρ) (hu : ρ≤1) :
    (seedLaw m).real {z | ¬((∀ i : Fin N, marginMass z ρ (circleInput N i)≤6*ρ) ∧ angularMargin z ρ≤6*ρ)} ≤
      5*((N:ℝ)+1)/(3*m*ρ) := by
  let f : Option (Fin N) → Atom → ℝ
    | none => angularMark ρ
    | some i => marginAtom ρ (circleInput N i)
  have info (q : Option (Fin N)) : MemLp (f q) 2 atomLaw ∧ (∫ z, f q z ∂atomLaw)=3*ρ ∧ (∫ z, f q z^2 ∂atomLaw) ≤ 15*ρ := by
    cases q with
    | none => exact ⟨angular_mem _,avg_angular_margin_mean _ hp.le hu,angular_second hp.le hu⟩
    | some i =>
      have h := margin_moments ρ hp.le hu _ (unit_grid_eq i)
      exact ⟨margin_mem _ _,h.1,h.2.le⟩
  let bad := fun q : Option (Fin N) => {z : Seed m | 3*ρ ≤ |sampleAverage (f q) z-3*ρ|}
  have sub : {z : Seed m | ¬((∀ i : Fin N, marginMass z ρ (circleInput N i)≤6*ρ) ∧ angularMargin z ρ≤6*ρ)} ⊆ ⋃q, bad q := by
    intro z h
    by_contra no
    have cap (q : Option (Fin N)) : sampleAverage (f q) z≤6*ρ := by
      have ht : ¬ 3*ρ ≤ |sampleAverage (f q) z-3*ρ| := fun k => no (mem_iUnion_of_mem q k)
      linarith [(le_abs_self _).trans_lt (lt_of_not_ge ht)]
    apply h
    constructor
    · intro i;rw [margin_initial];exact cap (some i)
    · rw [angle_margin_initial];exact cap none
  have tail (q : Option (Fin N)) : (seedLaw m).real (bad q) ≤ 5/(3*m*ρ) := by
    have h := average_concentration hm (info q).1 ((variance_le_expectation_sq (info q).1.aestronglyMeasurable).trans (info q).2.2)
      (show 0<3*ρ by positivity)
    rw [(info q).2.1] at h
    exact h.trans_eq (by field_simp;ring)
  refine (measureReal_mono sub).trans ((measureReal_iUnion_fintype_le bad).trans
    ((Finset.sum_le_sum (fun q _ => tail q)).trans_eq ?_))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_option,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

private theorem family_failure {ι : Type*} [Fintype ι] [Nonempty ι] (hm : 0<m) (f : ι → Atom → ℝ)
    (B : ι → Seed m → ℝ) {k δ U : ℝ} (hk : 0<k) (hδ : 0<δ) (hU : 0<U)
    (scale : U^2 = k^2*90*(Fintype.card ι:ℝ)/(δ*m))
    (meas : ∀ i, Measurable (f i)) (cap : ∀ i z, |f i z|≤k*atomEnergy z)
    (rep : ∀ i z, B i z=sampleAverage (f i) z - ∫ a, f i a ∂atomLaw) :
    (seedLaw m).real {z | ¬∀ i, |B i z|≤U} ≤ δ/6 := by
  let D := (Fintype.card ι:ℝ)
  have dp : 0<D := Nat.cast_pos.mpr Fintype.card_pos
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  let bad := fun i => {z : Seed m | U≤|B i z|}
  have sub : {z : Seed m | ¬∀ i, |B i z|≤U} ⊆ ⋃i, bad i := by
    intro z h
    push Not at h
    obtain ⟨i,hi⟩ := h
    exact mem_iUnion_of_mem i hi.le
  have tail (i : ι) : (seedLaw m).real (bad i)≤δ/(6*D) := by
    obtain ⟨mem,vc⟩ := energy_dominated (meas i) (cap i)
    change (seedLaw m).real {z | U≤|B i z|}≤_
    simp_rw [rep]
    apply (average_concentration hm mem vc hU).trans_eq
    rw [scale]
    dsimp only [D]
    field_simp
    ring
  refine (measureReal_mono sub).trans ((measureReal_iUnion_fintype_le bad).trans
    ((Finset.sum_le_sum (fun i _ => tail i)).trans_eq ?_))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change D*(δ/(6*D))=δ/6
  field_simp

private theorem grid_failure (N m : ℕ) [NeZero N] (hm : 0<m) {δ : ℝ} (hδ : 0<δ) :
    (seedLaw m).real {z | ¬∀ i j : Fin N, |gridGram 1 z (startGates z) i j-sampledMatrix 1 i j|≤gridScale N δ/sqrt m} ≤δ/6 := by
  let B := fun (q : Fin N × Fin N) (z : Seed m) => gridGram 1 z (startGates z) q.1 q.2-sampledMatrix 1 q.1 q.2
  let U := gridScale N δ/sqrt m
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have hU : 0<U := by dsimp [U,gridScale];positivity
  have scale : U^2=1^2*90*(Fintype.card (Fin N × Fin N):ℝ)/(δ*m) := by
    simp only [U,gridScale,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,div_pow,mul_pow,sq_sqrt (by positivity : 0≤90/δ),sq_sqrt mp.le]
    ring
  have h := family_failure (ι:=Fin N × Fin N) hm (fun q => gm q.1 q.2) B (by norm_num : 0<(1:ℝ)) hδ hU scale
    (fun q => gm_meas q.1 q.2) (fun q => gm_cap q.1 q.2) (fun q z => by
      dsimp only [B]; rw [gm_eq hm]
      have ct : (∫ a, gm q.1 q.2 a ∂atomLaw)=sampledMatrix 1 q.1 q.2 := congrFun (congrFun (populationGram_sampled (N:=N) 1) q.1) q.2
      rw [ct])
  have eq : {z : Seed m | ¬∀ i j : Fin N, |gridGram 1 z (startGates z) i j-sampledMatrix 1 i j| ≤gridScale N δ/sqrt m} =
      {z | ¬∀ q, |B q z|≤U} := by ext z;simp only [Prod.forall,B,U,mem_ofPred_eq]
  rw [eq];exact h

private theorem row_failure (N m : ℕ) [NeZero N] (hm : 0<m) {δ : ℝ} (hδ : 0<δ) :
    (seedLaw m).real {z | ¬∀ j : Fin N, |populationRow 1 z (startGates z) j-k0 1|≤rowScale N δ/sqrt m} ≤δ/6 := by
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  apply family_failure hm pm _ (by norm_num : 0<(1:ℝ)) hδ (by unfold rowScale;positivity) _ pm_meas pm_cap
  · intro j z;rw [pm_eq hm]
    exact congrArg (_-·) (populationMeanRow_constant (N:=N) 1 j).symm
  · simp only [rowScale,Fintype.card_fin,div_pow,sq_sqrt (by positivity : 0≤90*(N:ℝ)/δ),sq_sqrt mp.le]
    ring

private theorem signed_failure (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m) {δ : ℝ} (hδ : 0<δ) :
    let N := n+1; let b := weight 1 n
    (seedLaw m).real {z | ¬∀ j : Fin N, |CircleSignedRow.mixedRow N b z z (CircleEscape.gridPoint N j)|≤signedScale N b δ/sqrt m} ≤δ/6 := by
  intro N b
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have wb := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  have dp : 0<6/(N:ℝ)+1-b := by dsimp only [b];linarith [show 0<6/(N:ℝ) by positivity]
  apply family_failure hm (sm b) _ dp hδ (by unfold signedScale rowScale;positivity) _ (sm_meas b)
    (fun i => sm_cap hn odd wb.1 wb.2 i)
  · intro j z;rw [sm_eq hm,sm_zero n hn odd,sub_zero]
  · simp only [signedScale,rowScale,Fintype.card_fin,div_pow,mul_pow,sq_sqrt (by positivity : 0≤90*(N:ℝ)/δ),sq_sqrt mp.le]
    ring

private theorem energy_failure (m : ℕ) (hm : 0<m) {δ : ℝ} (hδ : 0<δ) (size : 36/δ≤m) :
    (seedLaw m).real {z | ¬meanEnergy z≤4}≤δ/6 := by
  have rep (z : Seed m) : meanEnergy z=sampleAverage atomEnergy z := by
    rw [meanEnergy,sampleAverage,←div_eq_inv_mul];simp_rw [length_sq];rfl
  have h := average_concentration hm (energy_mem 2) atomEnergy_variance.le (by norm_num : (0:ℝ)<1)
  rw [atomEnergy_mean] at h
  refine (measureReal_mono (s₂:={z : Seed m | 1≤|sampleAverage atomEnergy z-3|}) (fun ⦃z⦄ hz => ?_)).trans (h.trans ?_)
  · change ¬meanEnergy z≤4 at hz
    rw [rep] at hz
    exact (by linarith : 1≤sampleAverage atomEnergy z-3).trans (le_abs_self _)
  · have a := (div_le_iff₀ hδ).mp size
    rw [one_pow,mul_one,div_le_div_iff₀ (Nat.cast_pos.mpr hm) (by norm_num)];linarith


/-- The six estimates in the finite-width theorem hold on a single
measurable event under the unconditioned Gaussian initialization. -/
theorem six_tests (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m) (δ A : ℝ)
    (hδ : 0<δ) (_hδ1 : δ<1) (hA : 0<A) (hr : A/sqrt m≤1) (energy : 36/δ≤m)
    (margin : 10*((n+1:ℕ)+1:ℕ)/(δ*A)≤sqrt m) :
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ ≤ δ ∧ ∀ z∈E, InitialBounds n m δ A z := by
  let N := n+1
  let b := weight 1 n
  let ρ := A/sqrt m
  let P := seedLaw m
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have sq : (sqrt m)^2 = (m:ℝ) := sq_sqrt mp.le
  have rp : 0<ρ := div_pos hA (sqrt_pos.mpr mp)
  let B : Fin 6 → Set (Seed m) := ![
    {z | sqrt (12/δ)< ‖gridR N z‖},
    {z | ¬ ∀ i j : Fin N, |gridGram 1 z (startGates z) i j-sampledMatrix 1 i j|≤gridScale N δ/sqrt m},
    {z | ¬ ∀ j : Fin N, |populationRow 1 z (startGates z) j-k0 1|≤rowScale N δ/sqrt m},
    {z | ¬ ∀ j : Fin N, |CircleSignedRow.mixedRow N b z z (CircleEscape.gridPoint N j)|≤signedScale N b δ/sqrt m},
    {z | ¬ meanEnergy z≤4},
    {z | ¬ ((∀ i : Fin N, marginMass z ρ (circleInput N i)≤6*ρ) ∧ angularMargin z ρ≤6*ρ)}]
  have each (i : Fin 6) : P.real (B i) ≤ δ/6 := by
    fin_cases i
    · have a := CircleInitialResidualSecond.residual_tail hn odd hm (show 0<sqrt (12/δ) by positivity)
      apply a.trans_eq
      rw [sq_sqrt (by positivity : 0≤12/δ)]; field_simp
      ring
    · exact grid_failure N m hm hδ
    · exact row_failure N m hm hδ
    · exact signed_failure n m hn odd hm hδ
    · exact energy_failure m hm hδ energy
    · apply (margin_failure N m hm rp hr).trans
      have a := (div_le_iff₀ (mul_pos hδ hA)).mp margin
      push_cast at a
      have w : (m:ℝ)*ρ=A*sqrt m := by
        dsimp only [ρ]; field_simp; nlinarith [sq]
      apply (div_le_div_iff₀ (by positivity : 0<3*(m:ℝ)*ρ) (by norm_num)).mpr
      rw [mul_assoc (3:ℝ),w]
      dsimp only [N]
      push_cast
      linarith
  let F := ⋃ i, B i
  have bad : P.real F≤δ := (measureReal_iUnion_fintype_le B).trans ((Finset.sum_le_sum (fun i _ => each i)).trans_eq (by simp;ring))
  refine ⟨(toMeasurable P F)ᶜ,(measurableSet_toMeasurable _ _).compl,?_,?_⟩
  · change P.real ((toMeasurable P F)ᶜ)ᶜ≤δ
    rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    exact bad
  · intro z hz
    have no (i : Fin 6) : z∉B i := fun hh => hz (subset_toMeasurable P F (mem_iUnion_of_mem i hh))
    have margins : (∀ i : Fin N, marginMass z ρ (circleInput N i)≤6*ρ) ∧ angularMargin z ρ≤6*ρ := not_not.mp (no 5)
    exact ⟨le_of_not_gt (no 0),not_not.mp (no 4),margins.1,margins.2,not_not.mp (no 1),not_not.mp (no 2),not_not.mp (no 3)⟩

end CircleFiniteConfidence
