module

public import CircleFiniteConfidence
public import CirclePositiveSpectrum
import all CircleFiniteConfidence
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
namespace CirclePositiveConfidence
open Real MeasureTheory ProbabilityTheory Set CircleEscapeBridge CircleFlowPath CircleTangentDrift
open CircleInitializationConcentration CircleGridSpectrum CircleSpectrum CircleActualTracking
open CircleFiniteConfidence
set_option maxHeartbeats 1200000
open scoped InnerProductSpace
variable {N m : ℕ}


def mult (τ : ℝ) := max 1 τ
private theorem mp (τ : ℝ) : 0 < mult τ := zero_lt_one.trans_le (le_max_left ..)

def signedInitial [NeZero N] (τ b : ℝ) (z : Seed m) (j : Fin N) :=
  populationRow τ z (startGates z) j - b*((∑ i, gridGram τ z (startGates z) i j)/N)

structure InitialBounds (n m : ℕ) (τ δ A : ℝ) (z : Seed m) : Prop where
  residual : ‖gridR (n+1) z‖ ≤ sqrt (12/δ)
  energy : meanEnergy z ≤ 4
  gridMargin : ∀ i : Fin (n+1), marginMass z (A/sqrt m) (circleInput _ i) ≤ 6*(A/sqrt m)
  angular : angularMargin z (A/sqrt m) ≤ 6*(A/sqrt m)
  gram : ∀ i j : Fin (n+1), |gridGram τ z (startGates z) i j-sampledMatrix τ i j| ≤ mult τ*gridScale (n+1) δ/sqrt m
  mean : ∀ j : Fin (n+1), |populationRow τ z (startGates z) j-k0 τ| ≤ mult τ*rowScale (n+1) δ/sqrt m
  signed : ∀ j : Fin (n+1), |signedInitial τ (weight τ n) z j| ≤ mult τ*signedScale (n+1) (weight τ n) δ/sqrt m

private def tilt (τ : ℝ) (z : Atom) : Atom := ![sqrt τ*z 0,z 1,z 2]

private theorem atom_tilt (τ : ℝ) (ht : 0≤τ) (x y : ℝ×ℝ) (z : Atom) :
    weightedAtom τ x y z = weightedAtom 1 x y (tilt τ z) := by
  change _ = max (x.1*z 1+x.2*z 2) 0 * max (y.1*z 1+y.2*z 2) 0 +
    1*((sqrt τ*z 0)*(sqrt τ*z 0))*(actualGate (x.1*z 1+x.2*z 2)*actualGate (y.1*z 1+y.2*z 2))*dot x y
  rw [show (sqrt τ*z 0)*(sqrt τ*z 0)=τ*(z 0*z 0) by rw [←sq,mul_pow,sq_sqrt ht];ring,one_mul]
  rfl

private theorem energy_tilt (τ : ℝ) (ht : 0≤τ) (z : Atom) : atomEnergy (tilt τ z) ≤ mult τ*atomEnergy z := by
  change (sqrt τ*z 0)^2 + (z 1)^2 + (z 2)^2 ≤ mult τ*((z 0)^2 + (z 1)^2 + (z 2)^2)
  rw [mul_pow,sq_sqrt ht]
  nlinarith only [mul_le_mul_of_nonneg_right (le_max_right 1 τ) (sq_nonneg (z 0)),
    mul_le_mul_of_nonneg_right (le_max_left 1 τ) (sq_nonneg (z 1)),mul_le_mul_of_nonneg_right (le_max_left 1 τ) (sq_nonneg (z 2)),
    show mult τ=max 1 τ by rfl]

private def gridMark (τ : ℝ) (i j : Fin N) := weightedAtom τ (circleInput N i) (circleInput N j)
private def rowMark (τ : ℝ) (j : Fin N) (z : Atom) := ∫ t, weightedAtom τ (phase t) (circleInput N j) z ∂angularLaw
private def signedMark (τ b : ℝ) (j : Fin N) (z : Atom) := rowMark τ j z-b*((∑ i, gridMark τ i j z)/N)

private theorem gm_meas (τ : ℝ) (i j : Fin N) : Measurable (gridMark τ i j) :=
  weighted_meas τ measurable_const measurable_const measurable_id
private theorem pm_meas (τ : ℝ) (j : Fin N) : Measurable (rowMark τ j) := angle_test_meas (angle_weighted_meas τ _)
private theorem sm_meas (τ b : ℝ) (j : Fin N) : Measurable (signedMark τ b j) :=
  (pm_meas τ j).sub (measurable_const.mul ((Finset.measurable_fun_sum _ (fun i _ => gm_meas τ i j)).div_const _))
private theorem sharp_cap (τ : ℝ) (ht : 0≤τ) {x y : ℝ×ℝ} (ux : UnitInput x) (uy : UnitInput y) (z : Atom) :
    |weightedAtom τ x y z|≤mult τ*atomEnergy z := by
  rw [atom_tilt τ ht]; exact (CircleFiniteConfidence.sharp_atom ux uy _).trans (energy_tilt τ ht z)
private theorem gm_cap (τ : ℝ) (ht : 0≤τ) (i j : Fin N) (z : Atom) : |gridMark τ i j z| ≤ mult τ*atomEnergy z :=
  sharp_cap τ ht (grid_unit i) (grid_unit j) z
private theorem pm_cap (τ : ℝ) (ht : 0≤τ) (j : Fin N) (z : Atom) : |rowMark τ j z| ≤ mult τ*atomEnergy z :=
  angle_cap (fun t q => sharp_cap τ ht (phase_unit t) (grid_unit j) q) z
private theorem gm_eq (τ : ℝ) (hm : 0<m) (i j : Fin N) (z : Seed m) :
    gridGram τ z (startGates z) i j = sampleAverage (gridMark τ i j) z := weightedAtom_initial hm τ _ _ _
private theorem pm_eq (τ : ℝ) (hm : 0<m) (j : Fin N) (z : Seed m) :
    populationRow τ z (startGates z) j = sampleAverage (rowMark τ j) z := angular_entry_initial hm τ j z
private theorem sm_eq [NeZero N] (τ : ℝ) (hm : 0<m) (b : ℝ) (j : Fin N) (z : Seed m) :
    signedInitial τ b z j = sampleAverage (signedMark τ b j) z := by
  unfold signedInitial
  simp_rw [gm_eq τ hm,pm_eq τ hm]
  simp only [sampleAverage,signedMark,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_div]
  rw [Finset.sum_comm (s:=Finset.univ (α:=Fin N))];ring

private theorem sm_cap (τ : ℝ) (ht : 0≤τ) {b : ℝ} (hn : 3≤N) (odd : Odd N) (hb : 0≤b) (hu : b≤1)
    (j : Fin N) (z : Atom) : |signedMark τ b j z| ≤ (mult τ*(6/(N:ℝ)+1-b))*atomEnergy z := by
  have cap := CircleFiniteConfidence.sm_cap hn odd hb hu j (tilt τ z)
  have eq : signedMark τ b j z = CircleFiniteConfidence.sm b j (tilt τ z) := by
    simp only [signedMark,rowMark,gridMark,CircleFiniteConfidence.sm,CircleFiniteConfidence.gm,CircleFiniteConfidence.pm,atom_tilt τ ht]
  have e := energy_tilt τ ht z
  have d : 0≤6/(N:ℝ)+1-b := by linarith [show 0≤6/(N:ℝ) by positivity]
  rw [eq]
  exact cap.trans ((mul_le_mul_of_nonneg_left e d).trans_eq (by ring))

private theorem sm_zero (τ : ℝ) (ht : 0≤τ) (n : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (j : Fin (n+1)) :
    ∫ z, signedMark τ (weight τ n) j z ∂atomLaw = 0 := by
  let N := n+1
  let b := weight τ n
  have p := (energy_dominated (pm_meas τ j) (pm_cap τ ht j)).1.integrable (by norm_num)
  have g (i : Fin N) := (energy_dominated (gm_meas τ i j) (gm_cap τ ht i j)).1.integrable (by norm_num)
  have hgf : (∫ z, (∑ i, gridMark τ i j z)/N ∂atomLaw)=(∑ i : Fin N, sampledMatrix τ i j)/N := by
    rw [integral_div,integral_finsetSum _ (fun i _ => g i)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (congrFun (populationGram_sampled (N:=N) τ) i) j
  have hi := (integrable_finsetSum Finset.univ (fun (i : Fin N) _ => g i)).div_const (N:ℝ)
  have pp : (∫ z, rowMark τ j z ∂atomLaw)=k0 τ := populationMeanRow_constant τ j
  change (∫ z, rowMark τ j z-b*((∑ i, gridMark τ i j z)/N) ∂atomLaw)=0
  rw [integral_sub p (hi.const_mul b),integral_const_mul,hgf,pp,CirclePositiveSpectrum.weighted_column n hn odd τ ht j,sub_self]

private theorem grid_failure (τ : ℝ) (ht : 0≤τ) (N m : ℕ) [NeZero N] (hm : 0<m) {δ : ℝ} (hδ : 0<δ) :
    (seedLaw m).real {z | ¬∀ i j : Fin N, |gridGram τ z (startGates z) i j-sampledMatrix τ i j|≤mult τ*gridScale N δ/sqrt m} ≤δ/6 := by
  let B := fun (q : Fin N × Fin N) (z : Seed m) => gridGram τ z (startGates z) q.1 q.2-sampledMatrix τ q.1 q.2
  let U := mult τ*gridScale N δ/sqrt m
  have cpos := mp τ
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  have mpos : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have hU : 0<U := by dsimp [U,gridScale];positivity
  have scale : U^2=(mult τ)^2*90*(Fintype.card (Fin N × Fin N):ℝ)/(δ*m) := by
    simp only [U,gridScale,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,div_pow,mul_pow,sq_sqrt (by positivity : 0≤90/δ),sq_sqrt mpos.le]
    ring
  have h := family_failure (ι:=Fin N × Fin N) hm (fun q => gridMark τ q.1 q.2) B (mp τ) hδ hU scale
    (fun q => gm_meas τ q.1 q.2) (fun q => gm_cap τ ht q.1 q.2) (fun q z => by
      dsimp only [B]; rw [gm_eq τ hm]
      have ct : (∫ a, gridMark τ q.1 q.2 a ∂atomLaw)=sampledMatrix τ q.1 q.2 := congrFun (congrFun (populationGram_sampled (N:=N) τ) q.1) q.2
      rw [ct])
  have eq : {z : Seed m | ¬∀ i j : Fin N, |gridGram τ z (startGates z) i j-sampledMatrix τ i j| ≤mult τ*gridScale N δ/sqrt m} =
      {z | ¬∀ q, |B q z|≤U} := by ext z;simp only [Prod.forall,B,U,mem_ofPred_eq]
  rw [eq];exact h

private theorem row_failure (τ : ℝ) (ht : 0≤τ) (N m : ℕ) [NeZero N] (hm : 0<m) {δ : ℝ} (hδ : 0<δ) :
    (seedLaw m).real {z | ¬∀ j : Fin N, |populationRow τ z (startGates z) j-k0 τ|≤mult τ*rowScale N δ/sqrt m} ≤δ/6 := by
  have cpos := mp τ
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  have mpos : (0:ℝ)<m := Nat.cast_pos.mpr hm
  apply family_failure hm (rowMark τ) _ (mp τ) hδ (by unfold rowScale;positivity) _ (pm_meas τ) (pm_cap τ ht)
  · intro j z;rw [pm_eq τ hm]
    exact congrArg (_-·) (populationMeanRow_constant (N:=N) τ j).symm
  · simp only [rowScale,Fintype.card_fin,div_pow,mul_pow,sq_sqrt (by positivity : 0≤90*(N:ℝ)/δ),sq_sqrt mpos.le]
    ring

private theorem signed_failure (τ : ℝ) (ht : 0≤τ) (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m) {δ : ℝ} (hδ : 0<δ) :
    let N := n+1; let b := weight τ n
    (seedLaw m).real {z | ¬∀ j : Fin N, |signedInitial τ b z j|≤mult τ*signedScale N b δ/sqrt m} ≤δ/6 := by
  intro N b
  have cpos := mp τ
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have mpos : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have wb := CircleGaussianTracking.weight_bounds n ht
  have dp : 0<6/(N:ℝ)+1-b := by dsimp only [b];linarith [show 0<6/(N:ℝ) by positivity]
  apply family_failure hm (signedMark τ b) _ (mul_pos (mp τ) dp) hδ (by unfold signedScale rowScale;positivity) _ (sm_meas τ b)
    (fun i => sm_cap τ ht hn odd wb.1 wb.2 i)
  · intro j z;rw [sm_eq τ hm,sm_zero τ ht n hn odd,sub_zero]
  · simp only [signedScale,rowScale,Fintype.card_fin,div_pow,mul_pow,sq_sqrt (by positivity : 0≤90*(N:ℝ)/δ),sq_sqrt mpos.le]
    ring

/-- The six estimates in the finite-width theorem hold on a single
measurable event under the unconditioned Gaussian initialization. -/
theorem six_tests (τ : ℝ) (ht : 0≤τ) (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m) (δ A : ℝ)
    (hδ : 0<δ) (_hδ1 : δ<1) (hA : 0<A) (hr : A/sqrt m≤1) (energy : 36/δ≤m)
    (margin : 10*((n+1:ℕ)+1:ℕ)/(δ*A)≤sqrt m) :
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ ≤ δ ∧ ∀ z∈E, InitialBounds n m τ δ A z := by
  let N := n+1
  let b := weight τ n
  let ρ := A/sqrt m
  let P := seedLaw m
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have sq : (sqrt m)^2 = (m:ℝ) := sq_sqrt mp.le
  have rp : 0<ρ := div_pos hA (sqrt_pos.mpr mp)
  let B : Fin 6 → Set (Seed m) := ![
    {z | sqrt (12/δ)< ‖gridR N z‖},
    {z | ¬ ∀ i j : Fin N, |gridGram τ z (startGates z) i j-sampledMatrix τ i j|≤mult τ*gridScale N δ/sqrt m},
    {z | ¬ ∀ j : Fin N, |populationRow τ z (startGates z) j-k0 τ|≤mult τ*rowScale N δ/sqrt m},
    {z | ¬ ∀ j : Fin N, |signedInitial τ b z j|≤mult τ*signedScale N b δ/sqrt m},
    {z | ¬ meanEnergy z≤4},
    {z | ¬ ((∀ i : Fin N, marginMass z ρ (circleInput N i)≤6*ρ) ∧ angularMargin z ρ≤6*ρ)}]
  have each (i : Fin 6) : P.real (B i) ≤ δ/6 := by
    fin_cases i
    · have a := CircleInitialResidualSecond.residual_tail hn odd hm (show 0<sqrt (12/δ) by positivity)
      apply a.trans_eq
      rw [sq_sqrt (by positivity : 0≤12/δ)]; field_simp
      ring
    · exact grid_failure τ ht N m hm hδ
    · exact row_failure τ ht N m hm hδ
    · exact signed_failure τ ht n m hn odd hm hδ
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

end CirclePositiveConfidence
