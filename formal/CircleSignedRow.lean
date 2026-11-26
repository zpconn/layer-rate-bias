module

public import CircleSignedAngular
public import CircleDiscreteTracking
import all CircleDiscreteTracking
import all CircleSignedAngular
import all CircleMeanDynamics
import all CircleFlowPath
import all CircleTangentDrift
import all CircleEscapeBridge
import all CircleEscape
import Mathlib.Tactic

/-! Cancellation of the mixed tangent row under the original relative motion
tube, with readout-weighted counts of the neurons whose gates may change. -/
@[expose] public section
noncomputable section
namespace CircleSignedRow
open Real MeasureTheory CircleFlowPath CircleTangentDrift CircleEscapeBridge CircleSignedAngular
open scoped InnerProductSpace
variable {m N : ℕ}

abbrev hiddenWeight (z : State m) (j : Fin m) := (initial z).w j
def coordinates (v : ℂ) := (v.re,v.im)
def unitFeature (z : State m) (j : Fin m) (v : ℂ) := CircleEscape.feature (hiddenWeight z j) v
def unitGate (z : State m) (j : Fin m) (v : ℂ) := CircleEscape.gate (hiddenWeight z j) v
private def gateDir (z : State m) (j : Fin m) (y v : ℂ) := unitGate z j v*inner ℝ y v

def readoutMargin (z : State m) (ρ : ℝ) (v : ℂ) :=
  (∑ j, z (j,0)^2 * marginFlag z ρ (coordinates v) j)/m

def mixedAtom (N : ℕ) (b : ℝ) (z v : State m) (y : ℂ) (j : Fin m) :=
  signedFeature N b (hiddenWeight z j)*unitFeature v j y +
    (z (j,0)*v (j,0))*unitGate v j y * inner ℝ y (signedGate N b (hiddenWeight z j))

def mixedRow (N : ℕ) (b : ℝ) (z v : State m) (y : ℂ) :=
  (∑ j, mixedAtom N b z v y j)/m

private theorem projection_eq (z : State m) (j : Fin m) (v : ℂ) : inner ℝ (hiddenWeight z j) v=pre z j (coordinates v) := by
  simp [hiddenWeight,initial,Complex.inner,Complex.mul_re,pre,coordinates]

private theorem coord_gate (z : State m) (j : Fin m) (v : ℂ) : unitGate z j v=actualGate (pre z j (coordinates v)) := by
  rw [unitGate,CircleEscape.gate,projection_eq];rfl

private theorem unit_xy {v : ℂ} (hv : ‖v‖≤1) : UnitInput (coordinates v) := by
  have a := pow_le_pow_left₀ (norm_nonneg _) hv 2
  rw [Complex.sq_norm,Complex.normSq_apply] at a
  simpa [UnitInput,coordinates,sq] using a

private theorem hidden_le (z : State m) (j : Fin m) : ‖hiddenWeight z j‖≤length z j := by
  apply (sq_le_sq₀ (norm_nonneg _) (sqrt_nonneg _)).mp
  change ‖hiddenWeight z j‖^2≤length z j^2
  rw [length_sq,Complex.sq_norm,Complex.normSq_apply]
  dsimp [hiddenWeight,initial];nlinarith only [sq_nonneg (z (j,0))]

private theorem hidden_move {z v : State m} (j : Fin m) :
    ‖hiddenWeight z j-hiddenWeight v j‖≤length (z-v) j := by
  have eq : hiddenWeight z j-hiddenWeight v j=hiddenWeight (z-v) j := by apply Complex.ext <;> rfl
  rw [eq];exact hidden_le _ _

private theorem flag_int (z : State m) (ρ : ℝ) (j : Fin m) :
    Integrable (fun u => marginFlag z ρ (coordinates (x u)) j) Q := by
  have me : MeasurableSet {u : ℝ | |pre z j (phase u)|≤ρ*length z j} :=
    measurableSet_le (pre_phase_cont z j).abs.measurable measurable_const
  exact ((integrable_const (1:ℝ)).indicator (μ:=Q) me).congr (ae_of_all _ fun u => by
    change _ = if |pre z j (phase u)|≤ρ*length z j then 1 else 0
    simp [Set.indicator])

private theorem dir_int (z : State m) (j : Fin m) (y : ℂ) :
    Integrable (fun u => gateDir z j y (x u)) Q := by
  have hi := ((innerSL ℝ y).integrable_comp (gate_field_integrable (hiddenWeight z j)))
  simpa only [Function.comp_apply,innerSL_apply_apply,real_inner_smul_right,gateDir,unitGate] using hi

private theorem project_signed (z : State m) (j : Fin m) (y : ℂ) (N : ℕ) (b : ℝ) :
    inner ℝ y (signedGate N b (hiddenWeight z j)) =
    (∫ u, gateDir z j y (x u) ∂Q)-b*avg N (gateDir z j y) := by
  rw [signedGate,inner_sub_right,real_inner_smul_right,inner_pop,inner_grid]
  rfl

private theorem gate_one (z : State m) (j : Fin m) (y : ℂ) : |unitGate z j y|≤1 := by
  unfold unitGate CircleEscape.gate;split <;> norm_num

private theorem eval_gate_change (N : ℕ) {b ρ : ℝ} (hb : 0≤b) {z₀ z : State m}
    (tz : Tube ρ z₀ z) (j : Fin m) {y : ℂ} (hy : ‖y‖≤1) :
    |inner ℝ y (signedGate N b (hiddenWeight z j))-inner ℝ y (signedGate N b (hiddenWeight z₀ j))| ≤
    (∫ u, marginFlag z₀ ρ (coordinates (x u)) j ∂Q)+b*avg N (fun w => marginFlag z₀ ρ (coordinates w) j) := by
  have each (w : ℂ) (hw : ‖w‖≤1) : |gateDir z j y w-gateDir z₀ j y w|≤marginFlag z₀ ρ (coordinates w) j := by
    rw [gateDir,gateDir,←sub_mul,abs_mul,coord_gate,coord_gate]
    have h1 := gate_motion (j:=j) (unit_xy hw) tz (actualGate_admissible _) (actualGate_admissible _)
    have h2 := (abs_real_inner_le_norm y w).trans ((mul_le_mul hy hw (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    exact (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)).trans (mul_le_of_le_one_right ((abs_nonneg _).trans h1) h2)
  have pop := abs_integral_le_integral_abs (μ:=Q) (f:=fun u => gateDir z j y (x u)-gateDir z₀ j y (x u))
  have A := pop.trans (integral_mono ((dir_int z j y).sub (dir_int z₀ j y)).abs (flag_int z₀ ρ j)
    (fun u => each _ (x_norm u).le))
  have B : |avg N (gateDir z j y)-avg N (gateDir z₀ j y)|≤avg N (fun w => marginFlag z₀ ρ (coordinates w) j) := by
    simp only [avg,←sub_div,←Finset.sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) N)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => each _ (CircleEscape.grid_norm N i).le)
  rw [project_signed,project_signed]
  rw [show (∫ u, gateDir z j y (x u) ∂Q)-b*avg N (gateDir z j y)-
    ((∫ u, gateDir z₀ j y (x u) ∂Q)-b*avg N (gateDir z₀ j y))=
    ((∫ u, gateDir z j y (x u) ∂Q)-(∫ u, gateDir z₀ j y (x u) ∂Q))-b*(avg N (gateDir z j y)-avg N (gateDir z₀ j y)) by ring]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg hb,←integral_sub (dir_int z j y) (dir_int z₀ j y)]
  exact add_le_add A (mul_le_mul_of_nonneg_left B hb)

private theorem atom_motion (N : ℕ) {b ρ G₀ B₀ : ℝ} (hb : 0≤b) (hρ : 0≤ρ) (hG : 0≤G₀) (hB : 0≤B₀)
    (gb : ∀ w, ‖signedGate N b w‖≤G₀) (fb : ∀ w, |signedFeature N b w|≤B₀*‖w‖)
    (lip : ∀ v w, |signedFeature N b v-signedFeature N b w|≤G₀*‖v-w‖)
    {z₀ z v : State m} (tz : Tube ρ z₀ z) (tv : Tube ρ z₀ v) (j : Fin m) {y : ℂ} (hy : ‖y‖≤1) :
    |mixedAtom N b z v y j-mixedAtom N b z₀ z₀ y j|≤
      (((3+2*ρ)*G₀+B₀)*ρ)*length z₀ j^2 +
      G₀*(z₀ (j,0)^2*marginFlag z₀ ρ (coordinates y) j) +
      z₀ (j,0)^2*((∫ u,marginFlag z₀ ρ (coordinates (x u)) j ∂Q)+b*avg N (fun w => marginFlag z₀ ρ (coordinates w) j)) := by
  let L := length z₀ j
  let A := z₀ (j,0)
  let F := fun w : State m => signedFeature N b (hiddenWeight w j)
  let D := fun w : State m => inner ℝ y (signedGate N b (hiddenWeight w j))
  let M := marginFlag z₀ ρ (coordinates y) j
  let K := (∫ u,marginFlag z₀ ρ (coordinates (x u)) j ∂Q)+b*avg N (fun w => marginFlag z₀ ρ (coordinates w) j)
  have lp : 0≤L := sqrt_nonneg _
  have Gd (w : State m) : |D w|≤G₀ := (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul hy (gb _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have A0 := readout_bound z₀ j
  have move (u : State m) (tu : Tube ρ z₀ u) : |u (j,0)-A|≤ρ*L := (readout_bound (u-z₀) j).trans (tu j)
  have coef : |z (j,0)*v (j,0)-A^2|≤(2*ρ+ρ^2)*L^2 := by
    rw [sq A]; exact product_motion lp hρ (move _ tz) (move _ tv) A0 A0
  have gateM : |unitGate v j y-unitGate z₀ j y|≤M := by
    rw [coord_gate,coord_gate]; exact gate_motion (unit_xy hy) tv (actualGate_admissible _) (actualGate_admissible _)
  have fd : |F z-F z₀|≤G₀*(ρ*L) := (lip _ _).trans (mul_le_mul_of_nonneg_left ((hidden_move j).trans (tz j)) hG)
  have f0 : |F z₀|≤B₀*L := (fb _).trans (mul_le_mul_of_nonneg_left (hidden_le z₀ j) hB)
  have valdiff : |unitFeature v j y-unitFeature z₀ j y|≤ρ*L := by
    simp only [unitFeature,CircleEscape.feature,projection_eq]
    exact (relu_motion _ _).trans (pre_motion _ _ _ _ (unit_xy hy) tv)
  have val0 : |unitFeature z₀ j y|≤L := by
    rw [unitFeature,CircleEscape.feature,projection_eq,abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (pre_bound _ _ _ (unit_xy hy))) lp
  have val : |unitFeature v j y|≤(1+ρ)*L := by
    have A := (abs_sub_le (unitFeature v j y) (unitFeature z₀ j y) 0)
    simp only [sub_zero] at A
    nlinarith only [A,valdiff,val0]
  have ch1 := mul_le_mul fd val (abs_nonneg _) (mul_nonneg hG (mul_nonneg hρ lp))
  have ch2 := mul_le_mul f0 valdiff (abs_nonneg _) (mul_nonneg hB lp)
  have hF : |F z*unitFeature v j y-F z₀*unitFeature z₀ j y|≤(((1+ρ)*G₀+B₀)*ρ)*L^2 := by
    rw [show F z*unitFeature v j y-F z₀*unitFeature z₀ j y=(F z-F z₀)*unitFeature v j y+F z₀*(unitFeature v j y-unitFeature z₀ j y) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul];nlinarith only [ch1,ch2]
  have pG : |unitGate v j y*D z|≤G₀ := by
    rw [abs_mul]
    exact (mul_le_mul (gate_one _ _ _) (Gd z) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hC := mul_le_mul coef pG (abs_nonneg _) (by positivity)
  have hM := mul_le_mul gateM (Gd z) (abs_nonneg _) ((abs_nonneg _).trans gateM)
  have hK := eval_gate_change N hb tz j hy
  have hK' : |unitGate z₀ j y| * |D z-D z₀|≤K :=
    (mul_le_mul (gate_one _ _ _) hK (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hGates : |unitGate v j y*D z-unitGate z₀ j y*D z₀|≤M*G₀+K := by
    rw [show unitGate v j y*D z-unitGate z₀ j y*D z₀=(unitGate v j y-unitGate z₀ j y)*D z+unitGate z₀ j y*(D z-D z₀) by ring]
    apply (abs_add_le _ _).trans;rw [abs_mul,abs_mul];exact add_le_add hM hK'
  have hR := mul_le_mul_of_nonneg_left hGates (sq_nonneg A)
  change |F z*unitFeature v j y+z (j,0)*v (j,0)*unitGate v j y*D z-(F z₀*unitFeature z₀ j y+A*A*unitGate z₀ j y*D z₀)|≤_
  rw [show F z*unitFeature v j y+z (j,0)*v (j,0)*unitGate v j y*D z-(F z₀*unitFeature z₀ j y+A*A*unitGate z₀ j y*D z₀)=
    (F z*unitFeature v j y-F z₀*unitFeature z₀ j y)+(z (j,0)*v (j,0)-A^2)*(unitGate v j y*D z)+A^2*(unitGate v j y*D z-unitGate z₀ j y*D z₀) by ring]
  apply (abs_add_le _ _).trans
  apply (add_le_add_left (abs_add_le _ _) _).trans
  rw [abs_mul (z (j,0)*v (j,0)-A^2),abs_mul (A^2),abs_of_nonneg (sq_nonneg A)]
  change _≤(((3+2*ρ)*G₀+B₀)*ρ)*L^2+G₀*(A^2*M)+A^2*K
  nlinarith only [hF,hC,hR]

private theorem sum_eval (N : ℕ) (z : State m) (ρ b : ℝ) :
    (∑ j, z (j,0)^2*((∫ u, marginFlag z ρ (coordinates (x u)) j ∂Q)+b*avg N (fun w => marginFlag z ρ (coordinates w) j)))/m =
    (∫ u, readoutMargin z ρ (x u) ∂Q)+b*avg N (readoutMargin z ρ) := by
  simp only [readoutMargin,integral_div,integral_finsetSum _ (fun j _ => (flag_int z ρ j).const_mul _),integral_const_mul,
    avg,mul_add,Finset.sum_add_distrib,add_div]
  congr 1
  simp only [←Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem mixed_drift_of_bounds (N : ℕ) {ρ b G₀ B₀ : ℝ} (hb : 0≤b) (hρ : 0≤ρ) (hr : ρ≤1)
    (hG : 0≤G₀) (hB : 0≤B₀)
    (gb : ∀ w, ‖signedGate N b w‖≤G₀) (fb : ∀ w, |signedFeature N b w|≤B₀*‖w‖)
    (lip : ∀ v w, |signedFeature N b v-signedFeature N b w|≤G₀*‖v-w‖)
    {z₀ z v : State m} (tz : Tube ρ z₀ z) (tv : Tube ρ z₀ v) {y : ℂ} (hy : ‖y‖≤1)
    (energy : meanEnergy z₀≤4) (test : readoutMargin z₀ ρ y≤2*ρ)
    (ang : (∫ u, readoutMargin z₀ ρ (x u) ∂Q)≤2*ρ)
    (nodes : ∀ i : Fin N, readoutMargin z₀ ρ (CircleEscape.gridPoint N i)≤2*ρ) :
    |mixedRow N b z v y-mixedRow N b z₀ z₀ y|≤(22*G₀+4*B₀+2*(1+b))*ρ := by
  let c := ((3+2*ρ)*G₀+B₀)*ρ
  have cp : 0≤c := by dsimp [c];positivity
  have one := fun j => atom_motion N hb hρ hG hB gb fb lip tz tv j hy
  rw [mixedRow,mixedRow,←sub_div,←Finset.sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) m)]
  apply (div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => one j)) (Nat.cast_nonneg _)).trans
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,add_div,add_div,sum_eval,←Finset.mul_sum,←Finset.mul_sum]
  have mean : avg N (readoutMargin z₀ ρ)≤2*ρ := by
    by_cases n0 : N=0
    · simp [avg,n0,hρ]
    · apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero n0))).mpr
      exact (Finset.sum_le_sum (g:=fun _ => 2*ρ) (fun i _ => nodes i)).trans_eq (by simp;ring)
  have A := mul_le_mul_of_nonneg_left energy cp
  have B := mul_le_mul_of_nonneg_left test hG
  have C := mul_le_mul_of_nonneg_left mean hb
  have D := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr hG) hρ
  simp only [meanEnergy,readoutMargin] at A B
  dsimp [c] at A
  simp only [mul_div_assoc]
  nlinarith only [A,B,C,D,ang]

private def originalAtom (z v : State m) (y : ℂ) (j : Fin m) (w : ℂ) :=
  unitFeature z j w*unitFeature v j y+(z (j,0)*v (j,0)*unitGate v j y)*gateDir z j y w

private theorem original_eq (z v : State m) (y : ℂ) (j : Fin m) (w : ℂ) :
    originalAtom z v y j w = atom 1 z v (coordinates w) (coordinates y)
      (fun k => actualGate (pre z k (coordinates w))) (fun k => actualGate (pre v k (coordinates y))) j := by
  simp only [originalAtom,gateDir,unitFeature,CircleEscape.feature,projection_eq,coord_gate,atom,dot,coordinates]
  simp [Complex.inner,Complex.mul_re];ring

private theorem orig_integrable (z v : State m) (y : ℂ) (j : Fin m) :
    Integrable (fun u => originalAtom z v y j (x u)) Q := by
  simp_rw [original_eq]
  exact atom_integrable 1 z v (coordinates y) (fun k => actualGate (pre v k (coordinates y))) j

private theorem atom_signed (N : ℕ) (b : ℝ) (z v : State m) (y : ℂ) (j : Fin m) :
    mixedAtom N b z v y j = (∫ u,originalAtom z v y j (x u) ∂Q)-b*avg N (originalAtom z v y j) := by
  let E := fun u => unitFeature z j (x u)
  have eqE (u : ℝ) : E u=CircleMeanDynamics.feature z j u := by
    simp only [E,unitFeature,CircleEscape.feature,projection_eq];rfl
  have ei : Integrable E Q := by rw [funext eqE]; exact CircleMeanDynamics.feature_integrable z j
  have e : (∫ u,E u ∂Q)=‖hiddenWeight z j‖/π := by rw [funext eqE];exact CircleMeanDynamics.meanFeature_eq _ _
  let C := z (j,0)*v (j,0)*unitGate v j y
  have pop : (∫ u,originalAtom z v y j (x u) ∂Q)=‖hiddenWeight z j‖/π*unitFeature v j y + C*(∫ u,gateDir z j y (x u) ∂Q) := by
    change (∫ u, E u*unitFeature v j y + C*gateDir z j y (x u) ∂Q)=_
    rw [integral_add (ei.mul_const _) ((dir_int _ _ _).const_mul _),integral_mul_const,e,integral_const_mul]
  rw [pop,mixedAtom,project_signed]
  simp only [signedFeature,avg,originalAtom,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum]
  dsimp only [C,unitFeature]
  ring

/-- The finite-neuron expression is the actual mixed Jacobian tested against
the population average minus the weighted training-grid average. -/
theorem mixedRow_eq (N : ℕ) (b : ℝ) {m : ℕ} (hm : 0<m) (z v : State m) (y : ℂ) :
    mixedRow N b z v y = meanEntry 1 z v (coordinates y) (fun k => actualGate (pre v k (coordinates y))) -
      b*avg N (fun w => entry 1 z v (coordinates w) (coordinates y)
        (fun k => actualGate (pre z k (coordinates w))) (fun k => actualGate (pre v k (coordinates y)))) := by
  have eq (w : ℂ) : entry 1 z v (coordinates w) (coordinates y)
        (fun k => actualGate (pre z k (coordinates w))) (fun k => actualGate (pre v k (coordinates y))) =
        (∑ j, originalAtom z v y j w)/m := by rw [entry_sum hm];simp_rw [original_eq]
  have pop : meanEntry 1 z v (coordinates y) (fun k => actualGate (pre v k (coordinates y))) =
    (∑ j, ∫ u,originalAtom z v y j (x u) ∂Q)/m := by
    change (∫ u,entry 1 z v (coordinates (x u)) (coordinates y) (fun k => actualGate (pre z k (coordinates (x u)))) _ ∂Q)=_
    simp_rw [eq]
    rw [integral_div,integral_finsetSum _ (fun j _ => orig_integrable z v y j)]
  rw [pop,mixedRow];simp_rw [atom_signed,eq]
  simp only [Finset.sum_sub_distrib,sub_div]
  congr 1
  simp only [avg,←Finset.mul_sum,←Finset.sum_div]
  rw [Finset.sum_comm (s:=Finset.univ (α:=Fin m))]
  ring

/-- Sharp mixed-row drift at every training input, for genuine segment
and update-start factors in the initialization tube. -/
theorem mixed_drift (N : ℕ) (hn : 3≤N) (odd : Odd N) {ρ b : ℝ} (hb : 0≤b) (hρ : 0≤ρ) (hr : ρ≤1)
    {z₀ z v : State m} (tz : Tube ρ z₀ z) (tv : Tube ρ z₀ v)
    (energy : meanEnergy z₀≤4) (ang : (∫ u, readoutMargin z₀ ρ (x u) ∂Q)≤2*ρ)
    (nodes : ∀ i : Fin N, readoutMargin z₀ ρ (CircleEscape.gridPoint N i)≤2*ρ) (i : Fin N) :
    |mixedRow N b z v (CircleEscape.gridPoint N i)-mixedRow N b z₀ z₀ (CircleEscape.gridPoint N i)|≤
    (22*G N b+4*B N b+2*(1+b))*ρ :=
  mixed_drift_of_bounds N hb hρ hr (sqrt_nonneg _) ((abs_nonneg _).trans (le_max_left _ _))
    (gate_bound hn odd hb) (feature_bound hn odd hb) (feature_lipschitz hn odd hb)
    tz tv (CircleEscape.grid_norm N i).le energy (nodes i) ang nodes

/-- Along an actual GD update segment this is the signed mixed tangent row
that drives the change of the population statistic. -/
theorem segment_drift (N : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m)
    {ρ b : ℝ} (hb : 0≤b) (hρ : 0≤ρ) (hr : ρ≤1) {z₀ v : State m} (s : ℝ)
    (tv : Tube ρ z₀ v) (ts : Tube ρ z₀ (CircleDiscreteTracking.seg N v s))
    (energy : meanEnergy z₀≤4) (ang : (∫ u, readoutMargin z₀ ρ (x u) ∂Q)≤2*ρ)
    (nodes : ∀ i : Fin N, readoutMargin z₀ ρ (CircleEscape.gridPoint N i)≤2*ρ) (i : Fin N) :
    |(meanEntry 1 (CircleDiscreteTracking.seg N v s) v (circleInput N i) (startGates v i) -
       b*((∑ k : Fin N, CircleDiscreteTracking.mixedRow N v (circleInput N k) s i)/N)) -
      (populationRow 1 z₀ (startGates z₀) i -
       b*((∑ k : Fin N, gridGram 1 z₀ (startGates z₀) k i)/N))|≤
    (22*G N b+4*B N b+2*(1+b))*ρ := by
  have a := mixed_drift N hn odd hb hρ hr ts tv energy ang nodes i
  rw [mixedRow_eq _ _ hm,mixedRow_eq _ _ hm] at a
  exact a

end CircleSignedRow
