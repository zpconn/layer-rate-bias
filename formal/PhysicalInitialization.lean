module

public import SmoothSeedLaw
import all SmoothSeedLaw
import Mathlib.Tactic

/-! Physical readouts and hidden weights in the fixed-input-dimension
parameterization, with their exact normalization under Gaussian initialization. -/
@[expose] public section
noncomputable section
namespace PhysicalInitialization
open Real Filter Topology MeasureTheory ProbabilityTheory SmoothSeedLaw TwoLayerNetwork
open scoped InnerProductSpace
variable {d n : ℕ}

def physical (z : Params n d) : Params n d := WithLp.toLp 2 fun p =>
  Fin.cases (readout z p.1 / sqrt n) (fun j => (TwoLayerNetwork.hidden z p.1 j)/sqrt d) p.2

def hiddenNorm (z : Params n d) : ℝ := sqrt (∑ i, ‖TwoLayerNetwork.hidden z i‖^2/(d:ℝ))

private def hiddenPart (z : Params n d) : Params n d := WithLp.toLp 2 fun p =>
  Fin.cases 0 (fun j => (TwoLayerNetwork.hidden z p.1 j)/sqrt d) p.2

private theorem hidden_part_sq (z : Params n d) :
    ‖hiddenPart z‖^2 = ∑ i, ‖TwoLayerNetwork.hidden z i‖^2/(d:ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ,EuclideanSpace.real_norm_sq_eq,Finset.sum_div]
  simp [hiddenPart,div_pow,sq_sqrt (Nat.cast_nonneg d)]

private theorem part_norm (z : Params n d) : ‖hiddenPart z‖=hiddenNorm z := by
  unfold hiddenNorm; rw [←hidden_part_sq,Real.sqrt_sq (norm_nonneg _)]

theorem physical_sq (z : Params n d) :
    ‖physical z‖^2 = (∑ i, (readout z i)^2)/(n:ℝ) + (∑ i, ‖TwoLayerNetwork.hidden z i‖^2)/(d:ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type,Finset.sum_div,Finset.sum_div,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ,EuclideanSpace.real_norm_sq_eq,Finset.sum_div]
  simp [physical,div_pow,sq_sqrt (Nat.cast_nonneg d),sq_sqrt (Nat.cast_nonneg n)]

theorem physical_hidden_le (z : Params n d) : hiddenNorm z ≤ ‖physical z‖ := by
  apply (sqrt_le_iff).mpr ⟨norm_nonneg _,?_⟩
  rw [physical_sq,←Finset.sum_div]
  exact le_add_of_nonneg_left (by positivity)

theorem hidden_sub_le (hd : 0<d) (x y : Params n d) : |hiddenNorm x-hiddenNorm y| ≤ ‖x-y‖ := by
  rw [←part_norm,←part_norm]
  apply (abs_norm_sub_norm_le _ _).trans
  have eq : hiddenPart x-hiddenPart y = hiddenPart (x-y) := by
    ext p
    obtain ⟨i,j⟩ := p
    refine Fin.cases ?_ (fun a => ?_) j
    · change 0-0=(0:ℝ);ring
    · change x (i,a.succ)/sqrt d-y (i,a.succ)/sqrt d=(x (i,a.succ)-y (i,a.succ))/sqrt d;ring
  rw [eq]
  let z := x-y
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hidden_part_sq]
  have g := radius_identity z 0
  have rz (i : Fin n) : readout (0 : Params n d) i=0 := rfl
  have hz (i : Fin n) : TwoLayerNetwork.hidden (0 : Params n d) i=0 := rfl
  simp only [rz,hz,sub_zero] at g
  have all : (∑ i, ((readout z i)^2+‖TwoLayerNetwork.hidden z i‖^2)) = ‖z‖^2 := by
    exact g
  change (∑ i, ‖TwoLayerNetwork.hidden z i‖^2/(d:ℝ))≤‖z‖^2
  rw [←all]
  apply Finset.sum_le_sum
  intro i _
  exact (div_le_self (sq_nonneg _) (by exact_mod_cast hd : (1:ℝ)≤d)).trans (by linarith [sq_nonneg (readout z i)])

private abbrev G := gaussianReal 0 1

/-- The width-n prefix of the iid Gaussian neuron stream has exactly the
packed isotropic Gaussian law used by the nonlinear movement theorem. -/
theorem packed_law (n d : ℕ) :
    HasLaw (packed n (d:=d)) (stdGaussian (Params n d)) (law d) := by
  let row := Fin (d+1) → ℝ
  let raw := Fin n × Fin (d+1) → ℝ
  let pack : (Fin n → Neuron d) → Params n d := fun z => WithLp.toLp 2 (fun p : Fin n × Fin (d+1) =>
    Fin.cases (z p.1).1 (fun j => (z p.1).2 j) p.2)
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
  let neuron : row → Neuron d := fun v => ((split v).1,WithLp.toLp 2 (split v).2)
  have hs := measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => G) 0
  have hw : MeasurePreserving (WithLp.toLp 2) (Measure.pi (fun _ : Fin d => G)) (stdGaussian (Space d)) :=
    ⟨by fun_prop,map_pi_eq_stdGaussian⟩
  have hrow : MeasurePreserving neuron (Measure.pi fun _ : Fin (d+1) => G) (neuronLaw d) :=
    ((MeasurePreserving.id G).prod hw).comp hs
  have curr : MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin (d+1)) ℝ)
      (Measure.pi (fun _ : Fin n × Fin (d+1) => G)) (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin (d+1) => G))) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).measurable,?_⟩
    simpa [Measure.infinitePi_eq_pi] using Measure.infinitePi_map_curry (fun (_ : Fin n) (_ : Fin (d+1)) => G)
  let block := fun v : raw => fun i : Fin n => neuron (fun j => v (i,j))
  have joint : MeasurePreserving block (Measure.pi (fun _ : Fin n × Fin (d+1) => G)) (Measure.pi (fun _ : Fin n => neuronLaw d)) :=
    (measurePreserving_pi _ _ (fun _ => hrow)).comp curr
  have eq : pack ∘ block = fun v : raw => WithLp.toLp 2 v := by
    funext v
    ext ⟨i,j⟩
    refine Fin.cases ?_ (fun a => ?_) j
    · rfl
    · change v (i,(0:Fin (d+1)).succAbove a)=v (i,a.succ)
      simp
  have meas : Measurable pack := by
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    apply measurable_pi_iff.mpr
    rintro ⟨i,j⟩
    refine Fin.cases ?_ (fun a => ?_) j
    · change Measurable (fun u : Fin n → Neuron d => (u i).1)
      fun_prop
    · change Measurable (fun u : Fin n → Neuron d => (u i).2 a)
      fun_prop
  have target : HasLaw pack (stdGaussian (Params n d)) (Measure.pi (fun _ : Fin n => neuronLaw d)) := by
    refine ⟨meas.aemeasurable,?_⟩
    rw [←joint.map_eq,Measure.map_map meas joint.measurable,eq,map_pi_eq_stdGaussian]
  have iid : iIndepFun (fun (i : Fin n) (ω : Draws d) => ω i) (law d) :=
    iIndepFun.precomp Fin.val_injective (iIndepFun_infinitePi (fun _ => measurable_id))
  exact target.comp (iid.hasLaw_pi fun i => eval_law (d:=d) i.val)

private theorem coordinate_law (j : Fin d) :
    HasLaw (fun w : Space d => w j) (gaussianReal 0 1) (stdGaussian (Space d)) := by
  let e := EuclideanSpace.single j (1:ℝ)
  have q : (fun w : Space d => w j) = innerSL ℝ e := by ext w; simp [e,EuclideanSpace.inner_single_left]
  rw [q]
  refine ⟨by fun_prop,?_⟩
  rw [IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian,innerSL_apply_norm]
  simp [e]

private theorem hidden_second :
    Integrable (fun w : Space d => ‖w‖^2) (stdGaussian (Space d)) ∧
    (∫ w : Space d, ‖w‖^2 ∂stdGaussian (Space d))=d := by
  have h (j : Fin d) : Integrable (fun w : Space d => (w j)^2) (stdGaussian (Space d)) :=
    (coordinate_law j).integrable_comp normal_squared.1
  have moment (j : Fin d) : (∫ w : Space d, (w j)^2 ∂stdGaussian (Space d))=1 :=
    ((coordinate_law j).integral_comp (f:=fun a => a^2) (by fun_prop)).trans normal_squared.2
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact ⟨integrable_finsetSum _ (fun i _ => h i), by rw [integral_finsetSum _ (fun i _ => h i)];simp [moment]⟩

/-- On one infinite iid Gaussian draw, the initial physical Euclidean norm
divided by √n tends almost surely to one at every fixed positive input dimension. -/
theorem normalized (hd : 0<d) : ∀ᵐ ω ∂law d,
    Tendsto (fun n : ℕ => ‖physical (packed n ω)‖/sqrt n) atTop (𝓝 1) := by
  have ha := observable_lln (fun t : Neuron d => t.1^2) (by fun_prop) (normal_squared.1.comp_fst _)
  have hw := observable_lln (fun t : Neuron d => ‖t.2‖^2) (by fun_prop) (hidden_second.1.comp_snd _)
  have ma : (∫ t : Neuron d, t.1^2 ∂neuronLaw d)=1 := by rw [neuronLaw,integral_fun_fst (fun a : ℝ => a^2)];simpa using normal_squared.2
  have mw : (∫ t : Neuron d, ‖t.2‖^2 ∂neuronLaw d) = d := by rw [neuronLaw,integral_fun_snd (fun w : Space d => ‖w‖^2)];simpa using (hidden_second (d:=d)).2
  rw [ma] at ha
  rw [mw] at hw
  filter_upwards [ha,hw] with ω a w
  have inv := (tendsto_natCast_atTop_atTop (R:=ℝ)).inv_tendsto_atTop
  have lim := ((a.mul inv).add (w.div_const (d:ℝ))).sqrt
  have dp : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  simp only [one_mul,div_self dp,zero_add,sqrt_one] at lim
  apply lim.congr
  intro n
  simp only [smul_eq_mul]
  rw [←Real.sqrt_sq (norm_nonneg (physical (packed n ω))), ←sqrt_div (sq_nonneg _), physical_sq]
  simp only [packed_a,packed_w]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (ω i).1^2) n,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖(ω i).2‖^2) n]
  change Real.sqrt (_*(n:ℝ)⁻¹+_) = _
  congr 1; ring

end PhysicalInitialization
