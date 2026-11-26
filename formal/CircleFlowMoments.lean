module

public import CircleFlowPath
import all CircleFlowPath
public import CircleInitializationConcentration
public import CircleSeedIntegrability
import all CircleEscape
import all CircleEscapeBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic

/-! Actual finite-time weighted-flow outputs on the product Gaussian seed. The
radial estimate gives a coarse global fourth moment. The displacement bound
and the sharp initialization moments give a width-uniform fourth norm at fixed time. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory CircleEscapeBridge
namespace CircleFlowMoments
open CircleFlowPath
variable {m N : ℕ}

def squared (z : State m) : ℝ := ∑ p, z p ^ 2

def mean (z : State m) : ℝ := CircleEscape.populationMean (1/Real.sqrt m) (initial z)

private theorem hidden_sq (z : State m) (j : Fin m) :
    ‖(initial z).w j‖^2 = z (j,1)^2 + z (j,2)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  dsimp [initial]
  ring

private theorem neuron_cap (z : State m) (j : Fin m) :
    |(initial z).a j| * ‖(initial z).w j‖ ≤ (∑ k : Fin 3, z (j,k)^2)/2 := by
  rw [Fin.sum_univ_three]
  have h := sq_nonneg (|(initial z).a j|-‖(initial z).w j‖)
  have ha : |(initial z).a j|^2 = z (j,0)^2 := sq_abs _
  nlinarith [hidden_sq z j]

theorem mean_cap (z : State m) :
    |mean z| ≤ (1/Real.sqrt m)*(squared z/2) := by
  rw [mean,CircleEscape.populationMean,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (1/Real.sqrt m)/Real.pi)]
  have hs := (Finset.abs_sum_le_sum_abs (fun j => (initial z).a j*‖(initial z).w j‖) Finset.univ).trans
    (Finset.sum_le_sum (s:=Finset.univ) fun j _ => (by simpa only [abs_mul,abs_norm] using neuron_cap z j))
  have he : (∑ j, (∑ k : Fin 3, z (j,k)^2)/2) = squared z /2 := by
    rw [← Finset.sum_div, squared,Fintype.sum_prod_type]
  rw [he] at hs
  have hp := div_le_self (show 0 ≤ 1/Real.sqrt m by positivity) (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)
  exact mul_le_mul hp hs (abs_nonneg _) (by positivity)

theorem output_cap (z : State m) (x : ℂ) (unit : ‖x‖ ≤ 1) :
    |CircleEscape.output (1/Real.sqrt m) (initial z) x| ≤ (1/Real.sqrt m)*(squared z/2) := by
  rw [CircleEscape.output,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/Real.sqrt m)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [squared,Fintype.sum_prod_type,Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  apply le_trans _ (neuron_cap z j)
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  unfold CircleEscape.feature
  rw [abs_of_nonneg (le_max_right _ _)]
  apply max_le _ (norm_nonneg _)
  exact (real_inner_le_norm _ _).trans (by simpa using mul_le_mul_of_nonneg_left unit (norm_nonneg ((initial z).w j)))

theorem reference_cap (z : State m) (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1) :
    |reference N m b z| ≤ 1+(1/Real.sqrt m)*squared z := by
  let f := fun i => CircleEscape.output (1/Real.sqrt m) (initial z) (CircleEscape.gridPoint N i)
  let C := (1/Real.sqrt m)*(squared z/2)
  have ha := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => output_cap z _ (CircleEscape.grid_norm N i).le)
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hf : |(∑ i, f i)/(N:ℝ)| ≤ C := by
    rw [abs_div,abs_of_pos hn,div_le_iff₀ hn]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa [f,C,mul_comm] using ha
  change |mean z-b*((∑ i, f i)/(N:ℝ)-1)| ≤ _
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg hb]
  have hsub := abs_sub ((∑ i, f i)/(N:ℝ)) 1
  rw [abs_one] at hsub
  have hmul := mul_le_mul_of_nonneg_right hb' (abs_nonneg ((∑ i, f i)/(N:ℝ)-1))
  dsimp [C] at hf
  nlinarith [mean_cap z]

theorem radial_energy {τ : ℝ} (hlo : 1/2 ≤ τ) (hhi : τ ≤ 2) (z : State m) :
    kinetic τ z ≤ 2*squared z ∧ squared z ≤ 2*kinetic τ z := by
  constructor <;> simp only [kinetic,squared,Finset.mul_sum] <;> apply Finset.sum_le_sum <;> intro p _
  · have hp : (1/2:ℝ) ≤ rate τ p := by unfold rate; split <;> linarith
    rw [div_le_iff₀ (by linarith : 0 < rate τ p)]
    nlinarith [mul_nonneg (sq_nonneg (z p)) (sub_nonneg.mpr hp)]
  · have hp : 0 < rate τ p := by unfold rate; split <;> linarith
    have hu : rate τ p ≤ 2 := by unfold rate; split <;> linarith
    rw [← mul_div_assoc,le_div_iff₀ hp]
    nlinarith [mul_nonneg (sq_nonneg (z p)) (sub_nonneg.mpr hu)]

/-- Seedwise observable envelope at any finite time, across the complete
Gaussian support. Both mean and reference use the archived complex circle net. -/
theorem path_envelope {z : ℝ → State m} {τ T b : ℝ} (hN : 3 ≤ N) (hlo : 1/2 ≤ τ)
    (hhi : τ ≤ 2) (hT : 0 ≤ T) (hb : 0 ≤ b) (hb' : b ≤ 1)
    (F : IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) τ T z) :
    |mean (z T)-reference N m b (z 0)| ≤
      1 + (1/Real.sqrt m)*(3*squared (z 0)+3/2*T) := by
  have hr := (circle_path_bounds hN (by linarith) hhi hT F).1
  have he : squared (z T) ≤ 4*squared (z 0)+3*T := by
    linarith [(radial_energy hlo hhi (z T)).2,(radial_energy hlo hhi (z 0)).1]
  apply (abs_sub _ _).trans
  have hs := mul_le_mul_of_nonneg_left he (show 0 ≤ 1/Real.sqrt m by positivity)
  linarith [mean_cap (z T),reference_cap (z 0) (by omega : 0 < N) hb hb']


noncomputable def gaussianSquareNorm := lpNorm (fun x : ℝ => x^2) 4 (gaussianReal 0 1)

private theorem coordinate_square_mem (p : Coord m) :
    MemLp (fun ω : Seed m => ω p ^ 2) 4 (seedLaw m) := by
  have h := (memLp_id_gaussianReal' (μ:=0) (v:=1) 8 (by norm_num)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Coord m => gaussianReal 0 1) p)
  have : ENNReal.HolderTriple 8 8 4 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num⟩
  simpa [Function.comp_def,Pi.mul_def,pow_two,seedLaw] using (h.mul h : MemLp _ 4 _)

private theorem squared_mem : MemLp (squared (m:=m)) 4 (seedLaw m) :=
  memLp_finsetSum Finset.univ fun p _ => coordinate_square_mem p

theorem gaussian_energy_norm (m : ℕ) :
    lpNorm (squared (m:=m)) 4 (seedLaw m) ≤ (3*m : ℝ)*gaussianSquareNorm := by
  have hc (p : Coord m) : lpNorm (fun ω : Seed m => ω p^2) 4 (seedLaw m) = gaussianSquareNorm := by
    unfold lpNorm gaussianSquareNorm
    exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving
      (p:=4) (by fun_prop : AEStronglyMeasurable (fun q : ℝ => q^2) (gaussianReal 0 1))
      (measurePreserving_eval (fun _ : Coord m => gaussianReal 0 1) p))
  have h := lpNorm_sum_le (s:=Finset.univ) (fun p _ => coordinate_square_mem (m:=m) p)
    (by norm_num : (1:ENNReal) ≤ 4)
  rw [show squared (m:=m) = ∑ i : Coord m, (fun ω : Seed m => ω i^2) by funext ω; simp [squared]]
  simpa [hc,Fintype.card_prod,mul_comm] using h

private theorem mean_measurable : Measurable (mean (m:=m)) := by
  unfold mean CircleEscape.populationMean
  apply measurable_const.mul
  apply Finset.measurable_fun_sum
  intro j _
  have hw : Measurable fun ω : Seed m => (initial ω).w j := by
    change Measurable (fun ω : Seed m => (⟨ω (j,1),ω (j,2)⟩ : ℂ))
    have hp : Measurable (fun ω : Seed m => (ω (j,1),ω (j,2))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact Complex.equivRealProdCLM.symm.continuous.measurable.comp hp
  exact (measurable_pi_apply (j,0)).mul hw.norm

private theorem lp_const (c : ℝ) :
    lpNorm (fun _ : Seed m => c) 4 (seedLaw m) = |c| := by
  rw [lpNorm_const (by norm_num) (IsProbabilityMeasure.ne_zero _)]
  simp [measureReal_def]

private theorem lp_scale (c : ℝ) (f : Seed m → ℝ) :
    lpNorm (fun ω => c*f ω) 4 (seedLaw m) = |c| * lpNorm f 4 (seedLaw m) := by
  exact lpNorm_const_smul c f _

/-- Gaussian fourth moment of the actual flow/reference discrepancy. The
constant gaussianSquareNorm is universal; it is the fourth norm of G² for
one standard real Gaussian. Endpoint measurability follows, for example, by
evaluating any Borel whole-path selector. -/
theorem gaussian_flow_fourth {τ T b : ℝ} (hN : 3 ≤ N) (hlo : 1/2 ≤ τ) (hhi : τ ≤ 2)
    (hT : 0 ≤ T) (hb : 0 ≤ b) (hb' : b ≤ 1)
    (z : Seed m → ℝ → State m) (start : ∀ ω, z ω 0 = ω)
    (flow : ∀ ω, IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) τ T (z ω))
    (endpoint : Measurable fun ω => z ω T) :
    let Y := fun ω => mean (z ω T) - reference N m b ω
    MemLp Y 4 (seedLaw m) ∧ lpNorm Y 4 (seedLaw m) ≤
      1 + (1/Real.sqrt m)*((9*m : ℝ)*gaussianSquareNorm+3/2*T) := by
  let k : ℝ := 1/Real.sqrt m
  let e := squared (m:=m)
  let B := fun ω => 1+k*(3*e ω+3/2*T)
  let Z := reference N m b
  let Y := fun ω => mean (z ω T)-Z ω
  have hz := CircleSeedIntegrability.reference_memLp N m b 4 (by norm_num)
  have hy : AEStronglyMeasurable Y (seedLaw m) :=
    (mean_measurable.comp endpoint).aestronglyMeasurable.sub hz.aestronglyMeasurable
  have hB : MemLp B 4 (seedLaw m) := by
    exact (memLp_const 1).add (((squared_mem.const_mul 3).add (memLp_const (3/2*T))).const_mul k)
  have hdom (ω : Seed m) : ‖Y ω‖ ≤ B ω := by
    simpa [Y,Z,B,e,k,start,Real.norm_eq_abs] using path_envelope hN hlo hhi hT hb hb' (flow ω)
  have hnorm := lpNorm_mono_real hB hdom
  refine ⟨hB.mono' hy (.of_forall hdom), hnorm.trans ?_⟩
  have hk : 0 ≤ k := by dsimp [k]; positivity
  let a := fun ω => 3*e ω
  let f := fun ω => a ω + 3/2*T
  have ha : MemLp a 4 (seedLaw m) := squared_mem.const_mul 3
  have h1 : lpNorm B 4 (seedLaw m) ≤ 1+k*lpNorm f 4 (seedLaw m) := by
    have h := lpNorm_add_le (memLp_const (μ:=seedLaw m) (p:=4) (1:ℝ)) (g:=fun ω => k*f ω) (by norm_num)
    simpa [Pi.add_def,lp_const,lp_scale,abs_of_nonneg hk,B,f,a] using h
  have h2 : lpNorm f 4 (seedLaw m) ≤ 3*lpNorm e 4 (seedLaw m)+3/2*T := by
    have h := lpNorm_add_le ha (g:=fun _ => 3/2*T) (by norm_num)
    simpa [Pi.add_def,f,a,lp_scale,lp_const,abs_of_nonneg hT] using h
  have h3 := gaussian_energy_norm m
  change lpNorm e 4 (seedLaw m) ≤ _ at h3
  change lpNorm B 4 (seedLaw m) ≤ 1+k*_
  nlinarith [mul_le_mul_of_nonneg_left h2 hk,mul_le_mul_of_nonneg_left h3 hk]


private def neuronLength (z : State m) (j : Fin m) := Real.sqrt (∑ k : Fin 3, z (j,k)^2)

private theorem neuron_length_sq (z : State m) (j : Fin m) :
    neuronLength z j ^2 = ∑ k : Fin 3, z (j,k)^2 := Real.sq_sqrt (by positivity)

private theorem pieces_le (z : State m) (j : Fin m) :
    |(initial z).a j| ≤ neuronLength z j ∧ ‖(initial z).w j‖ ≤ neuronLength z j := by
  have hlen := neuron_length_sq z j
  rw [Fin.sum_univ_three] at hlen
  have hpos : 0 ≤ neuronLength z j := Real.sqrt_nonneg _
  have hsq := hidden_sq z j
  change |z (j,0)| ≤ _ ∧ _
  constructor
  · nlinarith [sq_abs (z (j,0)),abs_nonneg (z (j,0)),sq_nonneg (z (j,1)),sq_nonneg (z (j,2))]
  · nlinarith [norm_nonneg ((initial z).w j), sq_nonneg (z (j,0))]

private theorem sum_length_sq (z : State m) : ∑ j, neuronLength z j ^2 = squared z := by
  simp_rw [neuron_length_sq]
  rw [squared,Fintype.sum_prod_type]

/-- Population mean movement uses Cauchy-Schwarz across the neurons, retaining
the width normalization and the actual distance traveled from initialization. -/
theorem mean_movement (z q : State m) :
    |mean q-mean z| ≤ (1/Real.sqrt m)*
      (2*Real.sqrt (squared z)*Real.sqrt (squared (q-z))+squared (q-z)) := by
  let δ := q-z
  have each (j : Fin m) :
      |(initial q).a j*‖(initial q).w j‖-(initial z).a j*‖(initial z).w j‖| ≤
      2*(neuronLength z j*neuronLength δ j)+neuronLength δ j^2 := by
    let a := (initial z).a j
    let d := (initial δ).a j
    let w := (initial z).w j
    let u := (initial δ).w j
    have ea : (initial q).a j = a+d := by dsimp [initial,a,d,δ]; ring
    have ew : (initial q).w j = w+u := by apply Complex.ext <;> dsimp [initial,w,u,δ] <;> ring
    have hA := (pieces_le z j).1
    have hW := (pieces_le z j).2
    have hD := (pieces_le δ j).1
    have hU := (pieces_le δ j).2
    have hpos : 0 ≤ neuronLength z j := Real.sqrt_nonneg _
    have dpos : 0 ≤ neuronLength δ j := Real.sqrt_nonneg _
    change |a| ≤ _ at hA
    change ‖w‖ ≤ _ at hW
    change |d| ≤ _ at hD
    change ‖u‖ ≤ _ at hU
    rw [ea,ew]
    change |(a+d)*‖w+u‖-a*‖w‖| ≤ _
    rw [show (a+d)*‖w+u‖-a*‖w‖=a*(‖w+u‖-‖w‖)+d*‖w+u‖ by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_norm]
    have hdist : |‖w+u‖-‖w‖| ≤ neuronLength δ j := by
      exact (abs_norm_sub_norm_le _ _).trans (by simpa using hU)
    have hsum := (norm_add_le w u).trans (add_le_add hW hU)
    nlinarith [mul_le_mul hA hdist (abs_nonneg _) hpos,
      mul_le_mul hD hsum (norm_nonneg _) dpos]
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (s:=Finset.univ) fun j _ => each j)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,sum_length_sq] at hs
  have cs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (neuronLength z) (neuronLength δ)
  rw [sum_length_sq,sum_length_sq] at cs
  have normed := hs.trans (add_le_add_left (mul_le_mul_of_nonneg_left cs (by norm_num : (0:ℝ) ≤ 2)) _)
  rw [mean,mean,CircleEscape.populationMean,CircleEscape.populationMean,← mul_sub,← Finset.sum_sub_distrib,abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (1/Real.sqrt m)/Real.pi)]
  have hpi := div_le_self (show 0 ≤ 1/Real.sqrt m by positivity) (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)
  rw [mul_assoc 2]
  exact mul_le_mul hpi normed (abs_nonneg _) (by positivity)

/-- A useful envelope linear in initial empirical loss and in mean squared
initial parameter norm. These two Gaussian quantities have uniform fourth
norms by initial moment estimates. -/
theorem sharp_path_envelope {z : ℝ → State m} {τ T : ℝ} (hm : 0 < m)
    (hlo : 0 < τ) (hhi : τ ≤ 2) (hT : 0 ≤ T)
    (F : IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) τ T z) :
    let L := loss (residual (circleInput N) (circleLabel N) (1/Real.sqrt m) (z 0))
    |mean (z T)-mean (z 0)| ≤ Real.sqrt (2*T)*(squared (z 0)/m+L) + (2*T/Real.sqrt m)*L := by
  let L := loss (residual (circleInput N) (circleLabel N) (1/Real.sqrt m) (z 0))
  have lp : 0 ≤ L := by dsimp [L,loss]; positivity
  have sz : 0 ≤ squared (z 0) := by unfold squared; positivity
  have hw := euclidean_displacement hlo hhi hT F
  change squared (z T-z 0) ≤ 2*T*L at hw
  have hd := Real.sqrt_le_sqrt hw
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2*T)] at hd
  have h := mean_movement (z 0) (z T)
  apply h.trans
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hr := Real.sqrt_pos.mpr hm'
  have hnorm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*√(squared (z 0)) by positivity)
  have bound := mul_le_mul_of_nonneg_left (add_le_add hnorm hw) (show 0 ≤ 1/√(m:ℝ) by positivity)
  apply bound.trans
  have young := sq_nonneg (√(squared (z 0))/√(m:ℝ)-√L)
  have hscaled : (√(squared (z 0))/√(m:ℝ))^2 = squared (z 0)/m := by
    rw [div_pow,Real.sq_sqrt sz,Real.sq_sqrt hm'.le]
  have aux : 2*(√(squared (z 0))/√(m:ℝ))*√L ≤ squared (z 0)/m+L := by
    nlinarith [Real.sq_sqrt lp]
  have mult := mul_le_mul_of_nonneg_left aux (Real.sqrt_nonneg (2*T))
  change _ ≤ √(2*T)*(squared (z 0)/m+L)+(2*T/√(m:ℝ))*L
  convert add_le_add_left mult (2*T/√(m:ℝ)*L) using 1
  ring


def initialLoss (N m : ℕ) (ω : Seed m) :=
  loss (CircleFlowPath.residual (circleInput N) (circleLabel N) (1/Real.sqrt m) ω)

def outputConstant : ℝ := (CircleInitializationConcentration.standardEighth^2)^(8:ℝ)⁻¹

def lossConstant : ℝ := (outputConstant+2)^2/2

private theorem circle_label_abs (N : ℕ) (i : Fin N) : |circleLabel N i| ≤ 2 := by
  have h := Complex.abs_re_le_norm (CircleEscape.gridPoint N i)
  rw [CircleEscape.grid_norm] at h
  change |1+(CircleEscape.gridPoint N i).re| ≤ 2
  linarith [abs_add_le (1:ℝ) (CircleEscape.gridPoint N i).re,abs_one (α:=ℝ)]

private theorem initial_output_norm (hm : 0 < m) (i : Fin N) :
    lpNorm (fun ω : Seed m => output (1/Real.sqrt m) ω (circleInput N i)) 8 (seedLaw m) ≤
      outputConstant := by
  have h := CircleInitializationConcentration.output_lpNorm_eight hm (circleInput N i)
  have h1 : (circleInput N i).1 ^ 2 + (circleInput N i).2 ^ 2 = 1 := by
    have hn := Complex.sq_norm (CircleEscape.gridPoint N i)
    rw [CircleEscape.grid_norm,Complex.normSq_apply] at hn
    change (CircleEscape.gridPoint N i).re ^2 + (CircleEscape.gridPoint N i).im ^2 = 1
    nlinarith
  simpa [h1,outputConstant] using h

private theorem square_norm {f : Seed m → ℝ} (hf : MemLp f 8 (seedLaw m)) :
    lpNorm (fun ω => (f ω)^2) 4 (seedLaw m) = (lpNorm f 8 (seedLaw m))^2 := by
  have he := congrArg ENNReal.toReal (eLpNorm_norm_rpow (p:=4) f hf.aestronglyMeasurable (by norm_num : 0 < (2:ℝ)))
  norm_num [lpNorm,ENNReal.toReal_rpow,Real.norm_eq_abs,sq_abs] at he ⊢
  exact he

theorem initial_loss_fourth {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    MemLp (initialLoss N m) 4 (seedLaw m) ∧ lpNorm (initialLoss N m) 4 (seedLaw m) ≤ lossConstant := by
  let f := fun (i : Fin N) (ω : Seed m) => output (1/Real.sqrt m) ω (circleInput N i)
  let r := fun (i : Fin N) (ω : Seed m) => f i ω-circleLabel N i
  let s := fun (i : Fin N) (ω : Seed m) => (r i ω)^2
  have hf (i : Fin N) : MemLp (f i) 8 (seedLaw m) := CircleInitializationConcentration.output_memLp_eight _ _
  have hr (i : Fin N) : MemLp (r i) 8 (seedLaw m) := (hf i).sub (memLp_const _)
  have hh : ENNReal.HolderTriple 8 8 4 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num⟩
  have hs (i : Fin N) : MemLp (s i) 4 (seedLaw m) := by
    simpa [s,Pi.mul_def,pow_two] using ((hr i).mul (hr i) : MemLp _ 4 _)
  have bound (i : Fin N) : lpNorm (s i) 4 (seedLaw m) ≤ (outputConstant+2)^2 := by
    have ht := lpNorm_sub_le (hf i) (g:=fun _ => circleLabel N i) (by norm_num)
    have hc : lpNorm (fun _ : Seed m => circleLabel N i) 8 (seedLaw m) = |circleLabel N i| := by
      rw [lpNorm_const (by norm_num) (IsProbabilityMeasure.ne_zero _)]
      simp [measureReal_def]
    rw [hc] at ht
    have hb := ht.trans (add_le_add (initial_output_norm hm i) (circle_label_abs N i))
    exact (square_norm (hr i)).le.trans (pow_le_pow_left₀ lpNorm_nonneg hb _)
  let k : ℝ := 1/(2*N)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have he : initialLoss N m = fun ω => k*((∑ i, s i) ω) := by
    funext ω
    simp [initialLoss,loss,CircleFlowPath.residual,f,r,s,k]
  rw [he]
  have hsum : MemLp (∑ i, s i) 4 (seedLaw m) := by
    convert memLp_finsetSum Finset.univ (fun (i : Fin N) _ => hs i) using 1
    ext ω
    simp
  refine ⟨hsum.const_mul _,?_⟩
  rw [lp_scale,abs_of_nonneg hk]
  have hsum' := (lpNorm_sum_le (s:=Finset.univ) (fun i _ => hs i) (by norm_num)).trans
    (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => bound i))
  apply (mul_le_mul_of_nonneg_left hsum' hk).trans
  simp [k,lossConstant]
  field_simp
  rfl

private theorem output_eq_complex (z : State m) (i : Fin N) :
    output (1/Real.sqrt m) z (circleInput N i) =
    CircleEscape.output (1/Real.sqrt m) (initial z) (CircleEscape.gridPoint N i) := by
  simp [output,CircleEscape.output,CircleEscape.feature,pre,circleInput,initial,Complex.inner,Complex.mul_re]

private theorem reference_gap (hN : 0 < N) (z : State m) {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1) :
    |mean z-reference N m b z| ≤ 7/2+initialLoss N m z := by
  let f := fun i => output (1/Real.sqrt m) z (circleInput N i)
  let r := fun i => f i-circleLabel N i
  have hbnd (i : Fin N) : |f i| ≤ 5/2+(r i)^2/2 := by
    have e : f i = r i+circleLabel N i := by simp [r]
    have a := abs_add_le (r i) (circleLabel N i)
    rw [← e] at a
    nlinarith [circle_label_abs N i,sq_nonneg (|r i|-1),sq_abs (r i)]
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hsum := (Finset.abs_sum_le_sum_abs f Finset.univ).trans (Finset.sum_le_sum (s:=Finset.univ) fun i _ => hbnd i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  rw [← Finset.sum_div] at hsum
  have hf : |(∑ i, f i)/N| ≤ 5/2+initialLoss N m z := by
    rw [abs_div,abs_of_pos hn,div_le_iff₀ hn]
    change _ ≤ (5/2+1/(2*(N:ℝ))*(∑ i, r i^2))*N
    calc
      _ ≤ _ := hsum
      _ = _ := by
        generalize (∑ i, r i^2) = S
        field_simp
  change |mean z - (mean z - b*((∑ i, CircleEscape.output _ _ _)/N-1))| ≤ _
  simp_rw [← output_eq_complex]
  change |mean z-(mean z-b*((∑ i, f i)/N-1))| ≤ _
  rw [sub_sub_cancel,abs_mul,abs_of_nonneg hb]
  apply (mul_le_mul_of_nonneg_right hb' (abs_nonneg _)).trans
  rw [one_mul]
  linarith [abs_sub ((∑ i, f i)/N) 1,abs_one (α:=ℝ)]


/-- The same-seed flow/reference fourth norm is width-uniform at fixed time.
The constants use only the standard real Gaussian law. -/
theorem gaussian_flow_fourth_sharp {τ T b : ℝ} (hN : 0 < N) (hm : 0 < m) (hτ : 0 < τ) (hhi : τ ≤ 2)
    (hT : 0 ≤ T) (hb : 0 ≤ b) (hb' : b ≤ 1)
    (z : Seed m → ℝ → State m) (start : ∀ ω, z ω 0 = ω)
    (flow : ∀ ω, IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) τ T (z ω))
    (endpoint : Measurable fun ω => z ω T) :
    let Y := fun ω => mean (z ω T) - reference N m b ω
    MemLp Y 4 (seedLaw m) ∧ lpNorm Y 4 (seedLaw m) ≤
      7/2 + 3*Real.sqrt (2*T)*gaussianSquareNorm +
      (1+Real.sqrt (2*T)+2*T/Real.sqrt m)*lossConstant := by
  let a := Real.sqrt (2*T)/(m:ℝ)
  let b₁ := 1+Real.sqrt (2*T)+2*T/Real.sqrt m
  let E := squared (m:=m)
  let L := initialLoss N m
  let Y := fun ω => mean (z ω T) - reference N m b ω
  let A := fun ω => a*E ω
  let B := fun ω => b₁*L ω
  let K := fun ω => (7/2+A ω)+B ω
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb₁ : 0 ≤ b₁ := by dsimp [b₁]; positivity
  have hL := initial_loss_fourth hN hm
  have hA : MemLp A 4 (seedLaw m) := squared_mem.const_mul _
  have hB : MemLp B 4 (seedLaw m) := hL.1.const_mul _
  have hC : MemLp (fun ω => 7/2+A ω) 4 (seedLaw m) := (memLp_const (7/2:ℝ)).add hA
  have hK : MemLp K 4 (seedLaw m) := hC.add hB
  have hdom (ω : Seed m) : ‖Y ω‖ ≤ K ω := by
    have h1 := sharp_path_envelope hm hτ hhi hT (flow ω)
    dsimp only at h1
    rw [start] at h1
    have h2 := reference_gap hN ω hb hb'
    have h3 := abs_add_le (mean (z ω T)-mean ω) (mean ω-reference N m b ω)
    rw [sub_add_sub_cancel] at h3
    change |mean (z ω T)-reference N m b ω| ≤ (7/2+a*E ω)+b₁*L ω
    change _ ≤ Real.sqrt (2*T)*(E ω/m+L ω)+(2*T/Real.sqrt m)*L ω at h1
    change _ ≤ 7/2+L ω at h2
    dsimp only [a,b₁]
    calc
      _ ≤ _ := h3.trans (add_le_add h1 h2)
      _ = _ := by ring
  have hy : AEStronglyMeasurable Y (seedLaw m) := (mean_measurable.comp endpoint).aestronglyMeasurable.sub
    (CircleSeedIntegrability.reference_memLp N m b 4 (by norm_num)).aestronglyMeasurable
  refine ⟨hK.mono' hy (.of_forall hdom),(lpNorm_mono_real hK hdom).trans ?_⟩
  have h1 := lpNorm_add_le hC (g:=B) (by norm_num)
  have h2 := lpNorm_add_le (memLp_const (p:=4) (μ:=seedLaw m) (7/2:ℝ)) (g:=A) (by norm_num)
  change lpNorm K 4 _ ≤ lpNorm (fun ω => 7/2 + A ω) 4 _ + lpNorm B 4 _ at h1
  change lpNorm (fun ω => 7/2 + A ω) 4 _ ≤ _ at h2
  rw [lp_const] at h2
  have he := gaussian_energy_norm m
  change lpNorm E 4 _ ≤ _ at he

  have hA' : lpNorm A 4 (seedLaw m) ≤ 3*Real.sqrt (2*T)*gaussianSquareNorm := by
    rw [show lpNorm A 4 (seedLaw m) = a*lpNorm E 4 (seedLaw m) by rw [← abs_of_nonneg ha]; exact lp_scale a E]
    apply (mul_le_mul_of_nonneg_left he ha).trans
    have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    dsimp [a]
    field_simp
    rfl
  have hB' : lpNorm B 4 (seedLaw m) ≤ b₁*lossConstant := by
    rw [show lpNorm B 4 (seedLaw m) = b₁*lpNorm L 4 (seedLaw m) by rw [← abs_of_nonneg hb₁]; exact lp_scale b₁ L]
    exact mul_le_mul_of_nonneg_left hL.2 hb₁
  change lpNorm K 4 (seedLaw m) ≤ 7/2+3*Real.sqrt (2*T)*gaussianSquareNorm+b₁*lossConstant
  norm_num at h2
  linarith

end CircleFlowMoments

