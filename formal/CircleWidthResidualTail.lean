module

public import CircleSharpInitialization
import all CircleSharpInitialization
import all CircleInitializationConcentration
import all CircleTangentDrift
import all CircleFlowPath
import all CircleGaussianTracking
import all CircleKernelIdentification
import Mathlib.Tactic

/-! A two-sided Gaussian-initialization tail for the initial RMS residual. -/
public section
noncomputable section
namespace CircleWidthResidualTail
open Real MeasureTheory ProbabilityTheory CircleEscapeBridge CircleInitializationConcentration
  CircleKernelIdentification CircleGaussianBernstein CircleGaussianTracking CircleTangentDrift CircleFlowPath
  CircleSharpInitialization

private def radial (w : ℝ×ℝ) := exp ((w.1^2+w.2^2)/4)

private theorem radial_mean : (∫ w, radial w ∂standardPair)=2 := by
  have scalar : (∫ x : ℝ, exp (x^2/4) ∂gaussianReal 0 1) = sqrt 2 := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal)≠0)]
    have row (x : ℝ) : gaussianPDFReal 0 1 x • exp (x^2/4) =
        (1/sqrt (2*π))*exp (-(1/4:ℝ)*x^2) := by
      simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,smul_eq_mul]
      rw [mul_assoc,←exp_add]; congr 2 <;> ring
    simp_rw [row]
    rw [integral_const_mul,integral_gaussian,one_div,mul_comm,←div_eq_mul_inv,←sqrt_div (by positivity)]
    congr 1; field_simp; ring
  have split (w : ℝ×ℝ) : radial w = exp (w.1^2/4)*exp (w.2^2/4) := by rw [radial,add_div,exp_add]
  simp_rw [split]
  rw [standardPair,integral_prod_mul (fun a : ℝ => exp (a^2/4)) (fun a : ℝ => exp (a^2/4)),
    scalar,←sq,sq_sqrt (by norm_num)]

private theorem neuron_mgf (x : ℝ×ℝ) (hx : UnitInput x) (t : ℝ) (small : t^2 ≤ 1/2) :
    Integrable (fun z => exp (t*outputAtom x z)) atomLaw ∧
    mgf (outputAtom x) atomLaw t ≤ exp (2*t^2) := by
  let h (w : ℝ×ℝ) := max (x.1*w.1+x.2*w.2) 0
  let f (z : ℝ×(ℝ×ℝ)) := exp ((t*h z.2)*z.1)
  have row (w : ℝ×ℝ) : (∫ a, f (a,w) ∂gaussianReal 0 1) = exp ((t*h w)^2/2) := by
    change mgf (fun a : ℝ => a) (gaussianReal 0 1) (t*h w) = _
    rw [mgf_fun_id_gaussianReal]; simp
  have proj (w : ℝ×ℝ) : (h w)^2 ≤ w.1^2+w.2^2 := by
    unfold UnitInput at hx
    have q := mul_le_mul_of_nonneg_right hx (show 0≤w.1^2+w.2^2 by positivity)
    dsimp [h]; rcases max_cases (x.1*w.1+x.2*w.2) 0 with ⟨e,_⟩ | ⟨e,_⟩ <;> rw [e]
    · nlinarith [sq_nonneg (x.1*w.2-x.2*w.1)]
    · nlinarith [sq_nonneg w.1,sq_nonneg w.2]
  let g (w : ℝ×ℝ) := (1-2*t^2) + (2*t^2)*radial w
  have gI : Integrable g standardPair := (integrable_const _).add
    ((Integrable.of_integral_ne_zero (radial_mean.trans_ne (by norm_num))).const_mul _)
  have bound (w : ℝ×ℝ) : exp ((t*h w)^2/2) ≤ g w := by
    have e := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ ((w.1^2+w.2^2)/4))
      (show 0≤1-2*t^2 by linarith) (show 0≤2*t^2 by positivity) (show (1-2*t^2)+2*t^2=1 by ring)
    simp only [smul_eq_mul,mul_zero,zero_add,exp_zero,mul_one] at e
    apply le_trans (b:=exp ((2*t^2)*((w.1^2+w.2^2)/4))) _ e
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (proj w) (sq_nonneg t)]
  have h_meas : Measurable (fun w => exp ((t*h w)^2/2)) := by dsimp [h]; fun_prop
  have him := gI.mono' h_meas.aestronglyMeasurable (ae_of_all _ fun w => by
    simpa only [Real.norm_eq_abs,abs_of_pos (exp_pos _)] using bound w)
  have fI : Integrable f ((gaussianReal 0 1).prod standardPair) := by
    apply (integrable_prod_iff' (show Measurable f by dsimp [f,h]; fun_prop).aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun w => integrable_exp_mul_gaussianReal (t*h w)
    · have eq (a : ℝ) (w : ℝ×ℝ) : ‖f (a,w)‖=f (a,w) := norm_of_nonneg (exp_nonneg _)
      simpa only [eq,row] using him
  have eq (z : Atom) : exp (t*outputAtom x z)=f (readoutSplit z) := by
    change exp (t*(z 0*max (x.1*z 1+x.2*z 2) 0)) = exp ((t*max (x.1*z 1+x.2*z 2) 0)*z 0)
    congr 1; ring
  constructor
  · simp_rw [eq]; exact readoutSplit_preserving.integrable_comp_of_integrable fI
  · unfold mgf
    simp_rw [eq]
    rw [readoutSplit_preserving.integral_comp' f,integral_prod_symm f fI]
    simp_rw [row]
    apply (integral_mono him gI bound).trans
    have rI : Integrable radial standardPair := .of_integral_ne_zero (radial_mean.trans_ne (by norm_num))
    dsimp [g]; rw [integral_add (integrable_const _) (rI.const_mul _),integral_const,integral_const_mul,radial_mean]
    simp only [probReal_univ,smul_eq_mul,one_mul]
    linarith [Real.add_one_le_exp (2*t^2)]

private theorem prediction_tail {m : ℕ} (hm : 0<m) (x : ℝ×ℝ) (hx : UnitInput x) {d : ℝ}
    (hd : 0≤d) (hs : d≤m) :
    (seedLaw m).real {z | sqrt (8*d) ≤ |CircleFlowPath.output (1/sqrt m) z x|} ≤ 2*exp (-d) := by
  let u := sqrt (8*d)/sqrt m
  let t := u/4
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have rp : 0<sqrt (m:ℝ) := sqrt_pos.mpr mp
  have us : u^2=(8*d)/m := by simp only [u,div_pow,sq_sqrt (show 0≤8*d by positivity),sq_sqrt mp.le]
  have small : t^2 ≤ 1/2 := by
    rw [show t^2=u^2/16 by dsimp [t];ring,us]; apply (div_le_iff₀ (by norm_num : (0:ℝ)<16)).2
    rw [div_le_iff₀ mp]; linarith
  have tp : 0≤t := by dsimp [t,u]; positivity
  have meas : Measurable (outputAtom x) := by unfold outputAtom; fun_prop
  have plus := neuron_mgf x hx t small
  have minus := neuron_mgf x hx (-t) (by simpa using small)
  have hp := empirical_chernoff hm _ meas (u:=u) tp plus.1 plus.2
  have en (z : Atom) : exp (t*(-outputAtom x z))=exp ((-t)*outputAtom x z) := by rw [mul_neg,neg_mul]
  have negI : Integrable (fun z => exp (t*(-outputAtom x z))) atomLaw := by simpa only [en] using minus.1
  have negM : mgf (fun z => -outputAtom x z) atomLaw t ≤ exp (2*t^2) := by
    simpa only [mgf,en,neg_sq] using minus.2
  have hn := empirical_chernoff hm _ meas.neg (u:=u) tp negI negM
  have scale (ω : Seed m) : sampleAverage (outputAtom x) ω =
      CircleFlowPath.output (1/sqrt m) ω x / sqrt m := by
    unfold sampleAverage CircleFlowPath.output CircleFlowPath.pre outputAtom
    field_simp; rw [sq_sqrt (by positivity),mul_comm]
  have neg (ω : Seed m) : sampleAverage (fun z => -outputAtom x z) ω = -sampleAverage (outputAtom x) ω := by
    simp [sampleAverage]
  have sub : {z : Seed m | sqrt (8*d) ≤ |CircleFlowPath.output (1/sqrt m) z x|} ⊆
    {z | u≤sampleAverage (outputAtom x) z} ∪ {z | u≤sampleAverage (fun a => -outputAtom x a) z} := by
    intro z hz
    change sqrt (8*d) ≤ |CircleFlowPath.output (1/sqrt m) z x| at hz
    rcases le_abs.mp hz with p|p
    · exact Or.inl (by change u≤_; rw [scale]; exact div_le_div_of_nonneg_right p rp.le)
    · exact Or.inr (by change u≤_; rw [neg,scale,←neg_div]; exact div_le_div_of_nonneg_right p rp.le)
  have power : (m:ℝ)*(2*t^2-t*u) = -d := by
    rw [show 2*t^2-t*u= -u^2/8 by dsimp [t];ring,us]; field_simp
  rw [power] at hp hn
  apply (measureReal_mono sub).trans ((measureReal_union_le _ _).trans _)
  exact (add_le_add hp hn).trans_eq (by ring)

/-- Initial residual failure at the finite-width concentration threshold. -/
theorem initial_residual {N m : ℕ} (hN : 0<N) (hm : 0<m) {d : ℝ} (hd : 0≤d) (hs : d≤m) :
    (seedLaw m).real {z | 2+sqrt (8*d) < initialRms N m z} ≤ 2*N*exp (-d) := by
  let R := sqrt (8*d)
  have hR : 0≤R := sqrt_nonneg _
  let B (i : Fin N) := {ω : Seed m | R ≤ |CircleFlowPath.output (1/sqrt m) ω (circleInput N i)|}
  have sub : {ω : Seed m | 2+R < initialRms N m ω} ⊆ ⋃ i, B i := by
    intro ω hw
    by_contra h
    have bound (i : Fin N) : |CircleFlowPath.output (1/sqrt m) ω (circleInput N i)| ≤ R :=
      (lt_of_not_ge (fun hi => h (Set.mem_iUnion_of_mem i hi))).le
    let r := residual (circleInput N) (circleLabel N) (1/sqrt m) ω
    have hr (i : Fin N) : r i ^2 ≤ (2+R)^2 := by
      have hsub : |r i| ≤ 2+R := (abs_sub ..).trans ((add_le_add (bound i)
        (CircleFlowMoments.circle_label_abs N i)).trans_eq (add_comm _ _))
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hsub 2
    have sqb : initialRms N m ω ^2 ≤ (2+R)^2 := by
      change ‖rmsCoordinates r‖^2 ≤ _
      rw [rmsCoordinates_norm_sq,div_le_iff₀ (show 0 < (N:ℝ) by exact_mod_cast hN)]
      simpa [mul_comm] using Finset.sum_le_sum (fun (i:Fin N) (_:i ∈ Finset.univ) => hr i)
    exact (not_lt_of_ge ((sq_le_sq₀ (norm_nonneg _) (by linarith)).1 sqb)) hw
  refine (measureReal_mono sub).trans ((measureReal_iUnion_fintype_le B).trans
    ((Finset.sum_le_sum (fun i _ => prediction_tail hm _ (grid_unit i) hd hs)).trans_eq ?_))
  simp; ring

end CircleWidthResidualTail
