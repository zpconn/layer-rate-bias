module

public import CircleGridSpectrum
public import CircleInitializationConcentration
import all CircleGridSpectrum
import all CircleKernelIdentification
import all CircleSpectrum
import all CircleInitializationConcentration
import all CircleEscapeBridge
import all CircleEscape
import Mathlib.Tactic

/-! Exact finite-width first and second moments of the actual same-seed circle
interpolation reference. The output weights are centered independent normals;
the covariance of the hidden sample is the grid alias of the ReLU kernel. -/

public section
noncomputable section
namespace CircleReferenceMoments
open CircleGridSpectrum CircleKernelIdentification CircleInitializationConcentration
  CircleEscape CircleEscapeBridge CircleSpectrum MeasureTheory ProbabilityTheory Real Finset

abbrev G := gaussianReal 0 1
private def split : Atom ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)
private theorem split_preserving : MeasurePreserving split atomLaw (G.prod standardPair) :=
  ((MeasurePreserving.id G).prod (measurePreserving_finTwoArrow G)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => G) 0)
private theorem split_apply (z : Atom) : split z = (z 0,z 1,z 2) := rfl

private def phi (u : ℝ) (w : ℝ×ℝ) := max (projection u w) 0
private def gridFeature (N : ℕ) (w : ℝ×ℝ) := (∑ i : Fin N, phi (physicalAngle i) w)/N
private def coeff (N : ℕ) (b : ℝ) (w : ℝ×ℝ) := populationFeature w-b*gridFeature N w
private def atom (N : ℕ) (b : ℝ) (z : Atom) := z 0*coeff N b (z 1,z 2)

private theorem coord_mem (p : NNReal) :
    MemLp (fun w : ℝ×ℝ => w.1) (p:ENNReal) standardPair ∧
    MemLp (fun w : ℝ×ℝ => w.2) (p:ENNReal) standardPair :=
  ⟨(memLp_id_gaussianReal p).comp_measurePreserving measurePreserving_fst,
   (memLp_id_gaussianReal p).comp_measurePreserving measurePreserving_snd⟩

private theorem phi_mem (p : NNReal) (u : ℝ) : MemLp (phi u) (p:ENNReal) standardPair :=
  (((coord_mem p).1.mul_const (cos u)).add ((coord_mem p).2.mul_const (sin u))).pos_part

private theorem pop_mem (p : NNReal) : MemLp populationFeature (p:ENNReal) standardPair := by
  have h := (((coord_mem p).1.norm.add (coord_mem p).2.norm).mul_const π⁻¹)
  apply h.mono' (by unfold populationFeature; fun_prop)
  filter_upwards with w
  change ‖√(w.1^2+w.2^2)/π‖ ≤ (‖w.1‖+‖w.2‖)*π⁻¹
  rw [Real.norm_of_nonneg (by positivity),div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  rw [Real.norm_eq_abs,Real.norm_eq_abs]
  nlinarith [abs_mul_abs_self w.1,abs_mul_abs_self w.2,mul_nonneg (abs_nonneg w.1) (abs_nonneg w.2)]


private theorem grid_mem (N : ℕ) (p : NNReal) : MemLp (gridFeature N) (p:ENNReal) standardPair := by
  unfold gridFeature
  simpa only [div_eq_mul_inv] using (memLp_finsetSum univ
    (fun (i:Fin N) _ => phi_mem p (physicalAngle i))).mul_const (N:ℝ)⁻¹
private theorem coeff_mem (N : ℕ) (b : ℝ) (p : NNReal) : MemLp (coeff N b) (p:ENNReal) standardPair :=
  (pop_mem p).sub ((grid_mem N p).const_mul b)
private theorem atom_mem (N : ℕ) (b : ℝ) : MemLp (atom N b) 2 atomLaw := by
  have ha : MemLp (fun z : ℝ×(ℝ×ℝ) => z.1) 4 (G.prod standardPair) :=
    (memLp_id_gaussianReal 4).comp_measurePreserving measurePreserving_fst
  have hc : MemLp (fun z : ℝ×(ℝ×ℝ) => coeff N b z.2) 4 (G.prod standardPair) :=
    (coeff_mem N b 4).comp_measurePreserving measurePreserving_snd
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num⟩
  have hm : MemLp (fun z : ℝ×(ℝ×ℝ) => z.1*coeff N b z.2) 2 (G.prod standardPair) := ha.fun_mul hc
  exact hm.comp_measurePreserving split_preserving

private theorem atom_mean (N : ℕ) (b : ℝ) : (∫ z, atom N b z ∂atomLaw)=0 := by
  change (∫ z, (fun p : ℝ×(ℝ×ℝ) => p.1*coeff N b p.2) (split z) ∂atomLaw)=0
  rw [split_preserving.integral_comp' (fun p : ℝ×(ℝ×ℝ) => p.1*coeff N b p.2),integral_prod_mul (fun a : ℝ => a) (coeff N b),integral_id_gaussianReal,zero_mul]

private theorem atom_variance (N : ℕ) (b : ℝ) :
    ProbabilityTheory.variance (atom N b) atomLaw = ∫ w, coeff N b w ^ 2 ∂standardPair := by
  rw [variance_eq_sub (atom_mem N b),atom_mean]
  simp only [Pi.pow_apply,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,sub_zero]
  change (∫ z, (fun p : ℝ×(ℝ×ℝ) => (p.1*coeff N b p.2)^2) (split z) ∂atomLaw)=_
  rw [split_preserving.integral_comp' (fun p : ℝ×(ℝ×ℝ) => (p.1*coeff N b p.2)^2)]
  simp_rw [mul_pow]
  rw [integral_prod_mul (fun a : ℝ => a^2) (fun w => coeff N b w ^2),CircleKernelIdentification.gaussian_second,one_mul]

private theorem mixed_integrable {f g : ℝ×ℝ → ℝ} (hf : MemLp f ((2:NNReal):ENNReal) standardPair)
    (hg : MemLp g ((2:NNReal):ENNReal) standardPair) : Integrable (fun w => f w*g w) standardPair := by
  norm_num at hf hg
  exact hf.integrable_mul hg

private theorem grid_second {n : ℕ} (hn : 3≤n+1) (ho : Odd (n+1)) :
    (∫ w, gridFeature (n+1) w ^2 ∂standardPair) = c0+S n := by
  let N := n+1
  let F (i : Fin N) := phi (physicalAngle i)
  have hcov (i j : Fin N) : (∫ w, F i w*F j w ∂standardPair)=sampledMatrix 0 i j := by
    rw [sampledMatrix_cartesian]
    simp [cartesianKernel,cartesianProduct,F,phi]
  have hprod (i j : Fin N) : Integrable (fun w => F i w*F j w) standardPair :=
    mixed_integrable (phi_mem 2 _) (phi_mem 2 _)
  have hsq (w : ℝ×ℝ) : gridFeature N w ^2 = (∑ j : Fin N, ∑ i : Fin N, F i w*F j w)/(N:ℝ)^2 := by
    rw [gridFeature,div_pow,sq,Finset.mul_sum]
    simp only [Finset.sum_mul,F]
  change ∫ w, gridFeature N w^2 ∂standardPair = _
  simp_rw [hsq,integral_div,integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hprod i j)),
    integral_finsetSum _ (fun i _ => hprod i _),hcov]
  have hd (j : Fin N) := sampled_column 0 (by norm_num) (by norm_num) j
  have hn0 : (N:ℝ)≠0 := by dsimp [N]; positivity
  have hc (j : Fin N) : ∑ i : Fin N, sampledMatrix 0 i j = aliasValue (tangentCoeff 0) (0:ZMod N)*N :=
    (div_eq_iff hn0).mp (hd j)
  simp_rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [show (N:ℝ)*(aliasValue (tangentCoeff 0) (0:ZMod N)*N)/(N:ℝ)^2 = aliasValue (tangentCoeff 0) (0:ZMod N) by field_simp]
  rw [constant_alias_eq hn ho 0 (by norm_num) (by norm_num), S_eq_alias_sum]
  simp [k0,c0,ntkEven,covEven]

private theorem grid_mixed {N : ℕ} (hn : 0<N) :
    (∫ w, populationFeature w *gridFeature N w ∂standardPair) = c0 := by
  have prod (i : Fin N) : Integrable (fun w => populationFeature w*phi (physicalAngle i) w) standardPair :=
    mixed_integrable (pop_mem 2) (phi_mem 2 _)
  simp_rw [gridFeature,←mul_div_assoc,Finset.mul_sum,integral_div,integral_finsetSum _ (fun i _ => prod i),phi,populationFeature_mixed]
  simp [Nat.ne_of_gt hn]

private theorem coeff_second {n : ℕ} (hn : 3≤n+1) (ho : Odd (n+1)) (b : ℝ) :
    (∫ w, coeff (n+1) b w ^2 ∂standardPair) = c0*(1-b)^2+b^2*S n := by
  let N := n+1
  let C := populationFeature
  let D := gridFeature N
  have hC : Integrable (fun w => C w^2) standardPair := (pop_mem 2).integrable_sq
  have hCD : Integrable (fun w => C w*D w) standardPair := mixed_integrable (pop_mem 2) (grid_mem N 2)
  have hD : Integrable (fun w => D w^2) standardPair := (grid_mem N 2).integrable_sq
  have sqe (w : ℝ×ℝ) : coeff N b w^2=C w^2-(2*b)*(C w*D w)+b^2*D w^2 := by unfold coeff C D; ring
  change (∫ w, coeff N b w^2 ∂standardPair)=_
  simp_rw [sqe]
  have hsub : Integrable (fun w => C w^2-(2*b)*(C w*D w)) standardPair := hC.sub (hCD.const_mul _)
  rw [integral_add hsub (hD.const_mul _),integral_sub hC (hCD.const_mul _),
    integral_const_mul,integral_const_mul,show (∫ w,C w^2 ∂standardPair)=c0 from populationFeature_second,
    show (∫ w,C w*D w ∂standardPair)=c0 from grid_mixed (by dsimp [N]; omega),
    show (∫ w,D w^2 ∂standardPair)=c0+S n from grid_second hn ho]
  ring

private theorem feature_coord (N : ℕ) (i : Fin N) (x y : ℝ) :
    feature (⟨x,y⟩:ℂ) (gridPoint N i) = phi (physicalAngle i) (x,y) := by
  unfold feature phi
  congr 1
  simp only [Complex.inner,Complex.mul_re,Complex.conj_re,Complex.conj_im,gridPoint,projection,physicalAngle]
  ring
private theorem radius_coord (x y : ℝ) : ‖(⟨x,y⟩:ℂ)‖/π = populationFeature (x,y) := by
  simp only [populationFeature,Complex.norm_def,Complex.normSq_apply,sq]

private theorem reference_average (N m : ℕ) (hm : 0<m) (b : ℝ) :
    reference N m b = fun ω => b+√(m:ℝ)*sampleAverage (atom N b) ω := by
  have hm' : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hs : √(m:ℝ)≠0 := sqrt_ne_zero'.mpr (by exact_mod_cast hm)
  have hscale : √(m:ℝ)*(m:ℝ)⁻¹ = 1/√(m:ℝ) := by
    field_simp [hs,hm']; nlinarith [sq_sqrt (Nat.cast_nonneg m)]
  ext ω
  let a (j : Fin m) := ω (j,0)
  let w (j : Fin m) := (ω (j,1),ω (j,2))
  let R (j : Fin m) := populationFeature (w j)
  let X (j : Fin m) (i : Fin N) := phi (physicalAngle i) (w j)
  have hpop : populationMean (1/√(m:ℝ)) (initial ω) = 1/√(m:ℝ)*(∑ j,R j*a j) := by
    unfold populationMean
    simp only [R,a,w,←radius_coord,initial]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro _ _; ring
  have hgrid (i : Fin N) : output (1/√(m:ℝ)) (initial ω) (gridPoint N i)=1/√(m:ℝ)*∑ j,a j*X j i := by
    simp [output,a,X,w,initial,feature_coord]
  have hterm (j : Fin m) : atom N b (fun k => ω (j,k)) = (R j*a j)-b*((∑ i,a j*X j i)/N) := by
    dsimp [atom,coeff,gridFeature,R,X,w,a]
    rw [←Finset.mul_sum]
    ring
  rw [reference,hpop]
  simp only [hgrid,sampleAverage,←mul_assoc,hscale,hterm,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_div]
  rw [Finset.sum_comm (f:=fun i j => a j * X j i)]
  simp_rw [←Finset.mul_sum]
  ring

/-- The actual Gaussian finite-width shared-seed reference has mean b and its
variance is independent of width, with the complete covariance alias term S. -/
theorem reference_moments (n m : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m) (b : ℝ) :
    (∫ ω, reference (n+1) m b ω ∂seedLaw m) = b ∧
    ProbabilityTheory.variance (reference (n+1) m b) (seedLaw m) = c0*(1-b)^2+b^2*S n := by
  let f := atom (n+1) b
  have hmem := (average_mem (m:=m) (atom_mem (n+1) b)).const_mul (√(m:ℝ))
  rw [reference_average _ _ hm b]
  constructor
  · rw [integral_add (integrable_const _) (hmem.integrable (by norm_num)),integral_const,integral_const_mul,
      average_mean hm (atom_mem _ _),atom_mean]
    simp
  · rw [variance_const_add hmem.aestronglyMeasurable,variance_const_mul,average_variance hm (atom_mem _ _),
      atom_variance,coeff_second hn ho,Real.sq_sqrt (Nat.cast_nonneg m)]
    field_simp [show (m:ℝ)≠0 by exact_mod_cast hm.ne']

/-- Specialization to the interpolation weight of any layer ratio, including one. -/
theorem weighted_reference_moments (n m : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m) (τ : ℝ) :
    (∫ ω, reference (n+1) m (weight τ n) ω ∂seedLaw m) = weight τ n ∧
    ProbabilityTheory.variance (reference (n+1) m (weight τ n)) (seedLaw m) = CircleSpectrum.variance τ n := by
  simpa only [CircleSpectrum.variance] using reference_moments n m hn ho hm (weight τ n)

open Filter Topology

/-- The scaled bias and variance constants hold under the actual seed measure
along every growing odd grid, with any positive finite width schedule. -/
theorem reference_limits (n m : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 3≤n i+1) (ho : ∀ i, Odd (n i+1)) (hm : ∀ i, 0<m i) (τ : ℝ) (hτ : 0≤τ) :
    Tendsto (fun i => ((n i:ℝ)+1)^2*(1-∫ ω, reference (n i+1) (m i) (weight τ (n i)) ω ∂seedLaw (m i)))
      atTop (𝓝 (π^2*τ/(12*(2+τ)))) ∧
    Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance
      (reference (n i+1) (m i) (weight τ (n i))) (seedLaw (m i)))
      atTop (𝓝 (π^2/360*(1+5*τ^2/(2+τ)^2))) := by
  have h (i : ℕ) := weighted_reference_moments _ _ (hn i) (ho i) (hm i) τ
  simp_rw [fun i => (h i).1, fun i => (h i).2]
  exact ⟨(bias_limit τ hτ).comp grow,(variance_limit τ hτ).comp grow⟩

end CircleReferenceMoments
