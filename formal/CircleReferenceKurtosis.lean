module

public import CircleReferenceMixture
public import CircleResidualSpectrum
import all CircleResidualSpectrum
import all CircleReferenceMixture
import all CircleReferenceMoments
import all CircleSpectrum
import all CircleGridSpectrum
import all CircleInitializationConcentration
import all CircleKernelIdentification
import Mathlib.Tactic

/-! A uniform relative variance bound for one Gaussian circle feature.
The Fourier tail of the single-grid quadrature, its squared angular error,
and the exact second moment are retained separately until the final bound. -/
public section
noncomputable section
namespace CircleReferenceKurtosis
open Real MeasureTheory ProbabilityTheory Set CircleResidualSpectrum CircleReferenceMoments
  CircleReferenceMixture CircleInitializationConcentration CircleKernelIdentification CircleSpectrum
open CircleGridSpectrum CircleEscape

/-- A finite absolute-summability constant for nonzero multiples of the grid
frequency. The convention 1/0=0 drops the zero term in this bound. -/
def tailConstant : ℝ := 2*∑' j : ℤ, 1/(j:ℝ)^2
theorem tailConstant_nonneg : 0 ≤ tailConstant := by unfold tailConstant; positivity

private theorem alias_zero_error {N : ℕ} [NeZero N] (hn : 3≤N) (θ : ℝ) :
    ‖(∑' l : ℤ, if (l:ZMod N)=0 then shiftCoeff θ l else 0) - ((1/π:ℝ):ℂ)‖ ≤ tailConstant/(N:ℝ)^2 := by
  let a := shiftCoeff θ
  let f := fun l : ℤ => if (l:ZMod N)=0 then a l else 0
  let g := fun j : ℤ => (N:ℤ)*j
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  have hg : Function.Injective g := fun _ _ h => mul_left_cancel₀ (by exact_mod_cast (NeZero.ne N)) h
  have support : Function.support f ⊆ Set.range g := by
    intro l hl
    have c : (l:ZMod N)=0 := by by_contra h; exact hl (by simp [f,h])
    obtain ⟨j,hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd l N).mp c
    exact ⟨j,hj.symm⟩
  have val (j : ℤ) : f (g j) = a (g j) := by simp [f,g]
  have sf := (shift_summable θ).comp_injective hg
  have zero : a (g 0) = ((1/π:ℝ):ℂ) := by
    simp only [a,g,mul_zero,shiftCoeff,Int.cast_zero,fourier_zero,mul_one]
    have q := halfWaveCoeff_even 0
    norm_num at q
    simp [q]
  let v := fun j : ℤ => if j=0 then (0:ℂ) else a (g j)
  let b := fun j : ℤ => (2/(N:ℝ)^2)*(1/(j:ℝ)^2)
  have dom (j : ℤ) : ‖v j‖ ≤ b j := by
    by_cases hj : j=0
    · simp [v,b,hj]
    · have absj : 1≤j.natAbs := Int.natAbs_pos.mpr hj
      have high : 2 ≤ (g j).natAbs := by
        dsimp [g]; rw [Int.natAbs_mul,Int.natAbs_natCast]
        exact (by omega : 2≤N).trans ((Nat.le_mul_of_pos_right N (by omega)))
      rw [show v j=a (g j) by simp [v,hj],CircleResidualSpectrum.shift_norm]
      apply (halfWaveCoeff_high high).trans_eq
      dsimp [b,g]
      push_cast
      ring
  have sb : Summable b := (Real.summable_one_div_int_pow.mpr (by decide : 1<2)).mul_left _
  have sv := sb.of_nonneg_of_le (fun j => norm_nonneg (v j)) dom
  have hsa : Summable (fun j => a (g j)) := sf.of_norm
  have all : (∑' l : ℤ, f l) - ((1/π:ℝ):ℂ) = ∑' j, v j := by
    rw [← hg.tsum_eq support]
    simp_rw [val]
    rw [hsa.tsum_eq_add_tsum_ite 0,zero,add_sub_cancel_left]
  calc
    _ = ‖∑' j, v j‖ := congrArg norm all
    _ ≤ ∑' j, b j := (norm_tsum_le_tsum_norm sv).trans (sv.tsum_le_tsum dom sb)
    _ = _ := by simp only [b,tsum_mul_left,tailConstant];ring

private theorem zero_mode_radius {N : ℕ} [NeZero N] (hn : 3≤N) (w : ℂ) :
    ‖unitMode (0:ZMod N) w-((‖w‖/π:ℝ):ℂ)‖ ≤ ‖w‖*(tailConstant/(N:ℝ)^2) := by
  unfold unitMode
  simp_rw [wave_series w]
  rw [show (fun i => (↑‖w‖:ℂ)*series (shiftCoeff w.arg) i) =
    (↑‖w‖:ℂ) • series (shiftCoeff w.arg) from rfl,map_smul]
  change ‖(↑‖w‖:ℂ)*ZMod.dft (series (shiftCoeff w.arg)) 0 / (N:ℂ) - _‖ ≤ _
  rw [mul_div_assoc,dft_alias _ (shift_summable _),show ((‖w‖/π:ℝ):ℂ)=(‖w‖:ℂ)*((1/π:ℝ):ℂ) by push_cast;ring,
    ←mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left (alias_zero_error hn _) (norm_nonneg _)

private theorem grid_quadrature {N : ℕ} (hn : 3 ≤ N) (w : ℝ×ℝ) :
    |CircleReferenceMoments.gridFeature N w-populationFeature w| ≤ ‖(⟨w.1,w.2⟩:ℂ)‖*tailConstant/(N:ℝ)^2 := by
  let : NeZero N := ⟨by omega⟩
  let v : ℂ := ⟨w.1,w.2⟩
  have mode : unitMode (0:ZMod N) v = ((CircleReferenceMoments.gridFeature N w:ℝ):ℂ) := by
    simp only [unitMode,ZMod.dft_apply,mul_zero,neg_zero,AddChar.map_zero_eq_one,one_smul]
    have sum : (∑ i : ZMod N, (feature v (gridPoint N ((ZMod.finEquiv N).symm i)):ℂ)) =
        ∑ j : Fin N, (feature v (gridPoint N j):ℂ) :=
      (ZMod.finEquiv N).symm.toEquiv.sum_comp (fun j : Fin N => (feature v (gridPoint N j):ℂ))
    rw [sum,CircleReferenceMoments.gridFeature]
    push_cast
    dsimp only [v]
    simp_rw [CircleReferenceMoments.feature_coord]
  have h := zero_mode_radius hn v
  rw [mode,CircleReferenceMoments.radius_coord] at h
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at h
  exact h.trans_eq (by ring)

/-- Retaining the first alias pair gives a uniform fourth-power lower
bound on the excess covariance of the grid mean. -/
theorem S_lower (n : ℕ) : 1/(4*π^2*((n:ℝ)+1)^4) ≤ S n := by
  let f := fun j => rp 4 j * (1/(1-offset n j)^2)
  have non (j : ℕ) : 0≤f j := by unfold f rp; positivity
  have dom (j : ℕ) : f j ≤ 2*rp 4 j := by
    obtain ⟨_,hi⟩ := CircleSpectrum.offset_bounds n j
    have den : (1/2:ℝ) ≤ (1-offset n j)^2 := by nlinarith [sq_nonneg (offset n j)]
    rw [mul_comm (2:ℝ)]
    apply mul_le_mul_of_nonneg_left _ (by unfold rp; positivity)
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  have sum := (CircleSpectrum.rp_four_sum.summable.mul_left 2).of_nonneg_of_le non dom
  have term := sum.le_tsum 0 (fun i _ => non i)
  have h0 := CircleSpectrum.offset_bounds n 0
  have f0 : 1 ≤ f 0 := by
    simp only [f,rp,Nat.cast_zero,zero_add,one_pow,div_one,one_mul]
    apply (one_le_div (sq_pos_of_pos (by linarith))).mpr
    nlinarith [mul_nonneg h0.1 (show 0≤1-offset n 0 by linarith)]
  have s := mul_le_mul_of_nonneg_left (f0.trans term) (by positivity : 0≤(1/((n:ℝ)+1)^4)*(1/(4*π^2)))
  change _ ≤ (1/((n:ℝ)+1)^4)*((1/(4*π^2))*∑' j, f j)
  exact (show 1/(4*π^2*((n:ℝ)+1)^4)=(1/((n:ℝ)+1)^4)*(1/(4*π^2))*1 by rw [one_div, mul_inv_rev];ring).le.trans
    (s.trans_eq (mul_assoc ..))

/-- The one-neuron squared hidden coefficient has the covariance calculated
by the exact Gaussian feature kernel. -/
theorem mean_squaredFeature (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (b : ℝ) :
    (∫ z, squaredFeature (n+1) b z ∂atomLaw) = c0*(1-b)^2+b^2*S n := by
  let k := CircleReferenceMoments.coeff (n+1) b
  have h : AEStronglyMeasurable (fun w => k w^2) standardPair :=
    (CircleReferenceMoments.coeff_mem (n+1) b 2).integrable_sq.aestronglyMeasurable
  have law := (measurePreserving_snd.comp CircleReferenceMoments.split_preserving).hasLaw.integral_comp h
  exact law.trans (CircleReferenceMoments.coeff_second hn ho b)

def shapeConstant := 1+8*π^2*tailConstant^2

def ratioConstant := 15*shapeConstant^2

/-- A pointwise square bound prices a large hidden radius by its Gaussian
energy, and both angular terms by their exact variances. -/
private theorem one_square (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (b : ℝ) (z : Atom) :
    squaredFeature (n+1) b z ≤ atomEnergy z * (shapeConstant*∫ w, squaredFeature (n+1) b w ∂atomLaw) := by
  let N : ℝ := (n:ℝ)+1
  let w := (z 1,z 2)
  let v : ℂ := ⟨w.1,w.2⟩
  let V := c0*(1-b)^2+b^2*S n
  let x := |1-b|/π
  let y := |b| *tailConstant/N^2
  have np : 0<N := by dsimp [N]; positivity
  have rad : ‖v‖^2 ≤ atomEnergy z := by rw [Complex.sq_norm]; dsimp [v,w,Complex.normSq_apply,atomEnergy]; nlinarith [sq_nonneg (z 0)]
  have sn := S_lower n
  have part : b^2*S n ≤ V := le_add_of_nonneg_left (by unfold c0; positivity)
  have xbd : 2*x^2 ≤ V := by
    have sn0 := (show (0:ℝ)≤1/(4*π^2*N^4) by positivity).trans sn
    have bd : c0*(1-b)^2 ≤ V := le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) sn0)
    convert bd using 1
    dsimp [c0,x]; rw [div_pow,sq_abs]; ring
  have ybd : y^2 ≤ (4*π^2*tailConstant^2)*V := by
    have both := (mul_le_mul_of_nonneg_left sn (sq_nonneg b)).trans part
    have e := mul_le_mul_of_nonneg_left both (show 0≤4*π^2*tailConstant^2 by positivity)
    apply le_trans _ e
    change y^2 ≤ (4*π^2*tailConstant^2)*(b^2*(1/(4*π^2*N^4)))
    dsimp only [y]; rw [div_pow,mul_pow,sq_abs]; field_simp; rfl
  have sh : (x+y)^2 ≤ shapeConstant*V := by
    dsimp [shapeConstant]
    nlinarith only [xbd,ybd,sq_nonneg (x-y)]
  have q := grid_quadrature hn w
  have q' : |populationFeature w-CircleReferenceMoments.gridFeature (n+1) w| ≤ ‖v‖*tailConstant/N^2 := by
    rw [abs_sub_comm];simpa only [Nat.cast_add,Nat.cast_one] using q
  have k : |CircleReferenceMoments.coeff (n+1) b w| ≤ ‖v‖*(x+y) := by
    rw [CircleReferenceMoments.coeff,show populationFeature w-b*CircleReferenceMoments.gridFeature (n+1) w =
      (1-b)*populationFeature w+b*(populationFeature w-CircleReferenceMoments.gridFeature (n+1) w) by ring]
    apply (abs_add_le _ _).trans
    have r : |populationFeature w| = ‖v‖/π := by
      rw [←CircleReferenceMoments.radius_coord w.1 w.2,abs_of_nonneg (by positivity : 0≤‖v‖/π)]
    rw [abs_mul,abs_mul,r]
    have h := add_le_add (le_refl (|1-b| *(‖v‖/π))) (mul_le_mul_of_nonneg_left q' (abs_nonneg b))
    apply h.trans_eq
    dsimp only [x,y];ring
  have hi := pow_le_pow_left₀ (abs_nonneg _) k 2
  rw [sq_abs,mul_pow] at hi
  rw [mean_squaredFeature n hn ho b]
  exact hi.trans (mul_le_mul rad sh (sq_nonneg _) (atomEnergy_nonneg _))

/-- The relative variance of the squared Gaussian feature is bounded
uniformly over all odd grids and all real reference coefficients. In
particular it applies to the finite-grid kernel weight at unit rate. -/
theorem relative_variance (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (b : ℝ) :
    ProbabilityTheory.variance (squaredFeature (n+1) b) atomLaw ≤
      ratioConstant*(∫ z, squaredFeature (n+1) b z ∂atomLaw)^2 := by
  let F := squaredFeature (n+1) b
  let V := ∫ z, F z ∂atomLaw
  have mem := CircleReferenceMixture.squared_mem (n+1) b
  have hv := variance_le_expectation_sq mem.aestronglyMeasurable
  have integ := (energy_pow_integrable 2).const_mul ((shapeConstant*V)^2)
  have e := integral_mono mem.integrable_sq integ (fun z => by
    have h := pow_le_pow_left₀ (sq_nonneg _) (one_square n hn ho b z) 2
    change (F z)^2 ≤ (shapeConstant*V)^2 * atomEnergy z^2
    simpa only [mul_pow,mul_comm (atomEnergy z^2)] using h)
  change (∫ z, (F z)^2 ∂atomLaw) ≤ ∫ z, (shapeConstant*V)^2*atomEnergy z^2 ∂atomLaw at e
  rw [integral_const_mul,atomEnergy_second] at e
  exact hv.trans (e.trans_eq (by unfold ratioConstant;ring))

end CircleReferenceKurtosis
