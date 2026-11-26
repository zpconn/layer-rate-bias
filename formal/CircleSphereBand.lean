module

public import CircleInitializationConcentration
import all CircleInitializationConcentration
import all CircleGaussianMargin
import Mathlib.Tactic

/-! A scalar projection of a uniform three-dimensional direction, including a
uniform estimate for every interval centred at one. The distribution of the
unnormalized Gaussian radius does not enter the estimate. -/
public section
noncomputable section
namespace CircleSphereBand
open Real MeasureTheory ProbabilityTheory Set Finset CircleInitializationConcentration

def direction (z : Atom) : Atom :=
  if atomEnergy z=0 then ![0,1,0] else fun i => z i/√(atomEnergy z)

theorem measurable_direction : Measurable direction := by
  unfold direction
  have hE : Measurable atomEnergy := by unfold atomEnergy; fun_prop
  apply Measurable.ite (measurableSet_eq_fun hE measurable_const) measurable_const
  exact Measurable.of_eval (fun i => (measurable_pi_apply i).div hE.sqrt)

theorem direction_unit (z : Atom) : ∑ i, (direction z i)^2=1 := by
  by_cases h : atomEnergy z=0
  · simp [direction,h,Fin.sum_univ_three]
  · have hn := atomEnergy_nonneg z
    simp only [direction,ite_eq_right h,div_pow,sq_sqrt hn,←Finset.sum_div]
    rw [show ∑ i, (z i)^2=atomEnergy z by simp [atomEnergy,Fin.sum_univ_three],div_self h]

def project (b z : Atom) := ∑ i, direction z i*b i

theorem measurable_project (b : Atom) : Measurable (project b) := by
  unfold project
  exact Finset.measurable_fun_sum _ fun i _ => ((measurable_pi_apply i).comp measurable_direction).mul_const _

private theorem energy_pos_ae : ∀ᵐ z ∂atomLaw, 0<atomEnergy z := by
  let _ : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have h := (measurePreserving_eval (fun _ : Fin 3 => gaussianReal 0 1) 1).quasiMeasurePreserving.ae
    (show ∀ᵐ t ∂gaussianReal 0 1, t≠0 by rw [ae_iff]; simp)
  filter_upwards [h] with z hz
  unfold atomEnergy
  nlinarith [sq_pos_of_ne_zero hz,sq_nonneg (z 0),sq_nonneg (z 2)]

private theorem rotate (b : Atom) (hb : ∑i, (b i)^2=1) (Φ : ℝ → ℝ → ℝ) :
    (∫ z, Φ (atomEnergy z) (∑i, z i*b i) ∂atomLaw) = ∫ z, Φ (atomEnergy z) (z 1) ∂atomLaw := by
  let E := EuclideanSpace ℝ (Fin 3)
  let e : E := WithLp.toLp 2 ![0,1,0]
  let v : E := WithLp.toLp 2 b
  have hn : ‖e‖=‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    change (∑ i, ((![0,1,0] : Atom) i)^2)=∑i, (b i)^2
    rw [hb];simp [Fin.sum_univ_three]
  let R := (ℝ ∙ (e-v))ᗮ.reflection
  have hR : R e=v := Submodule.reflection_sub hn
  let toE := MeasurableEquiv.toLp 2 Atom
  have ht : MeasurePreserving toE atomLaw (stdGaussian E) := ⟨toE.measurable,map_pi_eq_stdGaussian⟩
  let r := R.symm.toHomeomorph.toMeasurableEquiv
  have hr : MeasurePreserving r (stdGaussian E) (stdGaussian E) := ⟨r.measurable,stdGaussian_map R.symm⟩
  have en (z : Atom) : ‖toE z‖^2=atomEnergy z := by
    simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,toE,atomEnergy]
  have coord (z : Atom) : inner ℝ e (toE z)=z 1 := by
    change z ⬝ᵥ (star (![0,1,0] : Fin 3 → ℝ))=_
    simp [dotProduct,Fin.sum_univ_three]
  have proj (z : Atom) : inner ℝ v (toE z)=∑i,z i*b i := by
    change z ⬝ᵥ (star b)=_; simp [dotProduct]
  have iso (z : E) : inner ℝ e (r z)=inner ℝ v z := by
    change inner ℝ e (R.symm z)=_
    rw [←hR,←R.inner_map_map e (R.symm z),R.apply_symm_apply]
  let test : E → ℝ := fun t => Φ (‖t‖^2) (inner ℝ e t)
  have rot (z : Atom) : test (r (toE z))=Φ (atomEnergy z) (∑i,z i*b i) := by
    change Φ (‖R.symm (toE z)‖^2) (inner ℝ e (r (toE z)))=_
    rw [R.symm.norm_map,en,iso,proj]
  have al (z : Atom) : test (toE z)=Φ (atomEnergy z) (z 1) := by simp [test,en,coord]
  simp_rw [←rot,←al]
  rw [ht.integral_comp' (fun u => test (r u)),ht.integral_comp' test,hr.integral_comp' test]

theorem projection_cdf (b : Atom) (hb : ∑i,(b i)^2=1) {t : ℝ} (ht : 0≤t) (hu : t≤1) :
    atomLaw.real {z | |project b z|≤t} = t := by
  let A := {z | |project b z|≤t}
  have hA : MeasurableSet A := measurableSet_le (continuous_abs.measurable.comp (measurable_project b)) measurable_const
  have eq := rotate b hb (fun E x => CircleGaussianMargin.mark t 0 x E)
  have h' := marked_energy t 0 ht hu (1,0) (by norm_num)
  simp only [zero_mul,one_mul,add_zero,pow_zero,integral_const,probReal_univ,smul_eq_mul,mul_one] at h'
  have hx : ∀ᵐ z ∂atomLaw, A.indicator (1 : Atom→ℝ) z =
      CircleGaussianMargin.mark t 0 (∑i,z i*b i) (atomEnergy z) := by
    filter_upwards [energy_pos_ae] with z hz
    have hp : project b z = (∑i,z i*b i)/√(atomEnergy z) := by
      simp only [project,direction,ite_eq_right hz.ne',Finset.sum_div]
      apply sum_congr rfl;intro i _;ring
    have eqv : z∈A ↔ |∑i,z i*b i|≤t*√(atomEnergy z) := by
      change |project b z|≤t ↔ _
      rw [hp,abs_div,abs_of_pos (sqrt_pos.mpr hz),div_le_iff₀ (sqrt_pos.mpr hz)]
    by_cases ha : z∈A
    · simp [indicator_of_mem ha,CircleGaussianMargin.mark,eqv.mp ha]
    · simp [indicator_of_notMem ha,CircleGaussianMargin.mark,mt eqv.mpr ha]
  rw [←integral_indicator_one hA,integral_congr_ae hx,eq]
  exact h'

theorem project_le_one (b : Atom) (hb : ∑i,(b i)^2=1) (z : Atom) : |project b z|≤1 := by
  have h := sum_mul_sq_le_sq_mul_sq univ (direction z) b
  rw [direction_unit,hb,one_mul] at h
  exact (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp (by simpa only [sq_abs,one_pow,project] using h)

private theorem unit_band (b : Atom) (hb : ∑i,(b i)^2=1) {R δ : ℝ} (hd : 0<δ) (hu : δ<1/4)
    (hr : 1-δ≤R) : atomLaw.real {z | |1-R*project b z|≤δ} ≤ 4*δ := by
  let lo := (1-2*δ)/R
  let hi := min 1 ((1+δ)/R)
  have rp : 0<R := by linarith
  have hl : 0≤lo := div_nonneg (by linarith) rp.le
  have hl1 : lo≤1 := (div_le_one rp).2 (by linarith)
  have hle : lo≤hi := le_min hl1 (div_le_div_of_nonneg_right (by linarith) rp.le)
  let A (t : ℝ) := {z | |project b z|≤t}
  have hA (t : ℝ) : MeasurableSet (A t) := measurableSet_le (continuous_abs.measurable.comp (measurable_project b)) measurable_const
  have mono : A lo⊆A hi := fun z hz => (show |project b z|≤lo from hz).trans hle
  have sub : {z | |1-R*project b z|≤δ}⊆ A hi \ A lo := by
    intro z hz
    have hh := abs_le.mp (show |1-R*project b z|≤δ from hz)
    have hpos : 0≤project b z := by by_contra! q;linarith [mul_neg_of_pos_of_neg rp q]
    have ht : |project b z|=project b z := abs_of_nonneg hpos
    refine ⟨le_min (project_le_one b hb z) ?_,?_⟩
    · rw [ht];exact (le_div_iff₀ rp).2 (by linarith [hh.1])
    · change ¬ |project b z|≤lo
      rw [ht,not_le]
      exact (div_lt_iff₀ rp).2 (by linarith [hh.2])
  apply (measureReal_mono sub).trans
  rw [measureReal_sdiff mono (hA lo)]
  change atomLaw.real {z | |project b z|≤hi}-atomLaw.real {z | |project b z|≤lo} ≤ _
  rw [projection_cdf b hb (hl.trans hle) (min_le_left _ _),projection_cdf b hb hl hl1]
  have hdiff : (1+δ)/R-lo≤4*δ := by
    unfold lo
    rw [←sub_div,div_le_iff₀ rp]
    nlinarith [mul_le_mul_of_nonneg_left hr hd.le,sq_nonneg δ,
      mul_le_mul_of_nonneg_left (le_of_lt hu) hd.le]
  exact (sub_le_sub_right (min_le_right _ _) _).trans hdiff

theorem projection_band (a : Atom) {δ : ℝ} (hd : 0≤δ) :
    atomLaw.real {z | |1-project a z|≤δ} ≤ 4*δ := by
  have large {v : ℝ} (h : 1/4≤v) : atomLaw.real {z | |1-project a z|≤v}≤4*v := by
    have q := measureReal_mono (μ:=atomLaw) (Set.subset_univ {z | |1-project a z|≤v})
    rw [probReal_univ] at q;linarith
  have pos {v : ℝ} (hv : 0<v) : atomLaw.real {z | |1-project a z|≤v}≤4*v := by
    by_cases hu : 1/4≤v
    · exact large hu
    have hl := lt_of_not_ge hu
    let R := √(∑i, (a i)^2)
    have RR : R^2=∑i,(a i)^2 := sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
    have cp (z : Atom) : |project a z|≤R := by
      have h := sum_mul_sq_le_sq_mul_sq univ (direction z) a
      rw [direction_unit,one_mul,←RR] at h
      exact (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp (by simpa [project] using h)
    by_cases hr : 1-v≤R
    · have rp : 0<R := by linarith
      let b (i : Fin 3) := a i/R
      have hb : ∑i,(b i)^2=1 := by simp only [b,div_pow,←sum_div,←RR,div_self (pow_ne_zero 2 rp.ne')]
      have eq (z : Atom) : R*project b z=project a z := by
        simp only [project,b,Finset.mul_sum]
        apply sum_congr rfl;intro i _;field_simp
      simpa only [eq] using unit_band b hb hv hl hr
    · have empty : {z | |1-project a z|≤v}=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have q := abs_le.mp (show |1-project a z|≤v from hz)
        linarith [cp z, le_abs_self (project a z),q.2]
      simp [empty,hv.le]
  rcases eq_or_lt_of_le hd with hz | hv
  · subst δ
    rw [mul_zero]
    apply le_of_forall_pos_le_add
    intro ε hε
    apply (measureReal_mono (show {z | |1-project a z|≤0}⊆{z | |1-project a z|≤ε/4} from
      fun z hz => (show |1-project a z|≤0 from hz).trans (by positivity))).trans
    exact (pos (show 0<ε/4 by positivity)).trans_eq (by ring)
  · exact pos hv
end CircleSphereBand
