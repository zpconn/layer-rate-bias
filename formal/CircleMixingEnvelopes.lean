module

public import CircleSpectralPathLength
public import CircleSharpInitialization
public import CircleScoreMargin
public import CircleReadoutMixing
import all CircleReadoutMixing
import all CircleSpectralPathLength
import all CircleSharpInitialization
import all CircleScoreMargin
import all CircleInitializationConcentration
import all CircleResidualSpectrum
import all CircleTangentDrift
import all CircleFlowPath
import Mathlib.Tactic

/-! Direction-independent envelopes for affine output features and quadratic
tangent entries of three readout replicas sharing their hidden weights. -/
public section
noncomputable section
namespace CircleMixingEnvelopes
open CircleInitializationConcentration CircleSharpInitialization CircleSpectralPathLength
  CircleTangentDrift CircleFlowPath CircleScoreMargin CircleGridSpectrum CircleEscapeBridge
  MeasureTheory ProbabilityTheory Real Finset

private def d := (sqrt 2)⁻¹
private theorem dsq : d^2=1/2 := by simp [d,inv_pow,sq_sqrt (show 0≤(2:ℝ) by norm_num),one_div]

/-- Three orthogonal axes and the three bisectors of their coordinate planes. -/
def quadDir : Fin 6 → Atom := ![![1,0,0],![0,1,0],![0,0,1],![d,d,0],![0,d,d],![d,0,d]]
def linDir : Fin 6 → Atom := ![![1,0,0],![0,1,0],![0,0,1],![-1,0,0],![0,-1,0],![0,0,-1]]
private def qWeight (u : Atom) : Fin 6 → ℝ := ![
  u 0*(u 0-u 1-u 2),u 1*(u 1-u 0-u 2),u 2*(u 2-u 0-u 1),2*(u 0*u 1),2*(u 1*u 2),2*(u 0*u 2)]
private def lWeight (u : Atom) : Fin 6 → ℝ := ![
  (1/6+u 0/2),(1/6+u 1/2),(1/6+u 2/2),(1/6-u 0/2),(1/6-u 1/2),(1/6-u 2/2)]

private theorem quad_unit (i : Fin 6) : ∑ j, (quadDir i j)^2=1 := by
  fin_cases i <;> norm_num [quadDir,Fin.sum_univ_three,dsq]
private theorem lin_unit (i : Fin 6) : ∑ j, (linDir i j)^2=1 := by
  fin_cases i <;> norm_num [linDir,Fin.sum_univ_three]

private theorem sphere_abs (u : Atom) (hu : ∑ i, (u i)^2=1) (j : Fin 3) : |u j|≤1 := by
  have hj := Finset.single_le_sum (f:=fun i => (u i)^2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  rw [hu] at hj
  exact (sq_le_one_iff_abs_le_one _).mp hj
private theorem qcap (u : Atom) (hu : ∑ i, (u i)^2=1) (i : Fin 6) : |qWeight u i|≤3 := by
  have h₁ (a b c : Fin 3) : |u a*(u a-u b-u c)|≤3 := by
    rw [abs_mul]
    have h := (abs_sub (u a-u b) (u c)).trans (add_le_add_left (abs_sub (u a) (u b)) _)
    have h3 : |u a-u b-u c|≤3 := h.trans (by linarith [sphere_abs u hu a,sphere_abs u hu b,sphere_abs u hu c])
    simpa using mul_le_mul (sphere_abs u hu a) h3 (abs_nonneg _) zero_le_one
  have h₂ (a b : Fin 3) : |2*(u a*u b)|≤3 := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : 0≤(2:ℝ))]
    have h := mul_le_mul (sphere_abs u hu a) (sphere_abs u hu b) (abs_nonneg _) zero_le_one
    linarith
  fin_cases i <;> first | exact h₁ _ _ _ | exact h₂ _ _
private theorem lcap (u : Atom) (hu : ∑ i, (u i)^2=1) (i : Fin 6) : |lWeight u i|≤1 := by
  have h (k : Fin 3) := abs_le.mp (sphere_abs u hu k)
  fin_cases i <;> simp [lWeight,abs_le] <;> constructor <;> linarith [h 0,h 1,h 2]

private def linForm (u x : Atom) := ∑ k, u k*x k
private theorem affine_interp (u x : Atom) (A B : ℝ) :
    A+B*linForm u x = ∑ i, lWeight u i*(A+B*linForm (linDir i) x) := by
  simp [lWeight,linDir,linForm,Fin.sum_univ_succ]
  ring
private theorem qsum (u : Atom) (hu : ∑ i,(u i)^2=1) : ∑ i, qWeight u i=1 := by
  rw [←hu]
  simp [qWeight,Fin.sum_univ_succ]
  ring
private theorem quadratic_interp (u x : Atom) (hu : ∑ i,(u i)^2=1) (A B : ℝ) :
    A+B*(linForm u x)^2 = ∑ i, qWeight u i*(A+B*(linForm (quadDir i) x)^2) := by
  have hp : (linForm u x)^2 = ∑ i, qWeight u i*(linForm (quadDir i) x)^2 := by
    simp [qWeight,quadDir,linForm,Fin.sum_univ_succ]
    ring_nf
    rw [dsq]
    ring
  simp_rw [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,qsum u hu,one_mul]
  rw [hp,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem euclidean_cap {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    (c : Fin 6 → ℝ) (C : ℝ) (hc : ∀ j, |c j|≤C) (v : Fin 6 → EuclideanSpace 𝕜 ι) :
    ‖∑ j, c j • v j‖ ≤ C*∑ j, ‖v j‖ := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  exact fun i _ => (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _))

private theorem block_cap {ι : Type*} (s : Finset ι) (F : Fin 6 → ι → ℂ) (c : Fin 6 → ℝ)
    (hc : ∀ j, |c j|≤1) : blockNorm s (fun i => ∑ j, c j • F j i) ≤ ∑ j, blockNorm s (F j) := by
  classical
  let V (j : Fin 6) : EuclideanSpace ℂ s := WithLp.toLp 2 (fun i => F j i)
  have normV (f : ι → ℂ) : ‖(WithLp.toLp 2 (fun i : s => f i) : EuclideanSpace ℂ s)‖=blockNorm s f := by
    rw [EuclideanSpace.norm_eq,blockNorm]
    congr 1
    exact Finset.sum_attach s (fun i => ‖f i‖^2)
  have hv : (∑ j, c j • V j) = WithLp.toLp 2 (fun i : s => ∑ j, c j • F j i) := by
    ext i; simp [V]
  have h := euclidean_cap c 1 hc V
  rw [hv,normV (fun i => ∑ j, c j • F j i),one_mul] at h
  simpa only [V,normV] using h

private theorem finiteRms_cap {ι : Type*} [Fintype ι] (F : Fin 6 → ι → ℝ) (c : Fin 6 → ℝ)
    (hc : ∀ j, |c j|≤3) : finiteRms (fun i => ∑ j, c j*F j i) ≤ 3*∑ j, finiteRms (F j) := by
  let V (j : Fin 6) : EuclideanSpace ℝ ι := WithLp.toLp 2 (F j)
  have normV (f : ι → ℝ) : finiteRms f = ‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ / sqrt (Fintype.card ι) := by
    rw [finiteRms,sqrt_div (Finset.sum_nonneg fun _ _ => sq_nonneg _),EuclideanSpace.norm_eq]
    simp [sq_abs]
  have hv : (∑ j, c j • V j) = WithLp.toLp 2 (fun i => ∑ j, c j*F j i) := by
    ext i; simp [V]
  simp_rw [normV]
  rw [←hv,←Finset.sum_div,mul_div_assoc']
  exact div_le_div_of_nonneg_right (euclidean_cap c 3 hc V) (sqrt_nonneg _)

private abbrev Ctx (m : ℕ) := (Fin 3 → Layer m) × Hidden m
private def mix {m : ℕ} (u : Atom) (p : Ctx m) : Seed m :=
  (splitLayer m).symm ((fun j => linForm u (fun i => p.1 i j)),p.2)
private theorem mix0 {m : ℕ} (u : Atom) (p : Ctx m) (j : Fin m) :
    mix u p (j,0)=linForm u (fun i => p.1 i j) := rfl
private theorem mix1 {m : ℕ} (u : Atom) (p : Ctx m) (j : Fin m) : mix u p (j,1)=p.2 0 j := rfl
private theorem mix2 {m : ℕ} (u : Atom) (p : Ctx m) (j : Fin m) : mix u p (j,2)=p.2 1 j := rfl

private theorem lsum (u : Atom) : ∑ j,lWeight u j=1 := by simpa [linForm] using (affine_interp u 0 1 0).symm

private theorem output_linear {m : ℕ} (p : Ctx m) (u : Atom) (x : ℝ×ℝ) :
    output (1/√(m:ℝ)) (mix u p) x = ∑ i, u i*output (1/√(m:ℝ)) (mix (Pi.single i 1) p) x := by
  unfold output pre
  simp only [mix0,mix1,mix2,linForm,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Pi.single_apply,Finset.sum_ite_eq',mul_assoc,mul_left_comm,mul_comm]

private theorem output_interp {m : ℕ} (p : Ctx m) (u : Atom) (x : ℝ×ℝ) :
    output (1/√(m:ℝ)) (mix u p) x = ∑ j,lWeight u j*output (1/√(m:ℝ)) (mix (linDir j) p) x := by
  let a : Atom := fun j => output (1/√(m:ℝ)) (mix (Pi.single j 1) p) x
  have h (v : Atom) : output (1/√(m:ℝ)) (mix v p) x = linForm v a := output_linear p v x
  simp_rw [h]
  simpa only [one_mul,zero_add] using affine_interp u a 0 1

private theorem coeff_interp {N m : ℕ} [NeZero N] (p : Ctx m) (u : Atom) (r : ZMod N) :
    CircleResidualSpectrum.initialCoeff N m r (mix u p) =
      ∑ j, lWeight u j • CircleResidualSpectrum.initialCoeff N m r (mix (linDir j) p) := by
  simp_rw [←normalizedCoeff_raw]
  have h (i : Fin N) : rawResidual N m (mix u p) i = ∑ j, lWeight u j * rawResidual N m (mix (linDir j) p) i := by
    change _-circleLabel N i = ∑ j, lWeight u j*(_-circleLabel N i)
    rw [output_interp p u]
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,lsum,one_mul]
  unfold normalizedCoeff
  simp only [ZMod.dft_apply,smul_eq_mul,h,Complex.ofReal_sum,Complex.ofReal_mul,Complex.real_smul,Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [←mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem budget_dom {N m : ℕ} [NeZero N] (ho : Odd N) (p : Ctx m) (u : Atom)
    (hu : ∑ i,(u i)^2=1) : seedBudget ho m (mix u p)≤∑ j,seedBudget ho m (mix (linDir j) p) := by
  unfold seedBudget pathBudget
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro q _
  simp_rw [coeff_interp p u,←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (block_cap _ _ _ (lcap u hu)) (by positivity [shellConstant_pos.le])

private def active (τ : ℝ) {m : ℕ} (z : Seed m) (x y : ℝ×ℝ) :=
  sampleAverage (weightedAtom τ x y) z
private theorem active_interp (τ : ℝ) {m : ℕ} (p : Ctx m) (u : Atom) (hu : ∑ i,(u i)^2=1) (x y : ℝ×ℝ) :
    active τ (mix u p) x y = ∑ j,qWeight u j*active τ (mix (quadDir j) p) x y := by
  let xw (j : Fin m) := x.1*p.2 0 j+x.2*p.2 1 j
  let yw (j : Fin m) := y.1*p.2 0 j+y.2*p.2 1 j
  let A (j : Fin m) := max (xw j) 0 * max (yw j) 0
  let B (j : Fin m) := τ*(actualGate (xw j)*actualGate (yw j))*dot x y
  have h (v : Atom) (j : Fin m) : weightedAtom τ x y (fun k => mix v p (j,k)) =
      A j+B j*(linForm v (fun i => p.1 i j))^2 := by
    unfold weightedAtom; simp only [mix0,mix1,mix2]; dsimp [A,B,xw,yw];ring
  simp only [active,sampleAverage,h]
  simp_rw [fun j : Fin m => quadratic_interp u (fun i => p.1 i j) hu (A j) (B j)]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Finset.mul_sum]
  ring

private def rowCenter {N m : ℕ} (τ : ℝ) (j : Fin N) (z : Seed m) := populationRow τ z (startGates z) j-CircleSpectrum.k0 τ
private def gramCenter {N m : ℕ} [NeZero N] (τ : ℝ) (q : Fin N × Fin N) (z : Seed m) :=
  gridGram τ z (startGates z) q.1 q.2 - sampledMatrix τ q.1 q.2

private theorem gram_interp {N m : ℕ} [NeZero N] (hm : 0<m) (τ : ℝ) (p : Ctx m) (u : Atom)
    (hu : ∑ i,(u i)^2=1) (q : Fin N × Fin N) : gramCenter τ q (mix u p)=∑ j,qWeight u j*gramCenter τ q (mix (quadDir j) p) := by
  have eq (v : Atom) : gramCenter τ q (mix v p)=active τ (mix v p) (circleInput N q.1) (circleInput N q.2)-sampledMatrix τ q.1 q.2 := by
    unfold gramCenter gridGram startGates; rw [weightedAtom_initial hm]; rfl
  simp_rw [eq,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,qsum u hu,one_mul,active_interp τ p u hu]

private theorem row_interp {N m : ℕ} (hm : 0<m) (τ : ℝ) (p : Ctx m) (u : Atom) (hu : ∑ i,(u i)^2=1) (j : Fin N) :
    rowCenter τ j (mix u p)=∑ k,qWeight u k*rowCenter τ j (mix (quadDir k) p) := by
  let y := circleInput N j
  let Y (z : Seed m) (t : ℝ) := angleEntry τ z z y (startGates z j) t
  have eq (v : Atom) (t : ℝ) : Y (mix v p) t=active τ (mix v p) (phase t) y := by
    unfold Y angleEntry startGates; rw [weightedAtom_initial hm];rfl
  have hi (v : Atom) : Integrable (Y (mix v p)) angularLaw := angleEntry_integrable hm ..
  have row (v : Atom) : rowCenter τ j (mix v p)=(∫ t, Y (mix v p) t ∂angularLaw)-CircleSpectrum.k0 τ := rfl
  simp_rw [row,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,qsum u hu,one_mul]
  congr 1
  simp_rw [←integral_const_mul]
  rw [←MeasureTheory.integral_finsetSum _ (fun k _ => (hi (quadDir k)).const_mul (qWeight u k))]
  apply integral_congr_ae
  filter_upwards with t
  simpa only [eq] using active_interp τ p u hu (phase t) y

private theorem error_dom {N m : ℕ} [NeZero N] (hm : 0<m) (τ : ℝ) (p : Ctx m) (u : Atom)
    (hu : ∑ i,(u i)^2=1) : initialError N m τ (mix u p) ≤ 3*∑ j,initialError N m τ (mix (quadDir j) p) := by
  let G (v : Atom) (q : Fin N×Fin N) := gramCenter τ q (mix v p)
  let R (v : Atom) (i : Fin N) := rowCenter τ i (mix v p)
  have eg : G u = fun i => ∑ j, qWeight u j*G (quadDir j) i := funext (gram_interp hm τ p u hu)
  have er : R u = fun i => ∑ j, qWeight u j*R (quadDir j) i := funext (row_interp hm τ p u hu)
  change finiteRms (G u)+finiteRms (R u) ≤ 3*∑ j,(finiteRms (G (quadDir j))+finiteRms (R (quadDir j)))
  rw [eg,er,Finset.sum_add_distrib,mul_add]
  exact add_le_add (finiteRms_cap _ _ (qcap u hu)) (finiteRms_cap _ _ (qcap u hu))

open CircleReadoutMixing

/-- Exact linearity of the original grid mean in a shared-hidden triple of readouts. -/
theorem gridMean_mix (N m : ℕ) (p : Triple m) (u : Atom) :
    gridMean N m (mixedSeed u p)=∑ i, u i*gridMean N m (mixedSeed (Pi.single i 1) p) := by
  change gridMean N m (mix u p) = ∑ i, u i*gridMean N m (mix (Pi.single i 1) p)
  unfold gridMean
  simp_rw [output_linear p u,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def mixBudget {N : ℕ} [NeZero N] (ho : Odd N) (m : ℕ) (p : Triple m) :=
  ∑ j,seedBudget ho m (mixedSeed (linDir j) p)
def mixError (N m : ℕ) [NeZero N] (τ : ℝ) (p : Triple m) :=
  3*∑ j,initialError N m τ (mixedSeed (quadDir j) p)

theorem mixBudget_dominates {N m : ℕ} [NeZero N] (ho : Odd N) (p : Triple m) (u : Atom) (hu : ∑ i,(u i)^2=1) :
    seedBudget ho m (mixedSeed u p)≤mixBudget ho m p := budget_dom ho p u hu

theorem mixError_dominates {N m : ℕ} [NeZero N] (hm : 0<m) (τ : ℝ) (p : Triple m) (u : Atom) (hu : ∑ i,(u i)^2=1) :
    initialError N m τ (mixedSeed u p)≤mixError N m τ p := error_dom hm τ p u hu

theorem mixBudget_nonneg {N m : ℕ} [NeZero N] (ho : Odd N) (p : Triple m) : 0≤mixBudget ho m p :=
  sum_nonneg (fun _ _ => seedBudget_nonneg _ _ _)
theorem mixError_nonneg {N m : ℕ} [NeZero N] (τ : ℝ) (p : Triple m) : 0≤mixError N m τ p :=
  mul_nonneg (by norm_num) (sum_nonneg (fun _ _ => initialError_nonneg _ _))

private theorem initialError_meas {N m : ℕ} [NeZero N] (hm : 0<m) (τ : ℝ) : Measurable (initialError N m τ) := by
  have H (q : InitIndex N) := sampleAverage_meas (m:=m) (initTest_meas N τ 0 q)
  have G (i j : Fin N) : Measurable (fun ω : Seed m => gridGram τ ω (startGates ω) i j) := by
    change Measurable fun ω : Seed m => entry τ ω ω (circleInput N i) (circleInput N j)
      (fun k => actualGate (pre ω k (circleInput N i))) (fun k => actualGate (pre ω k (circleInput N j)))
    simp_rw [weightedAtom_initial hm]; exact H (.inr (.inr (j,some i)))
  have R (i : Fin N) : Measurable (fun ω : Seed m => populationRow τ ω (startGates ω) i) := by
    simp_rw [CircleInitializationConcentration.angular_entry_initial hm]; exact H (.inr (.inr (i,none)))
  unfold initialError finiteRms
  fun_prop

theorem mixBudget_measurable {N : ℕ} [NeZero N] (ho : Odd N) (m : ℕ) : Measurable (mixBudget ho m) :=
  Finset.measurable_sum _ (fun j _ => (seedBudget_continuous ho m).measurable.comp (mixed_preserving m (linDir j) (lin_unit j)).measurable)

theorem mixError_measurable {N m : ℕ} [NeZero N] (hm : 0<m) (τ : ℝ) : Measurable (mixError N m τ) :=
  (Finset.measurable_sum _ (fun j _ => (initialError_meas (N:=N) hm τ).comp (mixed_preserving m (quadDir j) (quad_unit j)).measurable)).const_mul _

private theorem direction_sum {m : ℕ} (F : Seed m→ℝ) (dirs : Fin 6 → Atom) (hu : ∀ j, ∑ i, (dirs j i)^2=1)
    (hf : MemLp F 4 (seedLaw m)) (C : ℝ) (hC : lpNorm F 4 (seedLaw m)≤C) :
    MemLp (fun p => ∑ j, F (mixedSeed (dirs j) p)) 4 (tripleLaw m) ∧
    lpNorm (fun p => ∑ j, F (mixedSeed (dirs j) p)) 4 (tripleLaw m)≤6*C := by
  let f (j : Fin 6) := F ∘ mixedSeed (dirs j)
  have hm (j : Fin 6) : MemLp (f j) 4 (tripleLaw m) := hf.comp_measurePreserving (mixed_preserving _ _ (hu j))
  have hb (j : Fin 6) : lpNorm (f j) 4 (tripleLaw m)≤C := by
    rw [←toReal_eLpNorm,eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (mixed_preserving _ _ (hu j)),toReal_eLpNorm]
    exact hC
  refine ⟨memLp_finsetSum _ (fun j _ => hm j),?_⟩
  have hs := (lpNorm_sum_le (s:=Finset.univ) (fun j _ => hm j) (by norm_num)).trans (Finset.sum_le_sum (fun j _ => hb j))
  have eq : (∑ j,f j) = fun p => ∑ j,F (mixedSeed (dirs j) p) := by funext p; simp [Finset.sum_apply,f]
  rw [eq] at hs
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using hs

/-- The six directions preserve the Gaussian seed measure, giving the same
L⁴ order for the uniform envelope as for one run. -/
theorem mixBudget_fourth {N m : ℕ} [NeZero N] (ho : Odd N) (hm : 0<m) :
    MemLp (mixBudget ho m) 4 (tripleLaw m) ∧ lpNorm (mixBudget ho m) 4 (tripleLaw m)≤6*budgetConstant*sqrt N := by
  unfold mixBudget
  simpa only [mul_assoc] using direction_sum _ linDir lin_unit (seedBudget_mem hm ho) _ (seedBudget_lp4 hm ho)

theorem mixError_fourth {N m : ℕ} [NeZero N] (hm : 0<m) (τ : ℝ) (ht : |τ|≤2) :
    MemLp (mixError N m τ) 4 (tripleLaw m) ∧ lpNorm (mixError N m τ) 4 (tripleLaw m)≤108*markConstant/sqrt m := by
  have hb := initialError_fourth (N:=N) hm τ ht
  have hs := direction_sum _ quadDir quad_unit hb.1 _ hb.2
  refine ⟨hs.1.const_mul 3,?_⟩
  change lpNorm ((3:ℝ) • (fun p => ∑ j, initialError N m τ (mixedSeed (quadDir j) p))) _ _ ≤ _
  rw [lpNorm_const_smul]
  rw [show ((‖(3:ℝ)‖₊:NNReal):ℝ)=3 by change |(3:ℝ)|=3;norm_num]
  apply (mul_le_mul_of_nonneg_left hs.2 (by norm_num : (0:ℝ)≤3)).trans_eq
  ring

end CircleMixingEnvelopes
