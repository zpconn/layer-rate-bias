module

public import CircleTeacherRKHS
public import CircleFirstCosine
public import CircleSpectralPathLength
import all CircleTeacherRKHS
import all CircleGridMoments
import all CircleGridSpectrum
import all CircleSpectralPathLength
import all CircleTangentDrift
import all CircleKernelIdentification
import all CircleReferenceMoments
import all CircleEscapeBridge
import all CircleEscape
import all CircleInitializationConcentration
import Mathlib.Tactic

/-! Finite-width reference moments for the first cosine amplitude. Both measurements use
the same initialized Gaussian network. The grid includes the two distinct first harmonics
for every N ≥ 3, whether N is odd or even. -/
public section
noncomputable section
namespace CircleFirstCosineReference
open CircleEscape CircleEscapeBridge CircleReferenceMoments CircleInitializationConcentration
  CircleGridSpectrum CircleKernelIdentification CircleTeacherRKHS CircleSpectralPathLength
  MeasureTheory ProbabilityTheory Real Finset
open scoped InnerProductSpace
variable {N m : ℕ}

def cosine (i : Fin N) := cos (physicalAngle i)
def gridAmplitude (N : ℕ) (f : ℂ→ℝ) := (2/(N:ℝ))*∑ i,f (gridPoint N i)*cosine i

def firstEigen (N : ℕ) (τ : ℝ) := aliasValue (tangentCoeff τ) (1:ZMod N)
def offAlias (N : ℕ) (τ : ℝ) :=
  ∑' k : ℤ, if k≠1 ∧ (k:ZMod N)=1 then tangentCoeff τ k else 0
def firstWeight (N : ℕ) := tangentCoeff 1 1/firstEigen N 1

theorem firstEigen_eq (N : ℕ) {τ : ℝ} (hτ : 0≤τ) (hu : τ≤2) :
    firstEigen N τ=tangentCoeff τ 1+offAlias N τ := by
  let a := tangentCoeff τ
  let g (k : ℤ) := if k≠1 ∧ (k:ZMod N)=1 then a k else 0
  have hg : Summable g := ((tangentCoeff_summable _ hτ hu).indicator
    {k : ℤ | k≠1 ∧ (k:ZMod N)=1}).congr fun _ => by simp [g,a,Set.indicator_apply]
  have hδ : HasSum (fun k : ℤ => if k=1 then a 1 else 0) (a 1) := hasSum_ite_eq _ _
  have h := (hδ.add hg.hasSum).tsum_eq
  refine (tsum_congr (f:=fun k : ℤ => if (k:ZMod N)=1 then a k else 0) ?_).trans h
  intro k
  by_cases hk : k=1 <;> simp [hk,g]

theorem firstCoeff (τ : ℝ) : tangentCoeff τ 1=(1+τ)/8 := by norm_num [tangentCoeff]
theorem firstWeight_pos (N : ℕ) : 0<firstWeight N := by
  have h : 0≤offAlias N 1 := tsum_nonneg fun k => by
    dsimp; split <;> first | exact tangentCoeff_nonneg (by norm_num) _ | exact le_rfl
  unfold firstWeight
  rw [firstEigen_eq N (by norm_num) (by norm_num),firstCoeff]
  positivity

private theorem char_cos [NeZero N] (i : Fin N) :
    (char (1:ZMod N) (ZMod.finEquiv N i)).re=cosine i := by
  rw [←show ((1:ℤ):ZMod N)=1 by simp,←sampled_fourier,gridAngle_fin,fourier_coe_apply]
  push_cast
  have hπ : (π:ℂ)≠0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  rw [show 2*(π:ℂ)*Complex.I*1*(physicalAngle i:ℂ)/((π:ℂ)- -(π:ℂ))=
    (physicalAngle i:ℂ)*Complex.I by field_simp;ring]
  simp [Complex.exp_mul_I,cosine,Complex.cos_ofReal_re]

theorem cosine_eigen [NeZero N] (τ : ℝ) (hτ : 0≤τ) (hu : τ≤2) (i : Fin N) :
    (∑ j,sampledMatrix τ i j*cosine j)/(N:ℝ)=firstEigen N τ*cosine i := by
  let a (s : ZMod N) : ℂ := if s=1 then 1 else 0
  have h := matrix_synth τ hτ hu a i
  simpa [synth,a,ite_mul,Finset.sum_ite_eq',Complex.re_ofReal_mul,char_cos,eigen,firstEigen] using h

theorem cosine_sums (hn : 3≤N) :
    (∑ i : Fin N,cosine i)=0 ∧ (∑ i : Fin N,(cosine i)^2)=(N:ℝ)/2 := by
  constructor
  · simpa [Complex.inner,cosine,gridPoint,physicalAngle] using CircleGridMoments.projection_sum N hn (1:ℂ)
  · simpa [Complex.inner,cosine,gridPoint,physicalAngle] using CircleGridMoments.projection_sq_sum N hn (1:ℂ)

theorem grid_teacher (hn : 3≤N) : gridAmplitude N (fun x => 1+x.re)=1 := by
  have hz : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have h := cosine_sums hn
  simp only [gridAmplitude,add_mul,one_mul,show ∀ i : Fin N,(gridPoint N i).re=cosine i from fun _ => rfl,
    ←sq,sum_add_distrib,h.1,h.2,zero_add]
  field_simp

private def gweight (i : Fin N) := 2/(N:ℝ)*cosine i
private def P : H := (1/2:ℝ) • linearSection
private def D (N : ℕ) : H := ∑ i : Fin N,gweight i • gridSection i

private theorem P_eval (u : ℝ) : ⟪P,sectionAt u⟫_ℝ=cos u/4 := by
  rw [P,real_inner_smul_left,linear_section];ring

private theorem P_P : ⟪P,P⟫_ℝ=1/4 := by
  conv_lhs => rhs;rw [P,linearSection]
  rw [real_inner_smul_right,inner_sub_right,P_eval,P_eval,cos_zero,cos_pi];ring

private theorem P_D (hn : 3≤N) : ⟪P,D N⟫_ℝ=1/4 := by
  have hz : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  simp only [D,inner_sum,real_inner_smul_right,gridSection,P_eval,show ∀ i : Fin N,cos (physicalAngle i)=cosine i from fun _ => rfl,gweight]
  simp_rw [show ∀ c:ℝ,2/(N:ℝ)*c*(c/4)=(1/(2*N))*c^2 by intro c;ring]
  rw [←mul_sum,(cosine_sums hn).2];field_simp;norm_num

private theorem D_eval [NeZero N] (i : Fin N) :
    ⟪gridSection i,D N⟫_ℝ=2*firstEigen N 0*cosine i := by
  simp only [D,inner_sum,real_inner_smul_right,grid_covariance,gweight]
  simp_rw [show ∀ j : Fin N,2/(N:ℝ)*cosine j*sampledMatrix 0 i j=
    2/(N:ℝ)*(sampledMatrix 0 i j*cosine j) by intro;ring]
  rw [←mul_sum,div_mul_eq_mul_div,mul_div_assoc,cosine_eigen 0 (by norm_num) (by norm_num)]
  ring

private theorem D_D [NeZero N] (hn : 3≤N) : ⟪D N,D N⟫_ℝ=2*firstEigen N 0 := by
  have hz := NeZero.ne (N:ℝ)
  conv_lhs => lhs;rw [D]
  simp only [sum_inner,real_inner_smul_left,D_eval,gweight]
  simp_rw [show ∀ c:ℝ,2/(N:ℝ)*c*(2*firstEigen N 0*c)=
    (4*firstEigen N 0/N)*c^2 by intro;ring]
  rw [←mul_sum,(cosine_sums hn).2];field_simp;ring

private def dFn (N : ℕ) (w : ℝ×ℝ) := ∑ i : Fin N,gweight i*phi (physicalAngle i) w
private def comb (N : ℕ) (x y : ℝ) (w : ℝ×ℝ) := x*(w.1/2)+y*dFn N w
private def neuron (N : ℕ) (x y : ℝ) (z : Atom) := z 0*comb N x y (z 1,z 2)

private theorem comb_mem (N : ℕ) (x y : ℝ) (p : NNReal) :
    MemLp (comb N x y) (p:ENNReal) standardPair := by
  have hd := memLp_finsetSum univ (fun (i : Fin N) _ => (phi_mem p (physicalAngle i)).const_mul (gweight i))
  unfold comb dFn
  simp only [div_eq_mul_inv]
  exact (((coord_mem p).1.mul_const (2:ℝ)⁻¹).const_mul x).add (hd.const_mul y)

private theorem D_fn (N : ℕ) : ⇑(D N) =ᵐ[standardPair] dFn N := by
  apply (Lp.coeFn_finsetSum _ _).trans
  have hf (i : Fin N) : ⇑(gweight i • gridSection i) =ᵐ[standardPair]
      fun w => gweight i*phi (physicalAngle i) w := by
    filter_upwards [Lp.coeFn_smul (gweight i) (gridSection i),(phi_mem 2 (physicalAngle i)).coeFn_toLp] with w h1 h2
    rw [h1];change gweight i*(gridSection i w)=_
    rw [show gridSection i w=phi (physicalAngle i) w from h2]
  exact (eventuallyEq_sum (s:=univ) fun i _ => hf i).trans (by filter_upwards with w; simp [dFn])

private theorem P_fn : ⇑P =ᵐ[standardPair] fun w => w.1/2 := by
  filter_upwards [Lp.coeFn_smul (1/2:ℝ) linearSection,linear_coeff] with w h1 h2
  change ((1/2:ℝ) • linearSection) w=_
  rw [h1];change (1/2)*linearSection w=_
  rw [h2];ring

private theorem combo_second [NeZero N] (hn : 3≤N) (x y : ℝ) :
    (∫ w,comb N x y w^2 ∂standardPair)=x^2/4+x*y/2+y^2*(2*firstEigen N 0) := by
  let V := x • P+y • D N
  have he : ⇑V=ᵐ[standardPair] comb N x y := by
    filter_upwards [Lp.coeFn_add (x • P) (y • D N),Lp.coeFn_smul x P,Lp.coeFn_smul y (D N),
      P_fn,D_fn N] with w ha hx hy hp hd
    change (x • P + y • D N) w=_
    rw [ha];change (x • P) w+(y • D N) w=_
    rw [hx,hy];change x*(P w)+y*(D N w)=_;rw [hp,hd];rfl
  have vi : (∫ w,comb N x y w^2 ∂standardPair)=⟪V,V⟫_ℝ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [he] with w hw
    change _=V w*V w
    rw [hw,sq]
  rw [vi]
  simp only [V,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    P_P,P_D hn,D_D hn,show ⟪D N,P⟫_ℝ=1/4 by rw [real_inner_comm,P_D hn]]
  ring

private theorem neuron_moments [NeZero N] (hn : 3≤N) (x y : ℝ) :
    MemLp (neuron N x y) 2 atomLaw ∧ (∫ z,neuron N x y z ∂atomLaw)=0 ∧
      variance (neuron N x y) atomLaw=x^2/4+x*y/2+y^2*(2*firstEigen N 0) := by
  have ha : MemLp (fun z : ℝ×(ℝ×ℝ) => z.1) 4 (G.prod standardPair) :=
    (memLp_id_gaussianReal 4).comp_measurePreserving measurePreserving_fst
  have hc : MemLp (fun z : ℝ×(ℝ×ℝ) => comb N x y z.2) 4 (G.prod standardPair) :=
    (comb_mem N x y 4).comp_measurePreserving measurePreserving_snd
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)];norm_num⟩
  have hi : MemLp (neuron N x y) 2 atomLaw := (ha.fun_mul hc).comp_measurePreserving CircleReferenceMoments.split_preserving
  have hm : (∫ z,neuron N x y z ∂atomLaw)=0 := by
    change (∫ z,(fun t : ℝ×(ℝ×ℝ) => t.1*comb N x y t.2) (CircleReferenceMoments.split z) ∂atomLaw)=0
    rw [CircleReferenceMoments.split_preserving.integral_comp' (fun t : ℝ×(ℝ×ℝ) => t.1*comb N x y t.2),
      integral_prod_mul (fun a : ℝ => a) (comb N x y),integral_id_gaussianReal,zero_mul]
  refine ⟨hi,hm,?_⟩
  rw [variance_eq_sub hi,hm]
  simp only [Pi.pow_apply,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,sub_zero]
  change (∫ z,(fun t : ℝ×(ℝ×ℝ) => (t.1*comb N x y t.2)^2) (CircleReferenceMoments.split z) ∂atomLaw)=_
  rw [CircleReferenceMoments.split_preserving.integral_comp' (fun t:ℝ×(ℝ×ℝ)=>(t.1*comb N x y t.2)^2)]
  simp_rw [mul_pow]
  rw [integral_prod_mul (fun a : ℝ => a^2) (fun w => comb N x y w^2),
    CircleKernelIdentification.gaussian_second,one_mul,combo_second hn]

def pop (m : ℕ) (z : Seed m) :=
  CircleFirstCosine.amplitude (output (1/√m) (initial z))

def grid (N m : ℕ) (z : Seed m) := gridAmplitude N (output (1/√m) (initial z))

def reference (N m : ℕ) (b : ℝ) (z : Seed m) := pop m z-b*(grid N m z-1)

private theorem combine_actual (hm : 0<m) (N : ℕ) (x y : ℝ) (z : Seed m) :
    x*pop m z+y*grid N m z=√m*sampleAverage (neuron N x y) z := by
  have hm' : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hs : √(m:ℝ)≠0 := sqrt_ne_zero'.mpr (by exact_mod_cast hm)
  have hscale : √(m:ℝ)*(m:ℝ)⁻¹=1/√m := by
    field_simp [hs,hm'];nlinarith [sq_sqrt (Nat.cast_nonneg m)]
  let F (j : Fin m) (i : Fin N) := phi (physicalAngle i) (z (j,1),z (j,2))
  have hc (i : Fin N) : output (1/√(m:ℝ)) (initial z) (gridPoint N i)=1/√m*∑ j,z (j,0)*F j i := by
    simp [output,initial,F,feature_coord]
  have gd : grid N m z = 1/√m*∑ j,z (j,0)*dFn N (z (j,1),z (j,2)) := by
    unfold grid gridAmplitude
    simp only [hc,dFn,gweight,mul_sum,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro i _;dsimp [F];ring
  rw [pop,CircleFirstCosine.actual_amplitude,gd,sampleAverage,←mul_assoc (√(m:ℝ)),hscale]
  simp only [initial,neuron,comb,mul_add,Finset.mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro j _;ring

private theorem combo_moments [NeZero N] (hn : 3≤N) (hm : 0<m) (x y : ℝ) :
    let f (z : Seed m) := x*pop m z+y*grid N m z
    MemLp f 2 (seedLaw m) ∧ (∫ z,f z ∂seedLaw m)=0 ∧
      variance f (seedLaw m)=x^2/4+x*y/2+y^2*(2*firstEigen N 0) := by
  let f := neuron N x y
  have id : (fun z : Seed m => x*pop m z+y*grid N m z)=fun z => √m*sampleAverage f z := funext (combine_actual hm N x y)
  dsimp only
  rw [id]
  obtain ⟨mem,me,v⟩ := neuron_moments hn x y
  refine ⟨(average_mem (m:=m) mem).const_mul _,?_,?_⟩
  · rw [integral_const_mul,average_mean hm mem,me,mul_zero]
  · rw [variance_const_mul,average_variance hm mem,v,sq_sqrt (Nat.cast_nonneg m)]
    field_simp [show (m:ℝ)≠0 by exact_mod_cast hm.ne']

/-- Second moments of the continuum and grid cosine measurements of the same physical
network initialization. The covariance contribution is present at every positive width. -/
theorem joint_moments [NeZero N] (hn : 3≤N) (hm : 0<m) :
    (∫ z,pop m z ∂seedLaw m)=0 ∧ (∫ z,grid N m z ∂seedLaw m)=0 ∧
    variance (pop m) (seedLaw m)=2*tangentCoeff 0 1 ∧
    covariance (pop m) (grid N m) (seedLaw m)=2*tangentCoeff 0 1 ∧
    variance (grid N m) (seedLaw m)=2*(tangentCoeff 0 1+offAlias N 0) := by
  have p := combo_moments hn hm 1 0
  have g := combo_moments hn hm 0 1
  have pg := (combo_moments hn hm 1 1).2.2
  simp only [one_mul,zero_mul,add_zero,zero_add,one_pow,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
    not_false_eq_true,mul_zero,zero_div] at p g pg
  have c := variance_fun_add p.1 g.1
  rw [pg,p.2.2,g.2.2] at c
  rw [←firstEigen_eq N (by norm_num) (by norm_num),firstCoeff]
  exact ⟨p.2.1,g.2.1,by linarith [p.2.2],by linarith,g.2.2⟩

/-- Exact same-seed finite-width mean and variance for every deterministic reference
weight, including the kernel interpolation weight. -/
theorem reference_moments [NeZero N] (hn : 3≤N) (hm : 0<m) (b : ℝ) :
    (∫ z,reference N m b z ∂seedLaw m)=b ∧ variance (reference N m b) (seedLaw m)=
      2*((1-b)^2*tangentCoeff 0 1+b^2*offAlias N 0) := by
  have c := combo_moments hn hm 1 (-b)
  let f (z : Seed m) := 1*pop m z+-b*grid N m z
  have id : reference N m b=fun z => b+f z := by ext z;dsimp [reference,f];ring
  rw [id,integral_add (integrable_const _) (c.1.integrable (by norm_num)),
    variance_const_add c.1.aestronglyMeasurable,integral_const,c.2.1,c.2.2,
    firstEigen_eq N (by norm_num) (by norm_num),firstCoeff]
  simp
  ring

theorem interpolation_moments [NeZero N] (hn : 3≤N) (hm : 0<m) :
    (∫ z,reference N m (firstWeight N) z ∂seedLaw m)=firstWeight N ∧
      variance (reference N m (firstWeight N)) (seedLaw m)=
        2*((1-firstWeight N)^2*tangentCoeff 0 1+(firstWeight N)^2*offAlias N 0) :=
  reference_moments hn hm _

/-- The off-frequency variance counts every alias 1+ℓN except ℓ=0. -/
theorem offAlias_progression [NeZero N] (τ : ℝ) : offAlias N τ=
    ∑' l : ℤ, if l=0 then 0 else tangentCoeff τ (1+(N:ℤ)*l) := by
  let g (l : ℤ) := 1+(N:ℤ)*l
  let f (k : ℤ) := if k≠1 ∧ (k:ZMod N)=1 then tangentCoeff τ k else 0
  have hN : (N:ℤ)≠0 := by exact_mod_cast NeZero.ne N
  have inj : Function.Injective g := by
    intro x y he
    exact (mul_left_cancel₀ hN) (add_left_cancel he)
  have supp : Function.support f⊆Set.range g := by
    intro k hk
    have hd : (k:ZMod N)=1 := by
      by_contra! bad
      exact hk (by simp [f,bad])
    obtain ⟨l,hl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (k-1) N).mp (by simp [hd])
    exact ⟨l,by unfold g;omega⟩
  change ∑' k,f k=_
  rw [←inj.tsum_eq supp]
  apply tsum_congr
  intro l
  by_cases hl : l=0
  · simp [hl,g,f]
  · have hg : g l≠1 := by dsimp [g];simpa using mul_ne_zero hN hl
    have hcast : ((g l:ℤ):ZMod N)=1 := by simp [g]
    simp [hl,hg,hcast,f,g]

private theorem alias_high (hn : 3≤N) {l : ℤ} (hl : l≠0) : (1+(N:ℤ)*l).natAbs≠1 := by
  have h : (3:ℤ)≤N := by exact_mod_cast hn
  rcases le_total l 0 with hs|hs
  · have hh := mul_le_mul_of_nonneg_left (show l≤ -1 by omega) (show (0:ℤ)≤N by positivity)
    rw [mul_neg_one] at hh;omega
  · have hh := mul_le_mul_of_nonneg_left (show 1≤l by omega) (show (0:ℤ)≤N by positivity)
    rw [mul_one] at hh;omega

/-- On odd grids, only odd nonzero multiples of N contribute to the first-harmonic alias. -/
theorem odd_alias [NeZero N] (hn : 3≤N) (ho : Odd N) (τ : ℝ) :
    offAlias N τ=∑' l : ℤ, if Odd l then CircleSpectrum.ntkEven τ (1+(N:ℝ)*(l:ℝ)) else 0 := by
  rw [offAlias_progression]
  apply tsum_congr
  intro l
  by_cases hl : l=0
  · simp [hl]
  have he : Even (1+(N:ℤ)*l) ↔ Odd l := by
    simp [Int.even_add,Int.even_mul,Int.even_coe_nat,Nat.not_even_iff_odd.mpr ho,Int.not_even_iff_odd]
  simp only [ite_eq_right hl,tangentCoeff,he,alias_high hn hl,ite_false,Int.cast_add,
    Int.cast_one,Int.cast_mul,Int.cast_natCast]

theorem even_alias [NeZero N] (hn : 3≤N) (he : Even N) (τ : ℝ) : offAlias N τ=0 := by
  rw [offAlias_progression]
  rw [←tsum_zero (β:=ℤ) (α:=ℝ)]
  apply tsum_congr
  intro l
  by_cases hl : l=0
  · simp [hl]
  have ho : ¬Even (1+(N:ℤ)*l) := by simp [Int.even_add,Int.even_coe_nat,he]
  simp [hl,tangentCoeff,ho,alias_high hn hl]

local instance : Fact (0<π- -π) := ⟨by linarith [pi_pos]⟩

private theorem phase_re (u : ℝ) : (fourier (-1) (u:CircleTeacherRKHS.Angle)).re=cos u := by
  rw [fourier_neg,Complex.conj_re,fourier_coe_apply]
  push_cast
  have hπ : (π:ℂ)≠0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  rw [show 2*(π:ℂ)*Complex.I*1*(u:ℂ)/((π:ℂ)- -(π:ℂ))=(u:ℂ)*Complex.I by field_simp;ring]
  simp [Complex.exp_mul_I,Complex.cos_ofReal_re]

private theorem phase_add (x y : CircleTeacherRKHS.Angle) :
    fourier (-1) (x+y)=fourier (-1) x*fourier (-1) y := by
  simp only [fourier_apply,zsmul_add,AddCircle.toCircle_add,Circle.coe_mul]

private theorem first_row (τ : ℝ) (y : CircleTeacherRKHS.Angle) :
    (∫ x, (fourier (-1) x).re*(periodicTangent τ (x-y)).re ∂AddCircle.haarAddCircle)=
      tangentCoeff τ 1*(fourier (-1) y).re := by
  let F (x : CircleTeacherRKHS.Angle) := fourier (-1) x*periodicTangent τ (x-y)
  have hf : Integrable F AddCircle.haarAddCircle := by
    have hc : Continuous F := (fourier (-1)).continuous.mul ((periodicTangent τ).continuous.comp
      (continuous_id.sub continuous_const))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have fac (x : CircleTeacherRKHS.Angle) : F x=fourier (-1) y*(fourier (-1) (x-y)*periodicTangent τ (x-y)) := by
    unfold F
    rw [show fourier (-1) x=fourier (-1) (x-y)*fourier (-1) y by rw [←phase_add,sub_add_cancel]]
    ring
  have eqn : (∫ x,F x ∂AddCircle.haarAddCircle)=fourier (-1) y*(tangentCoeff τ 1:ℂ) := by
    simp_rw [fac]
    rw [integral_const_mul,integral_sub_right_eq_self
      (fun x : CircleTeacherRKHS.Angle => fourier (-1) x*periodicTangent τ x)]
    exact congrArg (fun z : ℂ => fourier (-1) y*z) (periodicTangent_coeff τ 1)
  have h := congrArg Complex.re eqn
  change Complex.reCLM (∫ x,F x ∂AddCircle.haarAddCircle)=_ at h
  rw [←Complex.reCLM.integral_comp_comm hf] at h
  simpa only [F,Complex.reCLM_apply,Complex.mul_re,periodicTangent_real,mul_zero,sub_zero,
    Complex.ofReal_re,Complex.ofReal_im,mul_comm,zero_mul] using h

/-- The actual first-cosine integral of the tangent section at source angle a. -/
theorem tangent_amplitude (τ a : ℝ) :
    (∫ u in 0..2*π,cartesianKernel τ a u*cos u)/π=2*tangentCoeff τ 1*cos a := by
  let P := π- -π
  let y : CircleTeacherRKHS.Angle := a
  let F (x : CircleTeacherRKHS.Angle) := (fourier (-1) x).re*(periodicTangent τ (x-y)).re
  have hh := AddCircle.intervalIntegral_preimage P 0 F
  rw [AddCircle.volume_eq_smul_haarAddCircle,integral_smul_measure,
    ENNReal.toReal_ofReal (by dsimp [P];linarith [pi_pos])] at hh
  have hF (u : ℝ) : F (u:CircleTeacherRKHS.Angle)=cartesianKernel τ a u*cos u := by
    rw [show F (u:CircleTeacherRKHS.Angle)=(fourier (-1) (u:CircleTeacherRKHS.Angle)).re*(periodicTangent τ ((u:CircleTeacherRKHS.Angle)-(a:CircleTeacherRKHS.Angle))).re from rfl,
       phase_re,←AddCircle.coe_sub,periodicTangent_cartesian,mul_comm]
  have hi : (∫ x,F x ∂AddCircle.haarAddCircle)=tangentCoeff τ 1*cos a := by
    rw [show (∫ x,F x ∂AddCircle.haarAddCircle)=_ from first_row τ y,phase_re]
  simp_rw [hF] at hh
  rw [hi] at hh
  simp only [zero_add,smul_eq_mul] at hh
  rw [show P=2*π by dsimp [P];ring] at hh
  rw [hh]
  field_simp

/-- In particular the finite kernel solve has exactly the claimed normalization. -/
theorem interpolation_row [NeZero N] (i : Fin N) :
    (∫ u in 0..2*π,cartesianKernel 1 (physicalAngle i) u*cos u)/π=
      firstWeight N*(2/(N:ℝ)*∑ j,sampledMatrix 1 i j*cosine j) := by
  rw [tangent_amplitude,show cos (physicalAngle i)=cosine i from rfl,
    div_mul_eq_mul_div,mul_div_assoc,cosine_eigen 1 (by norm_num) (by norm_num)]
  have h : firstEigen N 1≠0 := by
    intro hz; have hh := firstWeight_pos N; simp [firstWeight,hz] at hh
  unfold firstWeight;field_simp

/-- Any exact solution of the finite interpolation equations delivers the same first
cosine amplitude at the original initialization. -/
theorem kernel_solve [NeZero N] (hn : 3≤N) (z : Seed m) (a : Fin N→ℝ)
    (fit : ∀ j : Fin N, output (1/√m) (initial z) (gridPoint N j)+
      ∑ i,a i*sampledMatrix 1 i j=1+cosine j) :
    pop m z+ (∫ u in 0..2*π,(∑ i,a i*cartesianKernel 1 (physicalAngle i) u)*cos u)/π=
      reference N m (firstWeight N) z := by
  have hcont (i : Fin N) : Continuous (cartesianKernel 1 (physicalAngle i)) := by
    have hc : Continuous (fun u : ℝ => (periodicTangent 1
        ((u-physicalAngle i:ℝ):CircleTeacherRKHS.Angle)).re) :=
      Complex.continuous_re.comp ((periodicTangent 1).continuous.comp
        ((AddCircle.continuous_mk' _).comp (continuous_id.sub continuous_const)))
    exact hc.congr fun u => periodicTangent_cartesian 1 (physicalAngle i) u
  have hind (i : Fin N) : IntervalIntegrable
      (fun u => a i*(cartesianKernel 1 (physicalAngle i) u*cos u)) volume 0 (2*π) :=
    (continuous_const.mul ((hcont i).mul continuous_cos)).intervalIntegrable _ _
  have obs (j : Fin N) : (∑ i,a i*sampledMatrix 1 i j)=(1+cosine j)-
      output (1/√m) (initial z) (gridPoint N j) := by linarith [fit j]
  simp_rw [sum_mul,mul_assoc,intervalIntegral.integral_finsetSum (fun i _ => hind i),
    intervalIntegral.integral_const_mul,Finset.sum_div,mul_div_assoc,interpolation_row]
  have transform : (∑ i : Fin N,a i*(firstWeight N*(2/(N:ℝ)*∑ j,sampledMatrix 1 i j*cosine j)))=
      firstWeight N*(2/(N:ℝ)*(∑ j,(∑ i,a i*sampledMatrix 1 i j)*cosine j)) := by
    simp only [mul_sum,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl;intro j _
    apply sum_congr rfl;intro i _;ring
  rw [transform]
  simp_rw [obs,sub_mul,Finset.sum_sub_distrib,mul_sub]
  have ht := grid_teacher hn
  change 2/(N:ℝ)*(∑ j,(1+cosine j)*cosine j)=1 at ht
  rw [ht]
  change pop m z+(firstWeight N*1-firstWeight N*grid N m z)=pop m z-firstWeight N*(grid N m z-1)
  ring

theorem even_reference [NeZero N] (hn : 3≤N) (he : Even N) (hm : 0<m) :
    firstWeight N=1 ∧ reference N m (firstWeight N)=ᵐ[seedLaw m] fun _ => 1 := by
  have w : firstWeight N=1 := by
    rw [firstWeight,firstEigen_eq N (by norm_num) (by norm_num),even_alias hn he,firstCoeff];norm_num
  have mom := interpolation_moments hn hm
  rw [w,even_alias hn he] at mom
  have h := (combo_moments hn hm 1 (-1)).1
  have mem : MemLp (reference N m 1) 2 (seedLaw m) := by
    have eqn : reference N m 1=fun z => 1+(1*pop m z+ -1*grid N m z) := by ext z;dsimp [reference];ring
    rw [eqn];exact (memLp_const _).add h
  refine ⟨w,?_⟩
  rw [w]
  filter_upwards [ae_eq_integral_of_variance_eq_zero mem (by simpa using mom.2)] with z hz
  exact hz.trans mom.1

/-- On the benchmark's odd grid the tangent matrix always admits a solution, for every
realized initial network and the specified labels. -/
theorem realized_interpolation [NeZero N] (hn : 3≤N) (ho : Odd N) (z : Seed m) :
    ∃ a : Fin N→ℝ, (∀ j, output (1/√m) (initial z) (gridPoint N j)+
      ∑ i,a i*sampledMatrix 1 i j=1+cosine j) ∧
      pop m z+(∫ u in 0..2*π,(∑ i,a i*cartesianKernel 1 (physicalAngle i) u)*cos u)/π=
        reference N m (firstWeight N) z := by
  let G := CircleTangentDrift.gramOp (sampledMatrix (N:=N) 1)
  let b (j : Fin N) := 1+cosine j-output (1/√m) (initial z) (gridPoint N j)
  have hi : Function.Injective G := by
    intro x y hxy
    have hg := gramOp_gap hn ho 1 (by norm_num) (by norm_num) (x-y)
    change _ ≤ inner ℝ (x-y) (G (x-y)) at hg
    rw [map_sub,hxy,sub_self,inner_zero_right] at hg
    have hp : 0<1/(π*N)^2 := by positivity
    have hs := nonpos_of_mul_nonpos_right hg hp
    exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [sq_nonneg ‖x-y‖]))
  have sur : Function.Surjective G.toLinearMap := LinearMap.injective_iff_surjective.mp hi
  obtain ⟨v,hv⟩ := sur (WithLp.toLp 2 b)
  let a (i : Fin N) := v i/(N:ℝ)
  have fit (j : Fin N) : output (1/√m) (initial z) (gridPoint N j)+
      ∑ i,a i*sampledMatrix 1 i j=1+cosine j := by
    have hh := congrArg (fun u : EuclideanSpace ℝ (Fin N) => u j) hv
    change CircleTangentDrift.gramOp (sampledMatrix 1) v j=b j at hh
    rw [CircleTangentDrift.gramOp_apply,Finset.sum_div] at hh
    have symm (i : Fin N) : sampledMatrix 1 j i=sampledMatrix 1 i j := by
      simp [sampledMatrix_cartesian,cartesian_kernel_isotropic,abs_sub_comm]
    simp_rw [symm,show ∀ i : Fin N,sampledMatrix 1 i j*v i/(N:ℝ)= a i*sampledMatrix 1 i j by
      intro;dsimp [a];ring] at hh
    dsimp [b] at hh;linarith
  exact ⟨a,fit,kernel_solve hn z a fit⟩

end CircleFirstCosineReference
