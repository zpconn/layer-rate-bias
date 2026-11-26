module
public import CircleDiscreteBudget
public import CircleReciprocal
import all CircleDiscreteBudget
import all CircleKernelGD
import all CircleGridSpectrum
import all CircleSpectrum
import all CircleSpectralPathLength
import all CircleKernelIdentification
import all CircleCapInduction
import all CircleCapMoments
import all CircleReciprocal
import all CircleDiscreteTracking
import all CircleEscape
import all CircleEscapeBridge
import all CircleFlowPath
import all CircleTangentDrift
import Mathlib.Tactic

/-! Deterministic spectral estimates for the true initial reciprocal
curvature, with the actual strict ReLU gates. -/
public section
noncomputable section
namespace CircleReciprocalSpectral
open CircleFlowPath CircleTangentDrift CircleGridSpectrum CircleSpectrum CircleKernelGD
  CircleSpectralPathLength CircleCapInduction CircleEscapeBridge CircleKernelIdentification
  Real Finset
open scoped ComplexConjugate
variable {N m : ℕ} [NeZero N]

private theorem mass : ∑' k, tangentCoeff 1 k=1 := by
  have h := sampled_tangent_eq_series (N:=3) 1 (by norm_num) (by norm_num) 0
  have grid : gridAngle (0:ZMod 3)=((0:ℝ):AddCircle (π- -π)) := by simp [gridAngle]
  have h0 := periodicTangent_cartesian 1 0 0
  simp only [sub_zero,cartesian_kernel_isotropic,abs_zero,angular_tangent 1 0 (by norm_num) pi_pos.le,
    sin_zero,cos_zero] at h0
  have hf : (periodicTangent 1 ((0:ℝ):AddCircle (π- -π))).re=1 := h0.trans (by field_simp;ring)
  simpa only [grid,series,char,mul_zero,AddChar.map_zero_eq_one,mul_one,←Complex.ofReal_tsum,Complex.ofReal_re,hf]
    using (congrArg Complex.re h).symm

omit [NeZero N] in
/-- At least one of the two distinct residues ±1 is absent from any
single alias sum. Each of those coefficients contributes exactly 1/4. -/
theorem eigen_upper (hn : 3≤N) (r : ZMod N) : eigen 1 r≤3/4 := by
  have neq : (1:ZMod N)≠ -1 := by
    intro eq
    have h : ((2:ℤ):ZMod N)=0 := by
      push_cast; change (2:ZMod N)=0
      calc 2=(1:ZMod N)+1 := by ring
           _= -1+1 := congrArg (·+1) eq
           _=0 := neg_add_cancel _ 
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 N).1 h
    have hdn : N∣2 := by exact_mod_cast hd
    exact (not_le_of_gt (show 2<N by omega)) (Nat.le_of_dvd (by decide) hdn)
  obtain ⟨k,hk,hv⟩ : ∃ k : ℤ, (k:ZMod N)≠r ∧ tangentCoeff 1 k=1/4 := by
    by_cases h : (1:ZMod N)=r
    · refine ⟨-1,?_,by norm_num [tangentCoeff]⟩
      simpa [←h] using neq.symm
    · exact ⟨1,by simpa using h,by norm_num [tangentCoeff]⟩
  let a := tangentCoeff 1
  let f (j : ℤ) := if (j:ZMod N)=r then a j else 0
  have ha := tangentCoeff_summable 1 (by norm_num) (by norm_num)
  have hf : Summable f := (ha.indicator {k : ℤ | (k:ZMod N)=r}).congr (fun j => by simp [f,a,Set.indicator_apply])
  have nn (j : ℤ) : 0≤a j-f j := by dsimp [f];split <;> simp [a,tangentCoeff_nonneg (by norm_num : (0:ℝ)≤1)]
  have hs := (ha.sub hf).le_tsum k (fun j _ => nn j)
  rw [ha.tsum_sub hf,mass] at hs
  change ∑' j, f j ≤ 3/4
  change a k-f k ≤ _ at hs
  simp only [f,hk,ite_false,sub_zero,a,hv] at hs
  linarith

private theorem gram_upper (hn : 3≤N) (v : EuclideanSpace ℝ (Fin N)) :
    inner ℝ v (gram N v)≤(3/4)*‖v‖^2 := by
  let K (i : ZMod N) := periodicTangent 1 (gridAngle i)
  have neg_conv (f : ZMod N→ℂ) (i : ZMod N) : convolution (fun j => -K j) f i= -convolution K f i := by
    simp only [convolution,neg_mul,Finset.sum_neg_distrib,neg_div]
  have hh (r i : ZMod N) : convolution (fun j=> -K j) (char r) i= ((-eigen 1 r:ℝ):ℂ)*char r i := by
    rw [neg_conv];dsimp only [K,eigen];rw [sampled_character_eigenvalue 1 (by norm_num) (by norm_num)]
    push_cast;ring
  let f (i : ZMod N) : ℝ := v ((ZMod.finEquiv N).symm i)
  have H := rayleigh_of_character_gap _ (fun i => (f i:ℂ)) _ (-(3/4:ℝ)) hh (fun r => neg_le_neg (eigen_upper hn r))
  simp only [neg_conv,mul_neg,Finset.sum_neg_distrib,Complex.neg_re,neg_mul,neg_le_neg_iff] at H
  simp only [convolution,Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.re_sum,Complex.conj_ofReal,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Complex.div_natCast_re] at H
  have hf (i : Fin N) : f (ZMod.finEquiv N i)=v i := by simp [f]
  rw [←CircleGridSpectrum.fin_sum,←CircleGridSpectrum.fin_sum] at H
  simp only [hf] at H
  rw [EuclideanSpace.real_norm_sq_eq,PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply,star_trivial]
  refine LE.le.trans_eq' H ?_
  apply sum_congr rfl
  intro i _
  rw [mul_comm,gram,gramOp_apply,←CircleGridSpectrum.fin_sum]
  simp [K,sampledMatrix,hf]

private def initialGram (z : Seed m) := gramOp (gridGram 1 z (startGates (N:=N) z))

omit [NeZero N] in
private theorem entry_eq (hm : 0<m) (z : Seed m) (i k : Fin N) :
    gridGram 1 z (startGates z) i k =
      (∑ j, (CircleEscape.feature ((initial z).w j) (CircleEscape.gridPoint N i)*
          CircleEscape.feature ((initial z).w j) (CircleEscape.gridPoint N k)+
        ((initial z).a j)^2*CircleEscape.gate ((initial z).w j) (CircleEscape.gridPoint N i)*
          CircleEscape.gate ((initial z).w j) (CircleEscape.gridPoint N k)*
          inner ℝ (CircleEscape.gridPoint N i) (CircleEscape.gridPoint N k)))/m := by
  rw [gridGram,entry_sum hm]
  congr 1
  apply sum_congr rfl
  intro j _
  simp only [CircleEscape.feature,CircleEscape.gate,CircleDiscreteTracking.pre_complex]
  simp only [
    CircleTangentDrift.atom,startGates,actualGate,circleInput,dot,initial,Complex.inner,Complex.mul_re,
    Complex.conj_re,Complex.conj_im]
  let P (i : Fin N) := 0<pre z j ((CircleEscape.gridPoint N i).re,(CircleEscape.gridPoint N i).im)
  by_cases hi : P i <;> by_cases hk : P k <;> dsimp only [P] at hi hk <;> simp only [hi,hk,ite_false,ite_true] <;> ring

omit [NeZero N] in
private theorem quadratic (hm : 0<m) (z : Seed m) (v : EuclideanSpace ℝ (Fin N)) :
    inner ℝ v (initialGram (N:=N) z v) = jacSq (CircleEscape.gridPoint N) (initial z) (fun i=>v i)/((N:ℝ)*m) := by
  let x := CircleEscape.gridPoint N
  let w := initial z
  let f (i : Fin N) (j : Fin m) := CircleEscape.feature (w.w j) (x i)
  let g (i : Fin N) (j : Fin m) := CircleEscape.gate (w.w j) (x i)
  let a (j : Fin m) (i k : Fin N) := f i j*f k j+(w.a j)^2*g i j*g k j*inner ℝ (x i) (x k)
  have je (j : Fin m) : (∑ i, v i*f i j)^2+(w.a j)^2*‖∑ i, (v i*g i j) • x i‖^2=
      ∑ i, ∑ k, v i*(v k*a j i k) := by
    rw [←real_inner_self_eq_norm_sq]
    simp only [sq,Finset.mul_sum,Finset.sum_mul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
    rw [←Finset.sum_add_distrib]
    apply sum_congr rfl; intro i _
    rw [←Finset.sum_add_distrib]
    apply sum_congr rfl; intro k _
    dsimp only [a];rw [real_inner_comm (x k) (x i)];ring
  have S : (∑ j, ∑ i, ∑ k, v i*(v k*a j i k))=∑ i, ∑ k, v i*(v k*∑ j, a j i k) := by
    rw [sum_comm]
    simp_rw [mul_sum]
    apply sum_congr rfl;intro i _;rw [sum_comm]
  have J : jacSq x w (fun i=>v i)=∑ i, ∑ k, v i*(v k*∑ j, a j i k) := by
    change (∑ j, ((∑ i, v i*f i j)^2+(w.a j)^2*‖∑ i,(v i*g i j) •x i‖^2))=_
    simp_rw [je];exact S
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial,initialGram,gramOp_apply,entry_eq hm]
  change _=jacSq x w (fun i=>v i)/_
  rw [J]
  change (∑ i, ((∑ k, ((∑ j, a j i k)/m)*v k)/N)*v i)=_
  simp only [div_mul_eq_mul_div,←Finset.sum_div,div_div]
  congr 1
  · apply sum_congr rfl; intro i _
    rw [sum_mul]; apply sum_congr rfl; intro k _;ring
  · ring


private theorem gramBound_iff (hm : 0<m) (z : Seed m) (L : ℝ) :
    GramBound (CircleEscape.gridPoint N) (initial z) L ↔ ∀ v : EuclideanSpace ℝ (Fin N),
      inner ℝ v (initialGram (N:=N) z v)≤L*‖v‖^2 := by
  have hd : 0<(N:ℝ)*m := mul_pos (Nat.cast_pos.mpr (NeZero.pos N)) (Nat.cast_pos.mpr hm)
  constructor
  · intro H v
    rw [quadratic hm,EuclideanSpace.real_norm_sq_eq,div_le_iff₀ hd]
    exact (H (fun i=>v i)).trans_eq (by ring)
  · intro H r
    let v : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 r
    have h := H v
    rw [quadratic hm,EuclideanSpace.real_norm_sq_eq,div_le_iff₀ hd] at h
    exact h.trans_eq (by ring)

private theorem inner_close (z : Seed m) {ρ u : ℝ} {kQ : Fin N→ℝ} (hu : 0≤u)
    (G : GoodInit 1 ρ u (sampledMatrix 1) kQ z) (v : EuclideanSpace ℝ (Fin N)) :
    |inner ℝ v (initialGram (N:=N) z v)-inner ℝ v (gram N v)|≤2*u*‖v‖^2 := by
  let B := initialGram (N:=N) z-gram N
  have hb : ‖B‖≤2*u := by
    dsimp only [B,initialGram,gram]
    rw [←gramOp_sub]
    exact gramOp_norm (NeZero.pos N) (by positivity) G.gram
  change |inner ℝ v (initialGram z v)-inner ℝ v (gram N v)| ≤ _
  rw [←inner_sub_right]
  exact (abs_real_inner_le_norm v (B v)).trans ((mul_le_mul_of_nonneg_left
    ((B.le_opNorm v).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg v))) (norm_nonneg _)).trans_eq (by ring))

private theorem gamma_rayleigh : ∃ v : EuclideanSpace ℝ (Fin N), 0<‖v‖^2 ∧
    inner ℝ v (gram N v)=gamma N*‖v‖^2 := by
  let v : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun _ : Fin N => (1:ℝ))
  have eqv (i : Fin N) : v i=1 := rfl
  have hsym (i j : Fin N) : sampledMatrix 1 i j=sampledMatrix 1 j i := by
    simp [sampledMatrix_cartesian,cartesian_kernel_isotropic,abs_sub_comm]
  have hg (i : Fin N) : gram N v i=gamma N := by
    rw [gram,gramOp_apply]
    simpa only [gamma,eqv,mul_one,hsym i] using sampled_column 1 (by norm_num) (by norm_num) i
  have hnorm : ‖v‖^2=(N:ℝ) := by simp only [EuclideanSpace.real_norm_sq_eq,eqv,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  refine ⟨v,hnorm ▸ Nat.cast_pos.mpr (NeZero.pos _),?_⟩
  rw [hnorm,PiLp.inner_apply]
  simp [RCLike.inner_apply,eqv,hg,mul_comm]

omit [NeZero N] in
private theorem quadratic_op_norm {T : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)}
    (hs : T.toLinearMap.IsSymmetric) {c : ℝ} (hc : 0≤c)
    (h : ∀ v, |inner ℝ v (T v)|≤c*‖v‖^2) : ‖T‖≤c := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hs]
  apply ciSup_le; intro v
  by_cases hv : v=0
  · simpa [hv,ContinuousLinearMap.rayleighQuotient] using hc
  · show |T.reApplyInnerSelf v / ‖v‖^2| ≤ c
    rw [abs_div,abs_of_nonneg (sq_nonneg ‖v‖),div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv))]
    change |inner ℝ (T v) v|≤_
    rw [real_inner_comm];exact h v

theorem population_norm (hn : 3≤N) (odd : Odd N) : ‖gram N‖≤3/4 := by
  apply quadratic_op_norm CircleKernelGD.gram_symmetric (by norm_num)
  intro v
  have h := gramOp_gap hn odd 1 (by norm_num) (by norm_num) v
  have nn : 0 ≤ inner ℝ v (gram N v) := (mul_nonneg (by positivity) (sq_nonneg _)).trans h
  rw [abs_of_nonneg nn];exact gram_upper hn v

def propagator (N : ℕ) [NeZero N] (η : ℝ) :=
  (1 : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))-η • gram N

/-- The top sampled operator and the empirical initial curvature differ
by at most twice the entry tolerance. -/
theorem close_curvature (hn : 3≤N) (odd : Odd N) (hm : 0<m) (z : Seed m)
    {ρ u : ℝ} {kQ : Fin N→ℝ} (hu : 0≤u) (G : GoodInit 1 ρ u (sampledMatrix 1) kQ z) :
    let L := curvature (CircleEscape.gridPoint N) (initial z)
    gamma N-2*u≤L ∧ L≤3/4+2*u ∧ ‖gram N‖≤L+2*u := by
  intro L
  have top : IsTopGram (CircleEscape.gridPoint N) (initial z) L :=
    (CircleCapMoments.initial_top N m hn odd hm _).1
  have qa := (gramBound_iff hm z L).mp top.1
  obtain ⟨w,wp,we⟩ := gamma_rayleigh (N:=N)
  have wl := (abs_le.mp (inner_close z hu G w)).1
  rw [we] at wl
  have lower : gamma N-2*u≤L := le_of_mul_le_mul_right (a:=‖w‖^2) (by linarith only [wl,qa w]) wp
  have upper : L≤3/4+2*u := by
    apply top.2
    apply (gramBound_iff hm z _).mpr;intro v
    linarith only [(abs_le.mp (inner_close z hu G v)).2,gram_upper hn v]
  refine ⟨lower,upper,?_⟩
  have g0 := (gamma_bounds (N:=N)).1
  apply quadratic_op_norm CircleKernelGD.gram_symmetric (by linarith [show (0:ℝ)≤3/π^2 by positivity])
  intro v
  have hj := gramOp_gap hn odd 1 (by norm_num) (by norm_num) v
  have nn : 0 ≤ inner ℝ v (gram N v) := (mul_nonneg (by positivity) (sq_nonneg _)).trans hj
  rw [abs_of_nonneg nn]
  linarith only [(abs_le.mp (inner_close z hu G v)).1,qa v]

/-- With the exact rate 1/L, the population propagator is nonexpansive,
and its constant component decays at least as fast as exp(-γ) per update.
The threshold on u holds on the original width/circle design. -/
theorem good_rate (hn : 3≤N) (odd : Odd N) (hm : 0<m) (z : Seed m)
    {ρ u : ℝ} {kQ : Fin N→ℝ} (hu : 0≤u) (small : u≤1/100) (G : GoodInit 1 ρ u (sampledMatrix 1) kQ z) :
    let η := CircleReciprocal.rate N m 1 z
    1≤η ∧ η≤4 ∧ η*‖gram N‖≤1+8*u ∧ ‖propagator N η‖≤1 ∧ |1-η*gamma N|≤exp (-(gamma N)) := by
  intro η
  let L := curvature (CircleEscape.gridPoint N) (initial z)
  have cc := close_curvature hn odd hm z hu G
  change gamma N-2*u≤L ∧ L≤3/4+2*u ∧ ‖gram N‖≤L+2*u at cc
  have gl := (gamma_bounds (N:=N)).1
  have gl' : (27:ℝ)/100 < 3/π^2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos pi_pos)).mpr
    nlinarith [sq_nonneg (π-3.15),Real.pi_lt_d2,Real.pi_pos]
  have lp : 1/4≤L := by linarith [cc.1]
  have lp' : 0<L := by linarith
  have eu : η≤4 := by change 1/L≤4;rw [div_le_iff₀ lp'];linarith
  have el : 1≤η := by change 1≤1/L;rw [le_div_iff₀ lp'];linarith [cc.2.1]
  have ep : 0≤η := by linarith
  have unit : η*L=1 := by change (1/L)*L=1;field_simp
  have es : η*‖gram N‖≤1+8*u := by
    have h := mul_le_mul_of_nonneg_left cc.2.2 ep
    have h' := mul_le_mul_of_nonneg_right eu hu
    nlinarith only [unit,h,h']
  have gc : gamma N ≤ ‖gram N‖ := by
    obtain ⟨v,vp,eq⟩ := gamma_rayleigh (N:=N)
    have h := (real_inner_le_norm v (gram N v)).trans (mul_le_mul_of_nonneg_left ((gram N).le_opNorm v) (norm_nonneg _))
    rw [eq] at h
    exact le_of_mul_le_mul_right (a:=‖v‖^2) (h.trans_eq (by ring)) vp
  have gsmall := gc.trans (population_norm hn odd)
  refine ⟨el,eu,es,?_,?_⟩
  · have hs : (propagator N η).toLinearMap.IsSymmetric := LinearMap.IsSymmetric.id.sub (LinearMap.IsSymmetric.smul (by simp) CircleKernelGD.gram_symmetric)
    apply quadratic_op_norm hs zero_le_one
    intro v
    have hg := gramOp_gap hn odd 1 (by norm_num) (by norm_num) v
    have nn : 0 ≤ inner ℝ v (gram N v) := (mul_nonneg (by positivity) (sq_nonneg _)).trans hg
    have hu' := (real_inner_le_norm v (gram N v)).trans (mul_le_mul_of_nonneg_left ((gram N).le_opNorm v) (norm_nonneg _))
    have hB : η*inner ℝ v (gram N v)≤2*‖v‖^2 := by
      have h := mul_le_mul_of_nonneg_left hu' ep
      have h' := mul_le_mul_of_nonneg_right (show η*‖gram N‖≤2 by linarith) (sq_nonneg ‖v‖)
      nlinarith only [h,h']
    change |inner ℝ v (v-η • gram N v)| ≤ _
    rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,one_mul]
    exact abs_le.mpr ⟨by linarith,by linarith only [mul_nonneg ep nn]⟩
  · have eg := mul_le_mul_of_nonneg_left gc ep
    have g0 : 0≤gamma N := (by positivity : 0≤3/π^2).trans gl
    have h1 := mul_le_mul_of_nonneg_right el g0
    have he := Real.add_one_le_exp (-(gamma N))
    exact abs_le.mpr ⟨by linarith,by linarith⟩


theorem curvature_norm_distance (hn : 3≤N) (odd : Odd N) (hm : 0<m) (z : Seed m)
    {ρ u : ℝ} {kQ : Fin N→ℝ} (hu : 0≤u) (G : GoodInit 1 ρ u (sampledMatrix 1) kQ z) :
    |curvature (CircleEscape.gridPoint N) (initial z)-‖gram N‖|≤2*u := by
  have h := close_curvature hn odd hm z hu G
  have top := (CircleCapMoments.initial_top N m hn odd hm (initial z)).1
  have cap : curvature (CircleEscape.gridPoint N) (initial z)≤‖gram N‖+2*u := by
    apply top.2
    apply (gramBound_iff hm z _).mpr
    intro v
    have u1 := (real_inner_le_norm v (gram N v)).trans
      (mul_le_mul_of_nonneg_left ((gram N).le_opNorm v) (norm_nonneg _))
    nlinarith only [u1,(abs_le.mp (inner_close z hu G v)).2]
  exact abs_le.mpr ⟨by linarith only [h.2.2],by linarith only [cap]⟩

theorem contract {η : ℝ} (h : ‖propagator N η‖≤1) (v : EuclideanSpace ℝ (Fin N)) :
    ‖v-η • gram N v‖≤‖v‖ := ((propagator N η).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_right h (norm_nonneg v)).trans_eq (one_mul _))

/-- The signed constant-mode transient is at most N⁻³ in absolute value
at S on the same reciprocal event. -/
theorem short_decay {η : ℝ} (h : |1-η*gamma N|≤exp (-(gamma N))) :
    |(1-η*gamma N)^(short N)|≤1/(N:ℝ)^3 := by
  rw [abs_pow]
  have h3 : (3:ℝ)*log N ≤ gamma N*short N := by
    have hl := Nat.le_ceil (π^2*log N)
    change π^2*log N≤(short N:ℝ) at hl
    calc
      (3:ℝ)*log N = (3/π^2)*(π^2*log N) := by field_simp
      _ ≤ _ := (mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ)≤3/π^2)).trans
        (mul_le_mul_of_nonneg_right gamma_bounds.1 (Nat.cast_nonneg _))
  apply (pow_le_pow_left₀ (abs_nonneg _) h (short N)).trans
  rw [←exp_nat_mul,show (short N:ℝ)* -(gamma N) = -(gamma N*short N) by ring]
  apply (exp_le_exp.mpr (neg_le_neg h3)).trans_eq
  rw [exp_neg,show 3*log (N:ℝ)=log ((N:ℝ)^3) by simp,
    exp_log (pow_pos (Nat.cast_pos.mpr (NeZero.pos N)) _),one_div]

end CircleReciprocalSpectral
