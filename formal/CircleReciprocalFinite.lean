module

public import CircleReciprocal
public import CircleConditioning
import all CircleInitializationCheck
import all CircleReciprocal
import all CircleSeedIntegrability
import all CircleEscapeBridge
import all CircleEscape
import all CircleCapInduction
import all CircleCapMoments
import all CircleGridMargin
import all CircleFlowMoments
import all CircleConditioning
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Inverse powers of the actual Gaussian initialization radius and their
use in the finite-moment direction of the uncapped reciprocal-step theorem. -/
public section
noncomputable section
namespace CircleReciprocalFinite
open MeasureTheory ProbabilityTheory Real Set CircleEscape CircleEscapeBridge CircleSeedIntegrability
  CircleCapInduction CircleCapMoments

def length {m : ℕ} (ω : Seed m) := sqrt (∑ i, (ω i)^2)

private theorem length_nn {m : ℕ} (ω : Seed m) : 0≤length ω := sqrt_nonneg _
private theorem coordinate_le {m : ℕ} (ω : Seed m) (i : Fin m × Fin 3) : |ω i| ≤ length ω := by
  apply le_sqrt_of_sq_le
  rw [sq_abs]; exact Finset.single_le_sum (fun j _ => sq_nonneg (ω j)) (Finset.mem_univ i)

private theorem measurable_length (m : ℕ) : Measurable (length (m:=m)) := by unfold length; fun_prop

private theorem gaussian_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  apply le_trans _ (withDensity_one (μ:=(volume : Measure ℝ))).le
  apply withDensity_mono
  filter_upwards with x
  change ENNReal.ofReal (gaussianPDFReal 0 1 x)≤1
  apply (ENNReal.ofReal_le_one).2
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  have rt : 1 ≤ sqrt (2*π) := one_le_sqrt.mpr (by linarith [pi_gt_three])
  have r := inv_le_one_of_one_le₀ rt
  exact (mul_le_mul_of_nonneg_left (exp_le_one_iff.mpr (by nlinarith [sq_nonneg x] : -(x^2)/2≤0)) (by positivity)).trans (by simpa using r)

private theorem scalar_inverse {u : ℝ} (hu : 0≤u) (h1 : u<1) :
    Integrable (fun x : ℝ => |x|^(-u)) (gaussianReal 0 1) := by
  let A := Metric.ball (0:ℝ) 1
  have localInt : IntegrableOn (fun x : ℝ => |x|^(-u)) A volume := by
    apply integrableOn_ball_of_norm_le_rpow (by simp) (C:=1) (α:=u) (by simpa using h1) _ (continuous_abs.measurable.pow_const (-u)).aestronglyMeasurable
    exact ae_of_all _ fun x => by simp only [Real.norm_eq_abs,abs_of_nonneg (rpow_nonneg (abs_nonneg _) _),one_mul]; rfl
  have outside : IntegrableOn (fun x : ℝ => |x| ^ (-u)) Aᶜ (gaussianReal 0 1) := by
    apply (integrable_const (μ:=(gaussianReal 0 1).restrict Aᶜ) (1:ℝ)).mono' (continuous_abs.measurable.pow_const (-u)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=gaussianReal 0 1) Metric.isOpen_ball.measurableSet.compl] with x hx
    change x ∉ Metric.ball (0:ℝ) 1 at hx
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,not_lt] at hx
    rw [Real.norm_of_nonneg (rpow_nonneg (abs_nonneg _) _)]
    exact rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr hu)
  exact integrableOn_univ.mp (by simpa using ((localInt.mono_measure gaussian_le_volume).union outside))

private theorem nz_coords (m : ℕ) : ∀ᵐ z ∂seedLaw m, ∀ i, z i≠0 := by
  rw [ae_all_iff]
  intro i
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  exact Measure.ae_eval_ne (μ := fun _ : Fin m × Fin 3 => gaussianReal 0 1) i 0

theorem inverse_radius_integrable {m : ℕ} (hm : 0<m) {p : ℝ} (hp : 0≤p) (small : p<3*(m:ℝ)) :
    Integrable (fun z : Seed m => length z ^ (-p)) (seedLaw m) := by
  let D := 3*(m:ℝ)
  have dp : 0<D := by dsimp [D]; positivity
  let u := p/D
  have up : 0≤u := div_nonneg hp dp.le
  have ut : u<1 := (div_lt_one dp).mpr small
  let f := fun (_ : Fin m × Fin 3) (x : ℝ) => |x|^(-u)
  have prod : Integrable (fun z : Seed m => ∏ i, f i (z i)) (seedLaw m) := Integrable.fintype_prod fun _ => scalar_inverse up ut
  apply prod.mono' ((measurable_length m).pow_const (-p)).aestronglyMeasurable
  filter_upwards [nz_coords m] with z hz
  have hcard : (Fintype.card (Fin m × Fin 3):ℝ)=D := by simp [D,Fintype.card_prod,mul_comm]
  have lp : 0<length z := (abs_pos.mpr (hz (⟨0,hm⟩,0))).trans_le (coordinate_le z _)
  rw [Real.norm_of_nonneg (rpow_nonneg lp.le _)]
  calc
    _ = ∏ _i : Fin m × Fin 3, length z ^ (-u) := by
      rw [Finset.prod_const,Finset.card_univ,←Real.rpow_natCast,←Real.rpow_mul lp.le,hcard]
      congr 1; dsimp [u]; field_simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => rpow_nonneg lp.le _)
      (fun i _ => Real.rpow_le_rpow_of_nonpos (abs_pos.mpr (hz i)) (coordinate_le z i) (neg_nonpos.mpr up))


/-- A seed-independent constant bounds the frozen step multiplied by the
squared Gaussian radius. -/
theorem rate_radius (N m : ℕ) (hN : 3≤N) (odd : Odd N) (hm : 0<m) (c : ℝ) (hc : 0<c)
    (ω : Seed m) (rp : 0<length ω) (nz : ∀ j, (initial ω).w j≠0) :
    |CircleReciprocal.rate N m c ω/(N*sqrt m)| *N*(length ω)^2 ≤ 16*m*c/sqrt m := by
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  let L := curvature (gridPoint N) (initial ω)
  have low := gram_lower (gridPoint N) (initial ω) (by omega) hm (1/4) L (by norm_num) nz
    (fun w => (by ring : (N:ℝ)*(1/4)*‖w‖=(N:ℝ)*‖w‖/4) ▸ (CircleGridMargin.grid_relu_sum_bounds N hN w).1)
    (initial_top N m hN odd hm (initial ω)).1.1
  have rs : (length ω)^2=rawEnergy (initial ω) := by
    rw [initial_energy_coordinates];exact sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  rw [energy,←rs] at low
  have ll : (length ω)^2≤16*(m:ℝ)*L := by
    have h := (div_le_iff₀ mp).mp <| show (1/4:ℝ)^2*(length ω)^2/m≤L by
      simpa only [mul_div_assoc] using low
    linarith
  have lp : 0<L := by
    by_contra! hn
    have : 16*(m:ℝ)*L≤0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hn
    linarith [sq_pos_of_pos rp]
  change |c/L/(N*sqrt m)| *N*(length ω)^2 ≤ _
  rw [abs_of_pos (by positivity)]
  calc _ = c*(length ω)^2/(L*sqrt m) := by field_simp
       _ ≤ _ := by
         apply (div_le_iff₀ (by positivity)).mpr
         calc c*(length ω)^2 ≤ c*(16*m*L) := mul_le_mul_of_nonneg_left ll hc.le
              _ = _ := by field_simp

private theorem init_small {m : ℕ} (ω : Seed m) : Bounded (initial ω) (2*length ω) := by
  intro j
  constructor
  · exact (coordinate_le ω (j,0)).trans (by linarith [length_nn ω])
  · exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
      change |ω (j,1)|+|ω (j,2)|≤_;linarith [coordinate_le ω (j,1),coordinate_le ω (j,2)])

private theorem bound_mono {m : ℕ} {u : Net ℂ m} {B D : ℝ} (bnd : Bounded u B) (le : B≤D) :
    Bounded u D := fun j => ⟨(bnd j).1.trans le,(bnd j).2.trans le⟩

private theorem step_bound {N m : ℕ} (g k B : ℝ) (u : Net ℂ m) (hb : 0≤B) (bound : Bounded u B) :
    Bounded (step (gridPoint N) (fun i => 1+(gridPoint N i).re) g k u)
      (B+(|k| *N)*((|g| *m)*B^2+2)*B) := by
  let r := fun i => output g u (gridPoint N i)-(1+(gridPoint N i).re)
  let A := (|g| *m)*B^2+2
  have A₀ : 0≤A := by dsimp [A];positivity
  have hr (i : Fin N) : |r i|≤A := by
    have hy := Complex.abs_re_le_norm (gridPoint N i)
    rw [grid_norm] at hy
    have ty : |1+(gridPoint N i).re|≤2 := (abs_add_le _ _).trans (by rw [abs_one];linarith)
    exact (abs_sub _ _).trans (add_le_add (output_cap g B hb u bound _ (grid_norm N i).le) ty)
  intro j
  have a := sum_norm_cap (fun i => r i*feature (u.w j) (gridPoint N i)) (A*B) (by
    intro i;rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hr i) ((feature_cap _ _ (grid_norm N i).le).trans (bound j).2) (abs_nonneg _) A₀)
  have w := sum_norm_cap (fun i => (r i*gate (u.w j) (gridPoint N i)) • gridPoint N i) A (by
    intro i;rw [norm_smul,Real.norm_eq_abs,abs_mul,grid_norm,mul_one]
    have ga : |gate (u.w j) (gridPoint N i)|≤1 := by unfold gate; split <;> norm_num
    simpa only [mul_one] using mul_le_mul (hr i) ga (abs_nonneg _) A₀)
  simp only [Fintype.card_fin,Real.norm_eq_abs] at a w
  constructor
  · apply (abs_sub _ _).trans
    rw [abs_mul]
    exact (add_le_add (bound j).1 (mul_le_mul_of_nonneg_left a (abs_nonneg k))).trans_eq (by dsimp [A];ring)
  · apply (norm_sub_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_mul]
    exact (add_le_add (bound j).2 (mul_le_mul (mul_le_mul_of_nonneg_left (bound j).1 (abs_nonneg k))
      w (norm_nonneg _) (by positivity))).trans_eq (by dsimp [A];ring)

private theorem step_rescale {N m : ℕ} {r V K g k X : ℝ} (rp : 0<r) (v : 1/r≤V)
    (kn : |k| *N*r^2≤K) (x₀ : 0≤X) {u : Net ℂ m} (bound : Bounded u (r*X)) :
    Bounded (step (gridPoint N) (fun i => 1+(gridPoint N i).re) g k u)
      (r*(X*(1+K*((|g| *m)*X^2+2*V^2)))) := by
  have kk : 0≤|k| *N := by positivity
  have vp : 0≤V := (by positivity : 0≤1/r).trans v
  have rv : 1≤r*V := (div_le_iff₀ rp).mp v |>.trans_eq (mul_comm _ _)
  have small : 1≤r^2*V^2 := by simpa only [mul_pow] using (one_le_pow₀ rv (n:=2))
  have h := mul_le_mul_of_nonneg_left small (show 0≤2*(|k| *N) by positivity)
  have z : |k| *N*((|g| *m)*(r*X)^2+2) ≤ K*((|g| *m)*X^2+2*V^2) := calc
    _ ≤ (|k| *N*r^2)*((|g| *m)*X^2+2*V^2) := by nlinarith only [h]
    _ ≤ _ := mul_le_mul_of_nonneg_right kn (by positivity)
  apply bound_mono (step_bound g k _ u (mul_nonneg rp.le x₀) bound)
  linarith only [mul_le_mul_of_nonneg_right z (mul_nonneg rp.le x₀)]



theorem parameter_envelope (N m s : ℕ) (hN : 3≤N) (odd : Odd N) (hm : 0<m) (c : ℝ) (hc : 0<c) :
    ∃ D : ℝ, 0≤D ∧ ∀ ω : Seed m, 0<length ω → (∀ j, (initial ω).w j≠0) →
      ∀ j, let u := path N m (CircleReciprocal.rate N m c ω) ω (s+1)
           let B := length ω*(D*(max 1 (1/length ω))^(2*3^s))
           |u.a j|≤B ∧ ‖u.w j‖≤B := by
  let K := 16*m*c/sqrt m
  let g := 1/sqrt (m:ℝ)
  let M := |g| *m
  have K₀ : 0≤K := by dsimp [K];positivity
  have M₀ : 0≤M := by dsimp [M];positivity
  induction s with
  | zero =>
    let D := 2*(1+K*(M*4+2))
    have D₀ : 0≤D := by dsimp [D];positivity
    refine ⟨D,D₀,?_⟩
    intro ω rp nz
    let r := length ω
    let V := max 1 (1/r)
    have v : 1≤V := le_max_left _ _
    have v2 : 1≤V^2 := one_le_pow₀ v
    have b₀ := init_small ω
    have start : Bounded (initial ω) (r*2) := bound_mono b₀ (le_of_eq (mul_comm _ _))
    have bs := step_rescale (g:=g) rp (le_max_right 1 _) (rate_radius N m hN odd hm c hc ω rp nz) (by norm_num : (0:ℝ)≤2) start
    apply bound_mono bs
    change r*(2*(1+K*(M*2^2+2*V^2))) ≤ r*(D*V^(2*3^0))
    apply mul_le_mul_of_nonneg_left _ rp.le
    dsimp [D];norm_num
    nlinarith only [mul_le_mul_of_nonneg_left v2 (show 0≤2+8*K*M by positivity)]
  | succ s ih =>
    obtain ⟨D,D₀,prev⟩ := ih
    let A := D*(1+K*(M*D^2+2))
    have A₀ : 0≤A := by dsimp [A];positivity
    refine ⟨A,A₀,?_⟩
    intro ω rp nz
    let r := length ω
    let V := max 1 (1/r)
    let W := V^(2*3^s)
    have v : 1≤V := le_max_left _ _
    have W₁ : 1≤W := one_le_pow₀ v
    have VW : V≤W := le_self_pow₀ v (by positivity)
    have v₂ : V^2≤W^2 := pow_le_pow_left₀ (zero_le_one.trans v) VW 2
    have ws : 1≤W^2 := one_le_pow₀ W₁
    have bs := step_rescale (g:=g) rp (le_max_right 1 _) (rate_radius N m hN odd hm c hc ω rp nz)
      (mul_nonneg D₀ (zero_le_one.trans W₁)) (prev ω rp nz)
    apply bound_mono bs
    change r*(D*W*(1+K*(M*(D*W)^2+2*V^2))) ≤ r*(A*V^(2*3^(s+1)))
    rw [show 2*3^(s+1)=2*3^s*3 by rw [pow_succ,mul_assoc],pow_mul]
    apply mul_le_mul_of_nonneg_left _ rp.le
    change D*W*(1+K*(M*(D*W)^2+2*V^2)) ≤ A*W^3
    calc _ ≤ D*W*(1+K*(M*(D*W)^2+2*W^2)) := by gcongr
         _ ≤ _ := by
           dsimp [A]
           nlinarith only [mul_le_mul_of_nonneg_left ws (mul_nonneg D₀ (zero_le_one.trans W₁))]

theorem output_envelope (N m s : ℕ) (hN : 3≤N) (odd : Odd N) (hm : 0<m) (c : ℝ) (hc : 0<c) :
    ∃ D : ℝ, 0≤D ∧ ∀ ω : Seed m, 0<length ω → (∀ j, (initial ω).w j≠0) →
      |CircleReciprocal.Y N m (s+1) c ω| ≤ D*(length ω)^2*(max 1 (1/length ω))^(4*3^s) := by
  obtain ⟨A,A₀,par⟩ := parameter_envelope N m s hN odd hm c hc
  let g := 1/sqrt (m:ℝ)
  refine ⟨(|g/π| *m)*A^2,by positivity,?_⟩
  intro ω rp nz
  let V := max 1 (1/length ω)
  have vp : 0≤V := zero_le_one.trans (le_max_left _ _)
  have b := mean_cap g _ (mul_nonneg rp.le (mul_nonneg A₀ (pow_nonneg vp _))) _ (par ω rp nz)
  apply b.trans_eq
  change (|g/π| *m)*(length ω*(A*V^(2*3^s)))^2 = (|g/π| *m)*A^2*(length ω)^2*V^(4*3^s)
  rw [show 4*3^s=(2*3^s)*2 by ring,pow_mul];ring



private theorem length_le_radius {m : ℕ} (ω : Seed m) : length ω ≤ radius ω := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ) (fun i _ => abs_nonneg (ω i))
  simp only [sq_abs] at h
  have nn := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => abs_nonneg (ω i))
  apply (sqrt_le_iff).mpr
  constructor
  · exact zero_le_one.trans (radius_one ω)
  · dsimp [radius];nlinarith

private theorem small_output_power (r D p : ℝ) (e : ℕ) (rp : 0<r) (D₀ : 0≤D) :
    (D*r^2*(1/r)^e)^p = D^p*r^(-(((e:ℝ)-2)*p)) := by
  have eq : D*r^2*(1/r)^e=D*r^((2:ℝ)-(e:ℝ)) := by
    rw [rpow_sub rp,Real.rpow_natCast,rpow_two,div_pow,one_pow];ring
  rw [eq,mul_rpow D₀ (rpow_nonneg rp.le _),←rpow_mul rp.le]
  congr 2
  ring

/-- Finite positive absolute moments below the sharp radius exponent, for
the actual whole-circle mean after s+1 reciprocal-step updates. -/
theorem moment (N m s : ℕ) (hN : 3≤N) (odd : Odd N) (hm : 0<m) (c p : ℝ) (hc : 0<c) (hp : 0<p)
    (small : (4*(3:ℝ)^s-2)*p < 3*(m:ℝ)) :
    Integrable (fun z => |CircleReciprocal.Y N m (s+1) c z|^p) (seedLaw m) := by
  let e := 4*3^s
  let a := ((e:ℝ)-2)*p
  have expEq : (e:ℝ)=4*(3:ℝ)^s := by dsimp [e];push_cast;rfl
  have a₀ : 0≤a := mul_nonneg (by rw [expEq]; linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤3) (n:=s)]) hp.le
  have small' : a<3*(m:ℝ) := by simpa only [a,expEq] using small
  obtain ⟨D,D₀,env⟩ := output_envelope N m s hN odd hm c hc
  have hrad := (radius_power_mem m 2 (ENNReal.ofReal p) ENNReal.ofReal_ne_top).integrable_norm_rpow'
  simp only [ENNReal.toReal_ofReal hp.le,Real.norm_of_nonneg (sq_nonneg _)] at hrad
  have hinv := inverse_radius_integrable hm a₀ small'
  have dom := (hrad.add hinv).const_mul (D^p)
  have obs := CircleReciprocal.Y_measurable N m (s+1) c hN odd hm
  apply dom.mono' ((continuous_abs.measurable.comp obs).pow_const p).aestronglyMeasurable
  filter_upwards [gaussian_hidden_ne_zero m,nz_coords m] with ω nz nn
  let r := length ω
  have rp : 0<r := (abs_pos.mpr (nn (⟨0,hm⟩,0))).trans_le (coordinate_le ω _)
  have g := env ω rp nz
  have DP := rpow_nonneg D₀ p
  change |CircleReciprocal.Y N m (s+1) c ω|≤D*r^2*(max 1 (1/r))^e at g
  change ‖|CircleReciprocal.Y N m (s+1) c ω|^p‖ ≤ D^p*(((radius ω)^2)^p + r^(-a))
  rw [Real.norm_of_nonneg (rpow_nonneg (abs_nonneg _) _)]
  apply (rpow_le_rpow (abs_nonneg _) g hp.le).trans
  by_cases big : 1≤r
  · rw [max_eq_left ((div_le_one rp).mpr big),one_pow,mul_one,mul_rpow D₀ (sq_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ DP
    have le := rpow_le_rpow (sq_nonneg r) (pow_le_pow_left₀ rp.le (length_le_radius ω) 2) hp.le
    exact le.trans (le_add_of_nonneg_right (rpow_nonneg rp.le _))
  · rw [max_eq_right ((one_le_div rp).mpr (le_of_not_ge big)),small_output_power r D p e rp D₀]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (rpow_nonneg (sq_nonneg _) _)) DP

theorem memLp_output (N m s : ℕ) (hN : 3≤N) (odd : Odd N) (hm : 0<m) (c p : ℝ) (hc : 0<c) (hp : 0<p)
    (small : (4*(3:ℝ)^s-2)*p < 3*(m:ℝ)) :
    MemLp (CircleReciprocal.Y N m (s+1) c) (ENNReal.ofReal p) (seedLaw m) := by
  apply (integrable_norm_rpow_iff (CircleReciprocal.Y_measurable N m (s+1) c hN odd hm).aestronglyMeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs] using moment N m s hN odd hm c p hc hp small

/-- The same finite criterion also controls the paired reference error even
for exponents strictly below one. -/
theorem paired_moment (N m s : ℕ) (hN : 3≤N) (odd : Odd N) (hm : 0<m) (c p b : ℝ) (hc : 0<c) (hp : 0<p)
    (small : (4*(3:ℝ)^s-2)*p < 3*(m:ℝ)) :
    Integrable (fun z => |CircleReciprocal.Y N m (s+1) c z-reference N m b z|^p) (seedLaw m) := by
  have h := (memLp_output N m s hN odd hm c p hc hp small).sub (reference_memLp N m b _ ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs,Pi.sub_apply] using h.integrable_norm_rpow'



/-- The critical moment order at the logarithmic short cap has polynomial
order N^(32-π² log 3). The two explicit constants account for the ceiling. -/
theorem short_threshold (N : ℕ) (hN : 3≤N) :
    ∃ s : ℕ, ⌈π^2*log (N:ℝ)⌉₊=s+1 ∧
      3/4*(N:ℝ)^(32-π^2*log 3) ≤ 3*(N:ℝ)^32/(4*(3:ℝ)^s-2) ∧
      3*(N:ℝ)^32/(4*(3:ℝ)^s-2) ≤ 9/2*(N:ℝ)^(32-π^2*log 3) := by
  let a := π^2*log 3
  let Q := (N:ℝ)^a
  let W := (N:ℝ)^(32-a)
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have n1 : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have lp : 0<π^2*log (N:ℝ) := mul_pos (sq_pos_of_pos pi_pos) (log_pos n1)
  have l₃ : 0≤log 3 := log_nonneg (by norm_num)
  have t1 := Nat.le_ceil (π^2*log (N:ℝ))
  have t2 := Nat.ceil_lt_add_one lp.le
  cases ht : ⌈π^2*log (N:ℝ)⌉₊ with
  | zero => rw [ht,Nat.cast_zero] at t1;linarith
  | succ s =>
    rw [ht,Nat.cast_succ] at t1 t2
    refine ⟨s,rfl,?_⟩
    have hi : (s:ℝ)≤π^2*log (N:ℝ) := by linarith
    have e1 : exp ((s:ℝ)*log 3)=(3:ℝ)^s := by rw [exp_nat_mul,exp_log (by norm_num : 0<(3:ℝ))]
    have e2 : exp ((π^2*log (N:ℝ))*log 3)=Q := by
      dsimp [Q];rw [rpow_def_of_pos np];dsimp [a];ring_nf
    have e3 : exp (((s:ℝ)+1)*log 3)=(3:ℝ)^s*3 := by rw [add_mul,exp_add,e1,one_mul,exp_log (by norm_num)]
    have lo : (3:ℝ)^s≤Q := e1 ▸ e2 ▸ exp_le_exp.mpr (mul_le_mul_of_nonneg_right hi l₃)
    have up : Q≤(3:ℝ)^s*3 := e2 ▸ e3 ▸ exp_le_exp.mpr (mul_le_mul_of_nonneg_right t1 l₃)
    have pp : (1:ℝ)≤3^s := one_le_pow₀ (by norm_num)
    have dp : 0<4*(3:ℝ)^s-2 := by linarith
    have w₀ : 0≤W := rpow_nonneg np.le _
    have WQ : W*Q=(N:ℝ)^32 := by
      dsimp [W,Q];rw [←rpow_add np,sub_add_cancel,←rpow_natCast];norm_num
    constructor
    · apply (le_div_iff₀ dp).mpr
      change 3/4*W*(4*(3:ℝ)^s-2)≤_
      nlinarith only [WQ,mul_le_mul_of_nonneg_left lo w₀,w₀]
    · apply (div_le_iff₀ dp).mpr
      change _≤9/2*W*(4*(3:ℝ)^s-2)
      nlinarith only [WQ,mul_le_mul_of_nonneg_left up w₀,mul_le_mul_of_nonneg_left pp w₀]

theorem short_moment_exponent : 21 < 32-π^2*log 3 ∧ 32-π^2*log 3 < 22 := by
  have pp1 : π^2<(3.15:ℝ)^2 := sq_lt_sq' (by linarith [pi_pos]) pi_lt_d2
  have pp2 : (3.14:ℝ)^2<π^2 := sq_lt_sq' (by linarith [pi_pos]) pi_gt_d2
  constructor
  · linarith only [mul_le_mul pp1.le log_three_lt_d9.le (log_nonneg (by norm_num : (1:ℝ)≤3)) (sq_nonneg (3.15:ℝ))]
  · linarith only [mul_le_mul pp2.le log_three_gt_d9.le (by norm_num : (0:ℝ)≤1.0986122885) (sq_nonneg π)]

/-- Every fixed positive moment (raw and paired) exists at every
sufficiently large odd short-cap design. -/
theorem short_moments (p : ℝ) (hp : 0<p) :
    ∀ᶠ N : ℕ in Filter.atTop, Odd N → ∀ c>0, ∀ b : ℝ,
      Integrable (fun z => |CircleReciprocal.Y N (N^32) ⌈π^2*log (N:ℝ)⌉₊ c z|^p) (seedLaw (N^32)) ∧
      Integrable (fun z => |CircleReciprocal.Y N (N^32) ⌈π^2*log (N:ℝ)⌉₊ c z-reference N (N^32) b z|^p) (seedLaw (N^32)) := by
  have e : 0<32-π^2*log 3 := by linarith [short_moment_exponent.1]
  have T := (tendsto_rpow_atTop e).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [Filter.eventually_ge_atTop 3,T.eventually_gt_atTop (2*p)] with N hn hpN odd c hc b
  obtain ⟨s,eq,bound,_⟩ := short_threshold N hn
  rw [eq]
  change 2*p<(N:ℝ)^(32-π^2*log 3) at hpN
  have le : p<3*(N:ℝ)^32/(4*(3:ℝ)^s-2) := by linarith
  have den : 0<4*(3:ℝ)^s-2 := by linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤3) (n:=s)]
  have small : (4*(3:ℝ)^s-2)*p<3*((N^32:ℕ):ℝ) := by
    rw [Nat.cast_pow,mul_comm _ p];exact (lt_div_iff₀ den).mp le
  have hm : 0<N^32 := pow_pos (by omega) _
  exact ⟨moment N (N^32) s hn odd hm c p hc hp small,paired_moment N (N^32) s hn odd hm c p b hc hp small⟩

end CircleReciprocalFinite
