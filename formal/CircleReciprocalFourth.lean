module

public import CircleReciprocalFinite
public import CircleShortGDTails
import all CircleReciprocalFinite
import all CircleReciprocal
import all CircleCapInduction
import all CircleSeedIntegrability
import all CircleEscape
import all CircleEscapeBridge
import all CircleShortGDTails
import all CircleFlowMoments
import all CircleGaussianTracking
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! Quantitative fourth moments and the rare-event contribution of the
uncapped reciprocal step at the logarithmic training cap. -/
@[expose] public section
noncomputable section
namespace CircleReciprocalFourth
open CircleReciprocalFinite CircleSeedIntegrability CircleEscapeBridge CircleEscape CircleCapInduction
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology

def weight (x : ℝ) := 1+|x|^(-(1/2:ℝ))
def normalWeight := ∫ x : ℝ, weight x ∂gaussianReal 0 1
private theorem weight_integrable : Integrable weight (gaussianReal 0 1) :=
  (integrable_const 1).add (scalar_inverse (by norm_num : (0:ℝ)≤1/2) (by norm_num))
private theorem weight_one (x : ℝ) : 1≤weight x := le_add_of_nonneg_right (rpow_nonneg (abs_nonneg _) _)
private theorem normalWeight_one : 1≤normalWeight := by
  unfold normalWeight
  simpa only [integral_const,probReal_univ,one_smul] using integral_mono (integrable_const 1) weight_integrable weight_one

private def factor {m : ℕ} (ω : Seed m) := max 1 (1/length ω)

private theorem factor_measurable (m : ℕ) : Measurable (factor (m:=m)) :=
  measurable_const.max (measurable_const.div (measurable_length m))

/-- Select 2q independent coordinates. Each contributes only one finite
scalar half-inverse moment, keeping the bound exponential in q even when
width is much larger. -/
private theorem inverse_power (m q : ℕ) (width : 2*q≤3*m) :
    Integrable (fun ω : Seed m => (factor ω)^q) (seedLaw m) ∧
      (∫ ω : Seed m, (factor ω)^q ∂seedLaw m) ≤ normalWeight^(2*q) := by
  classical
  have card : 2*q≤(Finset.univ : Finset (Fin m × Fin 3)).card := by simpa [Fintype.card_prod,mul_comm] using width
  obtain ⟨S,_,size⟩ := Finset.exists_subset_card_eq card
  let f := fun (i : Fin m × Fin 3) (x : ℝ) => if i∈S then weight x else 1
  let prod := fun ω : Seed m => ∏ i, f i (ω i)
  have fint (i) : Integrable (f i) (gaussianReal 0 1) := by
    by_cases hi : i∈S <;> simp only [f,hi,ite_true,ite_false]
    · exact weight_integrable
    · exact integrable_const 1
  have pInt : Integrable prod (seedLaw m) := Integrable.fintype_prod fint
  have eval : (∫ ω, prod ω ∂seedLaw m)=normalWeight^(2*q) := by
    change (∫ ω, ∏ i, f i (ω i) ∂Measure.pi (fun _ => gaussianReal 0 1))=_
    rw [integral_fintype_prod_eq_prod]
    have eq : (∏ i, ∫ x, f i x ∂gaussianReal 0 1) = ∏ i ∈ S, (∫ x, f i x ∂gaussianReal 0 1) := by
      apply Eq.symm;apply Finset.prod_subset (Finset.subset_univ S);intro i _ hi;simp [f,hi]
    rw [eq]
    calc _ = ∏ _i ∈ S, normalWeight := Finset.prod_congr rfl fun i hi => by simp [f,hi,normalWeight]
         _ = _ := by rw [Finset.prod_const,size]
  have bound : ∀ᵐ ω : Seed m ∂seedLaw m, (factor ω)^q ≤ prod ω := by
    filter_upwards [nz_coords m] with ω nz
    have vn : 0≤factor ω := zero_le_one.trans (le_max_left _ _)
    have dom (i) : sqrt (factor ω) ≤ weight (ω i) := by
      have x := abs_pos.mpr (nz i)
      have r := x.trans_le (coordinate_le ω i)
      by_cases big : 1≤length ω
      · rw [factor,max_eq_left ((div_le_one r).mpr big),sqrt_one];exact weight_one _
      · rw [factor,max_eq_right ((one_le_div r).mpr (le_of_not_ge big)),one_div,sqrt_inv,
          sqrt_eq_rpow,←rpow_neg r.le]
        exact (rpow_le_rpow_of_nonpos x (coordinate_le ω i) (by norm_num)).trans
          (le_add_of_nonneg_left zero_le_one)
    have h := Finset.prod_le_prod₀ (s:=S) (fun _ _ => sqrt_nonneg (factor ω)) (fun i _ => dom i)
    rw [Finset.prod_const,size,pow_mul,sq_sqrt vn] at h
    apply h.trans_eq
    change (∏ i ∈ S, weight (ω i))=∏ i, f i (ω i)
    calc _ = ∏ i ∈ S, f i (ω i) := Finset.prod_congr rfl (fun i hi => by simp [f,hi])
         _ = _ := Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by simp [f,hi])
  have integ : Integrable (fun ω : Seed m => factor ω^q) (seedLaw m) := by
    apply pInt.mono' ((factor_measurable m).pow_const q).aestronglyMeasurable
    filter_upwards [bound] with ω h
    have pos : 0≤factor ω := zero_le_one.trans (le_max_left _ _)
    rwa [Real.norm_of_nonneg (pow_nonneg pos q)]
  exact ⟨integ,(integral_mono_ae integ pInt bound).trans_eq eval⟩



def coefficient (c : ℝ) := 256*(1+|c|)*(1+normalWeight)*exp 9
def base (m : ℕ) (c : ℝ) : ℝ := 2*(coefficient c)*(1+m)^2

private theorem base_bounds (m : ℕ) (c : ℝ) (hc : 0<c) :
    let A := base m c/2
    1+16*(m:ℝ)*c*(m+2)≤A ∧ 8*(1+3*(m:ℝ))≤A ∧ 6*(m:ℝ)≤A ∧
    (m:ℝ)+2≤A ∧ normalWeight≤A ∧ exp 9≤A ∧ 2≤A := by
  intro A
  have e1 : 1≤exp 9 := one_le_exp (by norm_num)
  have h := normalWeight_one
  have sp : 1≤(1+(m:ℝ))^2 := one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg m))
  have aeq : A=coefficient c*(1+(m:ℝ))^2 := by dsimp [A,base];ring
  have csize : 256*(1+c)≤coefficient c := by
    dsimp [coefficient];rw [abs_of_pos hc]
    apply (le_mul_of_one_le_right (by positivity) (by linarith : 1≤1+normalWeight)).trans
    exact le_mul_of_one_le_right (by positivity) e1
  have cb := mul_le_mul_of_nonneg_right csize (sq_nonneg (1+(m:ℝ)))
  rw [←aeq] at cb
  have c1 : 1≤256*(1+|c|) := by linarith [abs_nonneg c]
  have w : 1+normalWeight ≤ 256*(1+|c|)*(1+normalWeight) := le_mul_of_one_le_left (by linarith) c1
  have b : 1+normalWeight≤coefficient c := w.trans (le_mul_of_one_le_right (by linarith) e1)
  have a : coefficient c≤A := aeq ▸ le_mul_of_one_le_right (by linarith) sp
  have ex : exp 9≤coefficient c := le_mul_of_one_le_left (exp_pos _).le (by linarith : 1≤256*(1+|c|)*(1+normalWeight))
  have nn : 0≤(m:ℝ) := Nat.cast_nonneg _
  have n2 := sq_nonneg (m:ℝ)
  refine ⟨?_,?_,?_,?_,(by linarith : normalWeight≤1+normalWeight).trans (b.trans a),ex.trans a,?_⟩ <;>
    nlinarith only [cb,nn,n2,mul_nonneg hc.le nn,mul_nonneg hc.le n2,hc]

private theorem parameter (N m : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m) (c : ℝ) (hc : 0<c)
    (ω : Seed m) (rp : 0<length ω) (nz : ∀ j, (initial ω).w j ≠ 0) (t : ℕ) :
    let r := length ω
    let V := factor ω
    let A := base m c/2
    Bounded (path N m (CircleReciprocal.rate N m c ω) ω t) (r*((base m c*V)^(3^t)/A)) := by
  intro r V A
  have p := base_bounds m c hc
  have a1 : 1≤A := (by norm_num : (1:ℝ)≤2).trans p.2.2.2.2.2.2
  have ap : 0<A := zero_lt_one.trans_le a1
  have bA : base m c=2*A := by dsimp [A];ring
  have v1 : 1≤V := le_max_left _ _
  have v0 := zero_le_one.trans v1
  have bv : 1≤base m c*V := one_le_mul_of_one_le_of_one_le (by linarith [bA]) v1
  have sm : 1≤sqrt (m:ℝ) := one_le_sqrt.mpr (by exact_mod_cast hm)
  have kbd := (rate_radius N m hn odd hm c hc ω rp nz).trans (div_le_self (by positivity) sm)
  induction t with
  | zero =>
    have eq : r*((base m c*V)^(3^0)/A)=2*r*V := by rw [bA];simp only [pow_zero,pow_one];field_simp
    rw [eq]
    exact bound_mono (init_small ω) (le_mul_of_one_le_right (by positivity) v1)
  | succ t ih =>
    let X := (base m c*V)^(3^t)/A
    have vx : V≤X := by
      apply (le_div_iff₀ ap).mpr
      exact (by rw [bA];nlinarith [mul_nonneg ap.le v0] : V*A≤base m c*V).trans
        (le_self_pow₀ bv (by positivity))
    have x1 : 1≤X := v1.trans vx
    have xp := zero_le_one.trans x1
    let g := 1/sqrt (m:ℝ)
    have gs : |g|≤1 := by dsimp [g];rw [abs_of_nonneg (by positivity)];exact (div_le_one (by positivity)).mpr sm
    have G : |g| *(m:ℝ)≤m := by simpa only [one_mul] using mul_le_mul_of_nonneg_right gs (Nat.cast_nonneg m)
    have bs := step_rescale (V:=V) (g:=g) rp (le_max_right 1 _) kbd xp ih
    have coeff : 1+16*(m:ℝ)*c*((|g| *m)*X^2+2*V^2) ≤ A*X^2 := by
      have sx : 1≤X^2 := one_le_pow₀ x1
      have high : (|g| *m)*X^2+2*V^2 ≤ (m+2)*X^2 := by
        nlinarith only [mul_le_mul_of_nonneg_right G (sq_nonneg X), pow_le_pow_left₀ v0 vx 2]
      have upper := mul_le_mul_of_nonneg_left high (show 0≤16*(m:ℝ)*c by positivity)
      have d := mul_le_mul_of_nonneg_right p.1 (sq_nonneg X)
      change (1+16*(m:ℝ)*c*(m+2))*X^2≤A*X^2 at d
      nlinarith only [upper,d,sx]
    apply bound_mono bs
    apply mul_le_mul_of_nonneg_left _ rp.le
    calc
      _ ≤ X*(A*X^2) := mul_le_mul_of_nonneg_left coeff xp
      _ = ((base m c*V)^(3^t))^3/A^2 := by dsimp [X];field_simp
      _ ≤ (base m c*V)^(3^(t+1))/A := by
        rw [pow_succ (3:ℕ) t,pow_mul]
        exact div_le_div_of_nonneg_left (by positivity) ap (by nlinarith only [mul_le_mul_of_nonneg_left a1 ap.le])

private theorem output (N m t : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m) (c : ℝ) (hc : 0<c)
    (ω : Seed m) (rp : 0<length ω) (nz : ∀ j, (initial ω).w j≠0) :
    |CircleReciprocal.Y N m t c ω| ≤ (m*(base m c)^(2*3^t))*(length ω)^2*(factor ω)^(2*3^t) := by
  have p := base_bounds m c hc
  have a1 : 1≤base m c/2 := (by norm_num : (1:ℝ)≤2).trans p.2.2.2.2.2.2
  have V₀ : 0≤factor ω := zero_le_one.trans (le_max_left _ _)
  have B : 0≤base m c := by linarith
  have r := parameter N m hn odd hm c hc ω rp nz t
  have r' := bound_mono r (mul_le_mul_of_nonneg_left (div_le_self (pow_nonneg (mul_nonneg B V₀) _) a1) rp.le)
  let g := 1/sqrt (m:ℝ)
  have cp : |g/π|≤1 := by
    rw [abs_of_nonneg (by dsimp [g];positivity)]
    apply (div_le_self (by dsimp [g];positivity) (by linarith [pi_gt_three])).trans
    exact (div_le_one (by positivity)).mpr (one_le_sqrt.mpr (by exact_mod_cast hm))
  have ub := mean_cap g _ (by positivity) _ r'
  apply ub.trans
  have a := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cp (Nat.cast_nonneg m))
    (sq_nonneg (length ω*((base m c*factor ω)^(3^t))))
  apply a.trans_eq
  change (1*(m:ℝ))*(length ω*((base m c*factor ω)^(3^t)))^2 = _
  rw [mul_pow,mul_pow,mul_pow,show 2*3^t=3^t*2 by omega,pow_mul,pow_mul];ring



private theorem paired_point (N m t : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m) (c b : ℝ)
    (hc : 0<c) (hb : 0≤b) (hb' : b≤1) (ω : Seed m) (rp : 0<length ω) (nz : ∀ j, (initial ω).w j≠0) :
    (CircleReciprocal.Y N m t c ω-reference N m b ω)^4 ≤
      (base m c)^(4*(2*3^t+1))*((radius ω)^8+(factor ω)^(8*3^t)) := by
  let B := base m c
  let h := 3^t
  let r := length ω
  let V := factor ω
  let R := radius ω
  have bnd := base_bounds m c hc
  have b2 : 2≤B/2 := bnd.2.2.2.2.2.2
  have b1 : 1≤B := by linarith
  have mB : (m:ℝ)+2≤B := by linarith [bnd.2.2.2.1]
  have R1 : 1≤R := radius_one _
  have V1 : 1≤V := le_max_left _ _
  have bH : 1≤B^(2*h) := one_le_pow₀ b1
  have rC := length_le_radius ω
  have yy := output N m t hn odd hm c hc ω rp nz
  change _≤((m:ℝ)*B^(2*h))*r^2*V^(2*h) at yy
  have tr := CircleFlowMoments.reference_cap ω (show 0<N by omega) hb hb'
  have sm : 1≤sqrt (m:ℝ) := one_le_sqrt.mpr (by exact_mod_cast hm)
  have sumid : (∑ i, (ω i)^2)=r^2 := (sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (ω i)))).symm
  change _≤1+(1/sqrt (m:ℝ))*(∑ i, (ω i)^2) at tr
  rw [sumid] at tr
  have refb := tr.trans (add_le_add (le_refl 1) (show (1/sqrt (m:ℝ))*r^2≤r^2 from mul_le_of_le_one_left (sq_nonneg r)
    ((div_le_one (by positivity)).mpr sm)))
  have ar := (abs_sub _ _).trans (add_le_add yy refb)
  have Bmul : (m:ℝ)*B^(2*h)+2≤B^(2*h+1) := by
    rw [pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_left mB (zero_le_one.trans bH),bH]
  let Y := CircleReciprocal.Y N m t c ω-reference N m b ω
  change |Y|≤((m:ℝ)*B^(2*h))*r^2*V^(2*h)+(1+r^2) at ar
  change Y^4≤B^(4*(2*h+1))*(R^8+V^(8*h))
  rw [show 4*(2*h+1)=(2*h+1)*4 by omega,pow_mul]
  by_cases big : 1≤r
  · have v : V=1 := max_eq_left ((div_le_one rp).mpr big)
    rw [v,one_pow,mul_one] at ar
    have rr := pow_le_pow_left₀ rp.le rC 2
    have aa : |Y|≤B^(2*h+1)*R^2 := by
      apply ar.trans
      calc _ ≤ ((m:ℝ)*B^(2*h)+2)*r^2 := by linarith only [one_le_pow₀ big (n:=2)]
           _ ≤ _ := mul_le_mul Bmul rr (sq_nonneg _) (pow_nonneg (zero_le_one.trans b1) _)
    have bd := pow_le_pow_left₀ (abs_nonneg _) aa 4
    rw [(by decide : Even 4).pow_abs,mul_pow,←pow_mul R] at bd
    apply bd.trans
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg (zero_le_one.trans V1) _)) (by positivity)
  · have rr := pow_le_pow_left₀ rp.le (le_of_not_ge big) 2
    rw [one_pow] at rr
    have vH : 1≤V^(2*h) := one_le_pow₀ V1
    have aa : |Y|≤B^(2*h+1)*V^(2*h) := by
      apply ar.trans
      calc _ ≤ ((m:ℝ)*B^(2*h)+2)*V^(2*h) := by
              have l := mul_le_mul_of_nonneg_left rr (show 0≤(m:ℝ)*B^(2*h)*V^(2*h) by positivity)
              nlinarith only [l,rr,vH]
           _ ≤ _ := mul_le_mul_of_nonneg_right Bmul (zero_le_one.trans vH)
    have bd := pow_le_pow_left₀ (abs_nonneg _) aa 4
    rw [(by decide : Even 4).pow_abs,mul_pow,←pow_mul V,show 2*h*4=8*h by omega] at bd
    exact bd.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity : 0≤R^8)) (by positivity))

/-- Quantitative fourth moment of the actual reciprocal learner at width m,
with the reference formed from exactly the same initialization. The base is
a fixed c-dependent constant times (1+m)^2. -/
theorem fourth (N m t : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m) (c b : ℝ)
    (hc : 0<c) (hb : 0≤b) (hb' : b≤1) (width : 16*3^t≤3*m) :
    let F := fun ω => CircleReciprocal.Y N m t c ω-reference N m b ω
    MemLp F 4 (seedLaw m) ∧ ∫ ω, F ω^4 ∂seedLaw m ≤ (base m c)^(32*3^t) := by
  intro F
  let B := base m c
  let h := 3^t
  have hpos : 0<h := pow_pos (by decide) _
  obtain ⟨invint,invbound⟩ := inverse_power m (8*h) (by dsimp [h];omega)
  have rint := (radius_power_mem m 8 1 (by norm_num)).integrable (by norm_num)
  have dom := (rint.add invint).const_mul (B^(4*(2*h+1)))
  have mF : Measurable F := (CircleReciprocal.Y_measurable N m t c hn odd hm).sub (CircleCapMoments.reference_measurable N m b)
  have pt : ∀ᵐ ω ∂seedLaw m, F ω^4 ≤ B^(4*(2*h+1))*((radius ω)^8+(factor ω)^(8*h)) := by
    filter_upwards [gaussian_hidden_ne_zero m,nz_coords m] with ω nz nc
    have rp := (abs_pos.mpr (nc (⟨0,hm⟩,0))).trans_le (coordinate_le ω _)
    exact paired_point N m t hn odd hm c b hc hb hb' ω rp nz
  have integ : Integrable (fun ω => F ω^4) (seedLaw m) := by
    apply dom.mono' (mF.pow_const 4).aestronglyMeasurable
    filter_upwards [pt] with ω h
    rwa [Real.norm_of_nonneg (by positivity : 0≤F ω^4)]
  have bnd := base_bounds m c hc
  have b2 : 2≤B/2 := bnd.2.2.2.2.2.2
  have b1 : 1≤B := by linarith
  have b0 := zero_le_one.trans b1
  have ah : B/2≤B := by linarith
  have rad := CircleShortGDTails.radius_moment m 8 hm (by decide)
  have sm : (1+3*(m:ℝ))*8≤B := (mul_comm _ _).le.trans (bnd.2.1.trans ah)
  have rr : (∫ ω, (radius ω)^8 ∂seedLaw m)≤B^10 := by
    apply rad.trans
    change ((1+3*(m:ℝ))*8)^8*exp 9*(6*(m:ℝ))≤B^10
    calc _ ≤ B^8*B*B := by gcongr;exact bnd.2.2.2.2.2.1.trans ah;exact bnd.2.2.1.trans ah
         _ = _ := by ring
  have n0 := zero_le_one.trans normalWeight_one
  have inv := invbound.trans (pow_le_pow_left₀ n0 (bnd.2.2.2.2.1.trans ah) _)
  have mono := integral_mono_ae integ dom pt
  simp only [Pi.add_apply] at mono
  rw [integral_const_mul,integral_add rint invint] at mono
  refine ⟨?_,mono.trans ?_⟩
  · apply (integrable_norm_rpow_iff mF.aestronglyMeasurable (by norm_num : (4:ENNReal)≠0) (by norm_num)).mp
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat,Real.norm_eq_abs,(by decide : Even 4).pow_abs] using integ
  · change B^(4*(2*h+1))*_ ≤ B^(32*h)
    have bound : (∫ ω, (radius ω)^8 ∂seedLaw m)+(∫ ω, factor ω^(8*h) ∂seedLaw m) ≤ B^(16*h+1) := by
      have ex := pow_le_pow_right₀ b1 (show 10≤16*h by omega)
      have expEq : 2*(8*h)=16*h := by omega
      rw [expEq] at inv
      rw [pow_succ]
      have p16 : 0≤B^(16*h) := pow_nonneg b0 _
      nlinarith only [rr.trans ex,inv,mul_le_mul_of_nonneg_left (by linarith only [b2] : 2≤B) p16]
    calc _ ≤ B^(4*(2*h+1))*B^(16*h+1) := mul_le_mul_of_nonneg_left bound (pow_nonneg b0 _)
         _ ≤ _ := by rw [←pow_add];exact pow_le_pow_right₀ b1 (by omega)



private theorem short_degree (N : ℕ) (hn : 1≤N) :
    (3:ℝ)^⌈π^2*log (N:ℝ)⌉₊ ≤ 3*(N:ℝ)^11 := by
  have n1 : (1:ℝ)≤N := by exact_mod_cast hn
  have np := zero_lt_one.trans_le n1
  have ln := log_nonneg n1
  have t := Nat.ceil_lt_add_one (mul_nonneg (sq_nonneg π) ln)
  have a : π^2*log 3≤11 := by linarith [short_moment_exponent.1]
  have dl := mul_le_mul_of_nonneg_right t.le (log_nonneg (by norm_num : (1:ℝ)≤3))
  have b : (⌈π^2*log (N:ℝ)⌉₊:ℝ)*log 3 ≤ log 3+11*log (N:ℝ) := by
    nlinarith only [dl,mul_le_mul_of_nonneg_right a ln]
  have h := exp_le_exp.mpr b
  rw [exp_nat_mul,exp_log (by norm_num : 0<(3:ℝ)),exp_add,exp_log (by norm_num : 0<(3:ℝ)),
    show 11*log (N:ℝ)=log ((N:ℝ)^11) by rw [log_pow];norm_num,exp_log (by positivity)] at h
  exact h

private theorem short_width (N : ℕ) (hn : 16≤N) : 16*3^⌈π^2*log (N:ℝ)⌉₊≤3*N^32 := by
  have one : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have big : (16:ℝ)≤(N:ℝ)^21 := (show (16:ℝ)≤N by exact_mod_cast hn).trans (le_self_pow₀ one (by decide))
  have e := mul_le_mul_of_nonneg_left (short_degree N (by omega)) (by norm_num : (0:ℝ)≤16)
  have b : (16:ℝ)*3^⌈π^2*log (N:ℝ)⌉₊≤3*(N:ℝ)^32 := by
    nlinarith only [e,mul_le_mul_of_nonneg_right big (show 0≤(N:ℝ)^11 by positivity)]
  exact_mod_cast b

theorem short_memLp (N : ℕ) (hn : 16≤N) (odd : Odd N) (c b : ℝ) (hc : 0<c) (hb : 0≤b) (hb' : b≤1) :
    MemLp (fun z => CircleReciprocal.Y N (N^32) ⌈π^2*log (N:ℝ)⌉₊ c z-reference N (N^32) b z) 4
      (seedLaw (N^32)) :=
  (fourth _ _ _ (by omega) odd (pow_pos (by omega) _) c b hc hb hb' (short_width N hn)).1

private theorem short_cost (c : ℝ) (hc : 0<c) (k : ℕ) : ∀ᶠ N : ℕ in atTop,
    let B := base (N^32) c
    let T := ⌈π^2*log (N:ℝ)⌉₊
    B^(32*3^T)*exp (-((N:ℝ)^12)/2000000) ≤ 1/(N:ℝ)^k := by
  have apos : 0<coefficient c := by
    dsimp [coefficient];have w := normalWeight_one;positivity
  let L := |log (8*coefficient c)|
  let D := 96*64+(k:ℝ)
  have G := tendsto_natCast_atTop_atTop (R:=ℝ)
  have a : Tendsto (fun n : ℕ => log n/n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,rpow_one] using (isLittleO_log_rpow_atTop (r:=1) zero_lt_one).tendsto_div_nhds_zero.comp G
  have u : Tendsto (fun n : ℕ => (96*L+D*log n)/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [add_div,mul_div_assoc,add_zero,mul_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat (96*L)).add (a.const_mul D)
  filter_upwards [eventually_ge_atTop 16,u.eventually_lt_const (by norm_num : (0:ℝ)<1/2000000)] with N hn cut
  intro B T
  have n1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have np := zero_lt_one.trans_le n1
  have ln := log_nonneg n1
  have n32 := one_le_pow₀ n1 (n:=32)
  have BB := base_bounds (N^32) c hc
  have b1 : 1≤B := by linarith [BB.2.2.2.2.2.2]
  have bp := zero_lt_one.trans_le b1
  have baseLe : B≤8*coefficient c*(N:ℝ)^64 := by
    change 2*coefficient c*(1+((N^32:ℕ):ℝ))^2≤_
    rw [Nat.cast_pow]
    have z := pow_le_pow_left₀ (by positivity : 0≤1+(N:ℝ)^32) (by linarith : 1+(N:ℝ)^32≤2*(N:ℝ)^32) 2
    nlinarith only [mul_le_mul_of_nonneg_left z apos.le]
  have logB : log B≤L+64*log (N:ℝ) := by
    have z := log_le_log bp baseLe
    rw [log_mul (by positivity : 8*coefficient c≠0) (by positivity),log_pow] at z
    norm_num only [Nat.cast_ofNat] at z
    exact z.trans (add_le_add (le_abs_self _) le_rfl)
  have third : (3:ℝ)^T≤3*(N:ℝ)^11 := short_degree N (by omega)
  have w : (32*(3:ℝ)^T)*log B+(k:ℝ)*log N≤(N:ℝ)^12/2000000 := by
    have comb := mul_le_mul third logB (log_nonneg b1) (by positivity)
    have cs := (div_lt_iff₀ np).mp cut
    have n11 : 1≤(N:ℝ)^11 := one_le_pow₀ n1
    have rest := mul_le_mul_of_nonneg_right n11 (mul_nonneg (Nat.cast_nonneg k) ln)
    dsimp [D] at cs
    nlinarith only [comb,mul_le_mul_of_nonneg_right cs.le (show 0≤(N:ℝ)^11 by positivity),rest]
  calc
    _ = exp (((32*(3:ℝ)^T)*log B) + -((N:ℝ)^12)/2000000) := by
      rw [exp_add];congr 1
      rw [show (32:ℝ)*3^T=(((32*3^T):ℕ):ℝ) by push_cast;rfl,exp_nat_mul,exp_log bp]
    _ ≤ exp (-((k:ℝ)*log N)) := exp_le_exp.mpr (by linarith only [w])
    _ = _ := by rw [exp_neg,exp_nat_mul,exp_log np,one_div]

/-- On Gaussian events with probability at most exp(-N^12/10^6), the
uncapped reciprocal error contributes less than any fixed inverse power
to the unnormalized squared error at the short training cap. -/
theorem short_exceptional_order (c : ℝ) (hc : 0<c) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, Odd N → ∀ b : ℝ, 0≤b → b≤1 → ∀ E : Set (Seed (N^32)),
      (seedLaw (N^32)).real E ≤ exp (-((N:ℝ)^12)/1000000) →
      (∫ z in E, (CircleReciprocal.Y N (N^32) ⌈π^2*log (N:ℝ)⌉₊ c z-reference N (N^32) b z)^2
        ∂seedLaw (N^32)) ≤ 1/(N:ℝ)^k := by
  filter_upwards [eventually_ge_atTop 16,short_cost c hc k] with N hn cost odd b hb hb' E prob
  let T := ⌈π^2*log (N:ℝ)⌉₊
  let B := base (N^32) c
  let F := fun z => CircleReciprocal.Y N (N^32) T c z-reference N (N^32) b z
  obtain ⟨mem,upper⟩ := fourth N (N^32) T (by omega) odd (pow_pos (by omega) _) c b hc hb hb' (short_width N hn)
  have ex := CircleMoment.exceptional_second_moment (F:=F) (CircleGaussianTracking.square_mem mem) E
  have bbd := base_bounds (N^32) c hc
  have b₁ : 1≤B := by linarith [bbd.2.2.2.2.2.2]
  have w := one_le_pow₀ b₁ (n:=32*3^T)
  have root : sqrt (∫ z, F z^4 ∂seedLaw (N^32)) ≤ B^(32*3^T) := by
    apply sqrt_le_iff.mpr
    exact ⟨zero_le_one.trans w,upper.trans (by nlinarith only [mul_le_mul_of_nonneg_left w (zero_le_one.trans w)])⟩
  have prob' : sqrt ((seedLaw (N^32)).real E) ≤ exp (-((N:ℝ)^12)/2000000) := by
    apply (sqrt_le_sqrt prob).trans_eq
    rw [show exp (-((N:ℝ)^12)/1000000) = (exp (-((N:ℝ)^12)/2000000))^2 by
      rw [←exp_nat_mul];congr 1;norm_num;ring,sqrt_sq (exp_pos _).le]
  exact ex.trans ((mul_le_mul root prob' (sqrt_nonneg _) (pow_nonneg (zero_le_one.trans b₁) _)).trans cost)

theorem short_exceptional : ∀ᶠ N : ℕ in atTop, Odd N → ∀ b : ℝ, 0≤b → b≤1 →
    ∀ E : Set (Seed (N^32)), (seedLaw (N^32)).real E ≤ exp (-((N:ℝ)^12)/1000000) →
    (∫ z in E, (CircleReciprocal.Y N (N^32) ⌈π^2*log (N:ℝ)⌉₊ 1 z-reference N (N^32) b z)^2 ∂seedLaw (N^32))
      ≤ 1/(N:ℝ)^6 := short_exceptional_order 1 (by norm_num) 6

end CircleReciprocalFourth
