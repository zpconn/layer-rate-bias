module

public import CircleSharpInitialization
public import CircleUniformMargins
import all CircleInitializationConcentration
import all CircleGaussianTracking
import all CircleSharpInitialization
import all CircleTangentDrift
import Mathlib.Tactic

/-! A Gaussian event of any prescribed fixed polynomial confidence. It
provides the original width/time bootstrap data and simultaneous margin
counts even for radii chosen from the same initialization. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
namespace CircleSharpEvent
open CircleEscapeBridge CircleFlowPath CircleTangentDrift CircleGridSpectrum CircleGaussianTracking
open CircleInitializationConcentration CircleSharpInitialization CircleUniformMargins

private theorem exp_inverse_power {n : ℝ} (hn : 0<n) (k : ℕ) {v : ℝ}
    (h : (k:ℝ)*log n ≤ v) : exp (-v) ≤ 1/n^k := by
  calc
    _ ≤ exp (-((k:ℝ)*log n)) := exp_le_exp.mpr (neg_le_neg h)
    _ = _ := by rw [exp_neg,exp_nat_mul,exp_log hn,one_div]

private theorem log_cost (N k : ℕ) (hk : k ≤ N) (hN : 1 ≤ N) :
    (k:ℝ)*log N ≤ (N:ℝ)^2 := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  simpa [sq] using mul_le_mul (show (k:ℝ) ≤ N by exact_mod_cast hk)
    (log_le_self (Nat.cast_nonneg N)) (log_nonneg hn) (Nat.cast_nonneg N)

theorem margin_power (N k : ℕ) (hk : k+17 ≤ N) :
    (seedLaw (N^32)).real (marginMesh N (N^32) (N^16))ᶜ ≤ 2/(N:ℝ)^k := by
  have hn : 0 < N := by omega
  have one : (1:ℝ) ≤ N := by exact_mod_cast hn
  have npos : (0:ℝ) < N := by exact_mod_cast hn
  have expb := exp_inverse_power npos (k+17)
    ((log_cost N (k+17) hk (by omega)).trans (pow_le_pow_right₀ one (by decide : 2≤16)))
  have h := mesh_failure N (N^32) (N^16) (by positivity) (by positivity)
  push_cast at h
  have eq : -(N:ℝ)^32 / (N:ℝ)^16 = -(N:ℝ)^16 := by field_simp
  rw [eq] at h
  apply h.trans
  calc
    _ ≤ (N:ℝ)^16*(2*N)*(1/(N:ℝ)^(k+17)) := by
      apply mul_le_mul _ expb (exp_nonneg _) (by positivity)
      gcongr; linarith
    _ = _ := by rw [pow_add]; field_simp

theorem initialization_power (N k : ℕ) [NeZero N] (hN : 36864 ≤ N) (hk : k+2 ≤ N)
    {τ ρ : ℝ} (hτ : |τ| ≤ 2) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) :
    (seedLaw (N^32)).real {ω | ¬GoodInit τ ρ (1/(N:ℝ)^7) (sampledMatrix τ)
      (fun _ : Fin N => CircleSpectrum.k0 τ) ω} ≤ 10/(N:ℝ)^k := by
  have x : (36864:ℝ) ≤ N := by exact_mod_cast hN
  have one : (1:ℝ) ≤ N := by linarith
  have npos : (0:ℝ) < N := by linarith
  have hm : 0 < N^32 := pow_pos (by omega) _
  have h := CircleGaussianBernstein.goodInit_exponential (N:=N) hm (τ:=τ) hτ (ρ:=ρ) (u:=1/(N:ℝ)^7)
    hρ hρ' (by positivity) ((div_le_one (by positivity)).mpr (one_le_pow₀ one))
  have epos : (N:ℝ)^2 ≤ (N:ℝ)^18/36864 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ)<36864)]
    calc
      _ ≤ (N:ℝ)^2 * N := mul_le_mul_of_nonneg_left x (by positivity)
      _ = _^3 := by ring
      _ ≤ _ := pow_le_pow_right₀ one (by decide : 3 ≤ 18)
  have eq : -((N^32:ℕ):ℝ)*(1/(N:ℝ)^7)^2/36864 = -((N:ℝ)^18/36864) := by
    push_cast; field_simp
  rw [eq] at h
  have ex := exp_inverse_power npos (k+2) ((log_cost N _ hk (by omega)).trans epos)
  have hb : ((N:ℝ)+1)^2+1 ≤ 5*(N:ℝ)^2 := by nlinarith [sq_nonneg ((N:ℝ)-1)]
  apply h.trans
  calc
    _ ≤ (5*(N:ℝ)^2)*(2*(1/(N:ℝ)^(k+2))) := mul_le_mul hb
      (mul_le_mul_of_nonneg_left ex (by norm_num)) (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; field_simp; ring

/-- The actual Gaussian initialization supplies a positive neuron length,
controlled initial error, bounded mean energy, residual and uniform margin
counts on the same Borel event at every fixed layer rate in the range. -/
theorem design_event (N k : ℕ) [NeZero N] (hN : 36864 ≤ N) (hk : k+17 ≤ N)
    {τ : ℝ} (hτ : |τ| ≤ 2) :
    ∃ G : Set (Seed (N^32)), MeasurableSet G ∧ (seedLaw (N^32)).real Gᶜ ≤ 14/(N:ℝ)^k ∧
      ∀ ω ∈ G, (∀ j, 0 < length ω j) ∧ meanEnergy ω ≤ 4 ∧
        initialRms N (N^32) ω ≤ (N:ℝ)^2 ∧ initialError N (N^32) τ ω ≤ 4/(N:ℝ)^7 ∧
        ∀ ρ : ℝ, 1/(N:ℝ)^16 ≤ ρ → ρ ≤ 1 →
          (∀ j : Fin N, marginMass ω ρ (circleInput N j) ≤ 32*ρ) ∧ angularMargin ω ρ ≤ 32*ρ := by
  let μ := seedLaw (N^32)
  let M := marginMesh N (N^32) (N^16)
  let I := {ω : Seed (N^32) | ¬ GoodInit τ 0 (1/(N:ℝ)^7) (sampledMatrix τ)
      (fun _ : Fin N => CircleSpectrum.k0 τ) ω}
  let Z := {ω : Seed (N^32) | ¬∀ j, 0 < length ω j}
  let R := {ω : Seed (N^32) | 2+64*sqrt (((k:ℝ)+1)*log N) < initialRms N (N^32) ω}
  let D := ((Mᶜ ∪ I) ∪ R) ∪ Z
  refine ⟨(toMeasurable μ D)ᶜ,(measurableSet_toMeasurable μ D).compl,?_,?_⟩
  · change μ.real ((toMeasurable μ D)ᶜ)ᶜ ≤ _
    rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    have z : μ.real Z = 0 := by rw [measureReal_def, (ae_iff.mp (length_pos_ae (N^32)) : μ Z = 0)]; simp
    have hM : μ.real Mᶜ ≤ 2/(N:ℝ)^k := margin_power N k hk
    have hI : μ.real I ≤ 10/(N:ℝ)^k := initialization_power N k hN (by omega) hτ le_rfl zero_le_one
    have hR : μ.real R ≤ 2/(N:ℝ)^k := initialRms_schedule_tail k (by omega)
    dsimp only [D]
    have hb := (measureReal_union_le (μ:=μ) ((Mᶜ∪I)∪R) Z).trans
      (add_le_add ((measureReal_union_le (μ:=μ) (Mᶜ∪I) R).trans
        (add_le_add (measureReal_union_le (μ:=μ) Mᶜ I) le_rfl)) le_rfl)
    apply hb.trans
    rw [z,add_zero]
    exact ((add_le_add (add_le_add hM hI) hR)).trans_eq (by ring)
  · intro ω hg
    have hd : ω ∉ D := fun hh => hg (subset_toMeasurable μ D hh)
    have h : ω ∈ M ∧ ω ∉ I ∧ ω ∉ R ∧ ω ∉ Z := by simpa [D,not_or,and_assoc] using hd
    have hs : GoodInit τ 0 (1/(N:ℝ)^7) (sampledMatrix τ) (fun _ : Fin N => CircleSpectrum.k0 τ) ω :=
      not_not.mp h.2.1
    have npos : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have nr : (36864:ℝ) ≤ N := by exact_mod_cast hN
    have rbound : 2+64*sqrt (((k:ℝ)+1)*log N) ≤ (N:ℝ)^2 := by
      have lo := log_cost N (k+1) (by omega) (by omega)
      push_cast at lo
      have hb := Real.sqrt_le_sqrt lo
      rw [sqrt_sq npos.le] at hb
      nlinarith [mul_nonneg (sub_nonneg.mpr nr) npos.le]
    refine ⟨not_not.mp h.2.2.2, hs.energy, (le_of_not_gt h.2.2.1).trans rbound,?_,?_⟩
    · convert initialError_le_of_good (by positivity : 0 ≤ 1/(N:ℝ)^7) hs using 1
      ring
    · intro ρ hρ hu
      exact uniform_margins N (N^32) (N^16) (by positivity) h.1 ρ (by simpa using hρ) hu
end CircleSharpEvent
