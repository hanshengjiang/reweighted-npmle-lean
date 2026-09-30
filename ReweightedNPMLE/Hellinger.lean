import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

namespace ReweightedNPMLE

/-- Squared Hellinger distance with respect to a dominating measure. -/
noncomputable def hellingerSq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ) : ℝ :=
  ∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ

/-- Hellinger affinity `∫ √(pq)`. -/
noncomputable def hellingerAffinity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ) : ℝ :=
  ∫ x, Real.sqrt (p x * q x) ∂μ

theorem sqrt_sub_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * Real.sqrt (a * b) := by
  rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_mul ha]
  ring

/-- The pointwise squared Hellinger integrand is bounded by absolute
density error. -/
theorem sqrt_sub_sq_le_abs_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have hsqrt : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt a + Real.sqrt b := by
    calc
      |Real.sqrt a - Real.sqrt b| ≤ |Real.sqrt a| + |Real.sqrt b| := abs_sub _ _
      _ = Real.sqrt a + Real.sqrt b := by
        rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    (Real.sqrt a - Real.sqrt b) ^ 2 =
        |Real.sqrt a - Real.sqrt b| ^ 2 := (sq_abs _).symm
    _ ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) :=
      by simpa [pow_two] using
        mul_le_mul_of_nonneg_left hsqrt (abs_nonneg (Real.sqrt a - Real.sqrt b))
    _ = |a - b| := by
      rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
        ← abs_mul]
      apply congrArg abs
      calc
        (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) =
            Real.sqrt a ^ 2 - Real.sqrt b ^ 2 := by ring
        _ = a - b := by rw [Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- Consequently squared Hellinger distance is at most `L¹` distance. -/
theorem hellingerSq_le_integral_abs_sub
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hhell : Integrable
      (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ)
    (hl1 : Integrable (fun x ↦ |p x - q x|) μ) :
    hellingerSq μ p q ≤ ∫ x, |p x - q x| ∂μ := by
  unfold hellingerSq
  apply integral_mono_ae hhell hl1
  filter_upwards [hp, hq] with x hpx hqx
  exact sqrt_sub_sq_le_abs_sub hpx hqx

/-- Weighted Cauchy--Schwarz in the exact form used by the Gaussian-mixture
net argument.  A positive reference density converts weighted `L²` error
into ordinary `L¹` error. -/
theorem integral_abs_le_sqrt_weightedL2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h φ : Ω → ℝ)
    (hh : AEStronglyMeasurable h μ) (hφm : AEStronglyMeasurable φ μ)
    (hφpos : ∀ᵐ x ∂μ, 0 < φ x)
    (hweighted : Integrable (fun x ↦ h x ^ 2 / φ x) μ)
    (hφint : Integrable φ μ) :
    ∫ x, |h x| ∂μ ≤
      (∫ x, h x ^ 2 / φ x ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, φ x ∂μ) ^ (1 / 2 : ℝ) := by
  let f : Ω → ℝ := fun x ↦ |h x| / Real.sqrt (φ x)
  let g : Ω → ℝ := fun x ↦ Real.sqrt (φ x)
  have hgmeas : AEStronglyMeasurable g μ := by
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hφm
  have hfmeas : AEStronglyMeasurable f μ := by
    exact (hh.norm.aemeasurable.div hgmeas.aemeasurable).aestronglyMeasurable
  have hf_sq : Integrable (fun x ↦ f x ^ 2) μ := by
    apply hweighted.congr
    filter_upwards [hφpos] with x hx
    dsimp [f]
    rw [div_pow, sq_abs, Real.sq_sqrt hx.le]
  have hg_sq : Integrable (fun x ↦ g x ^ 2) μ := by
    apply hφint.congr
    filter_upwards [hφpos] with x hx
    dsimp [g]
    exact (Real.sq_sqrt hx.le).symm
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfmeas).2 hf_sq
  have hg : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgmeas).2 hg_sq
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) Real.HolderConjugate.two_two
    (f := f) (g := g)
    (Filter.Eventually.of_forall fun x ↦
      div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall fun x ↦ Real.sqrt_nonneg _) hf' hg'
  calc
    (∫ x, |h x| ∂μ) = ∫ x, f x * g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hφpos] with x hx
      dsimp [f, g]
      field_simp [Real.sqrt_ne_zero'.2 hx]
    _ ≤ (∫ x, f x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder
    _ = (∫ x, h x ^ 2 / φ x ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, φ x ∂μ) ^ (1 / 2 : ℝ) := by
      congr 2
      · apply integral_congr_ae
        filter_upwards [hφpos] with x hx
        dsimp [f]
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
        rw [div_pow, sq_abs, Real.sq_sqrt hx.le]
      · apply integral_congr_ae
        filter_upwards [hφpos] with x hx
        dsimp [g]
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
        exact Real.sq_sqrt hx.le

/-- For a normalized positive reference density, weighted `L²` error bounds
squared Hellinger distance by its square root. -/
theorem hellingerSq_le_sqrt_weightedL2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q φ : Ω → ℝ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpqmeas : AEStronglyMeasurable (fun x ↦ p x - q x) μ)
    (hφmeas : AEStronglyMeasurable φ μ)
    (hφpos : ∀ᵐ x ∂μ, 0 < φ x)
    (hhell : Integrable
      (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ)
    (hl1 : Integrable (fun x ↦ |p x - q x|) μ)
    (hweighted : Integrable (fun x ↦ (p x - q x) ^ 2 / φ x) μ)
    (hφint : Integrable φ μ) (hφone : ∫ x, φ x ∂μ = 1) :
    hellingerSq μ p q ≤
      (∫ x, (p x - q x) ^ 2 / φ x ∂μ) ^ (1 / 2 : ℝ) := by
  calc
    hellingerSq μ p q ≤ ∫ x, |p x - q x| ∂μ :=
      hellingerSq_le_integral_abs_sub μ p q hp hq hhell hl1
    _ ≤ (∫ x, (p x - q x) ^ 2 / φ x ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, φ x ∂μ) ^ (1 / 2 : ℝ) :=
      integral_abs_le_sqrt_weightedL2 μ (fun x ↦ p x - q x) φ
        hpqmeas hφmeas hφpos hweighted hφint
    _ = (∫ x, (p x - q x) ^ 2 / φ x ∂μ) ^ (1 / 2 : ℝ) := by
      rw [hφone]
      norm_num

theorem hellingerSq_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ) : 0 ≤ hellingerSq μ p q := by
  apply integral_nonneg
  intro x
  exact sq_nonneg _

/-- Integrable nonnegative densities have an integrable squared Hellinger
integrand.  This discharges a recurring analytic side condition for finite
Gaussian mixtures. -/
theorem hellingerIntegrand_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
  have hmeas : AEStronglyMeasurable
      (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
    exact ((Real.continuous_sqrt.comp_aestronglyMeasurable hpmeas).sub
      (Real.continuous_sqrt.comp_aestronglyMeasurable hqmeas)).pow 2
  apply ((hpint.add hqint).const_mul 2).mono' hmeas
  filter_upwards [hp, hq] with x hpx hqx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ≤ 2 * (p x + q x)
  nlinarith [sq_nonneg (Real.sqrt (p x) + Real.sqrt (q x)),
    Real.sq_sqrt hpx, Real.sq_sqrt hqx]

/-- For nonnegative integrable densities, squared Hellinger distance vanishes
exactly when the two densities agree almost everywhere. -/
theorem hellingerSq_eq_zero_iff_ae_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    hellingerSq μ p q = 0 ↔ p =ᵐ[μ] q := by
  have hint := hellingerIntegrand_integrable_of_integrable μ p q
    hpmeas hqmeas hp hq hpint hqint
  have hzero :
      (∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ) = 0 ↔
        (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) =ᵐ[μ] 0 :=
    integral_eq_zero_iff_of_nonneg
      (fun x ↦ sq_nonneg (Real.sqrt (p x) - Real.sqrt (q x))) hint
  unfold hellingerSq
  rw [hzero]
  constructor
  · intro h
    filter_upwards [h, hp, hq] with x hx hpx hqx
    have hsqrt : Real.sqrt (p x) = Real.sqrt (q x) := by
      have : Real.sqrt (p x) - Real.sqrt (q x) = 0 :=
        sq_eq_zero_iff.mp hx
      linarith
    exact (Real.sqrt_inj hpx hqx).mp hsqrt
  · intro h
    filter_upwards [h] with x hx
    simp only [hx, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Pi.zero_apply]

/-- The square-root affinity integrand is integrable for any two integrable
nonnegative densities. -/
theorem sqrt_mul_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ Real.sqrt (p x * q x)) μ := by
  have hhell := hellingerIntegrand_integrable_of_integrable
    μ p q hpmeas hqmeas hp hq hpint hqint
  have hcomb := ((hpint.add hqint).sub hhell).const_mul (1 / 2 : ℝ)
  apply hcomb.congr
  filter_upwards [hp, hq] with x hpx hqx
  have hs := sqrt_sub_sq hpx hqx
  change (1 / 2 : ℝ) *
      (p x + q x - (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) =
    Real.sqrt (p x * q x)
  linarith

theorem abs_sub_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ |p x - q x|) μ := by
  exact (hpint.sub hqint).abs

/-- Total-variation (`L¹`) error is controlled by squared Hellinger distance.
For probability densities in the manuscript's normalization,
`∫ |p - q| ≤ 2 √(H²(p,q))`. -/
theorem integral_abs_sub_le_two_mul_sqrt_hellingerSq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (hpone : ∫ x, p x ∂μ = 1) (hqone : ∫ x, q x ∂μ = 1) :
    ∫ x, |p x - q x| ∂μ ≤ 2 * Real.sqrt (hellingerSq μ p q) := by
  let f : Ω → ℝ := fun x ↦ |Real.sqrt (p x) - Real.sqrt (q x)|
  let g : Ω → ℝ := fun x ↦ Real.sqrt (p x) + Real.sqrt (q x)
  have hfmeas : AEStronglyMeasurable f μ := by
    exact (((Real.continuous_sqrt.comp_aestronglyMeasurable hpmeas).sub
      (Real.continuous_sqrt.comp_aestronglyMeasurable hqmeas)).norm)
  have hgmeas : AEStronglyMeasurable g μ := by
    exact (Real.continuous_sqrt.comp_aestronglyMeasurable hpmeas).add
      (Real.continuous_sqrt.comp_aestronglyMeasurable hqmeas)
  have hhell := hellingerIntegrand_integrable_of_integrable
    μ p q hpmeas hqmeas hp hq hpint hqint
  have hfsq : Integrable (fun x ↦ f x ^ 2) μ := by
    apply hhell.congr
    exact Filter.Eventually.of_forall fun x ↦ by
      simp only [f, sq_abs]
  have hgsq : Integrable (fun x ↦ g x ^ 2) μ := by
    apply ((hpint.add hqint).const_mul 2).mono' (hgmeas.pow 2)
    filter_upwards [hp, hq] with x hpx hqx
    change ‖g x ^ 2‖ ≤ 2 * (p x + q x)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    dsimp [g]
    nlinarith [Real.sq_sqrt hpx, Real.sq_sqrt hqx,
      sq_nonneg (Real.sqrt (p x) - Real.sqrt (q x))]
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfmeas).2 hfsq
  have hg : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgmeas).2 hgsq
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) Real.HolderConjugate.two_two
    (f := f) (g := g)
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg _)
    (Filter.Eventually.of_forall fun x ↦
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hf' hg'
  have hholder' :
      ∫ x, f x * g x ∂μ ≤
        Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
    norm_num [Real.sqrt_eq_rpow] at hholder ⊢
    exact hholder
  have hgfour : ∫ x, g x ^ 2 ∂μ ≤ 4 := by
    calc
      (∫ x, g x ^ 2 ∂μ) ≤ ∫ x, 2 * (p x + q x) ∂μ := by
        apply integral_mono_ae hgsq ((hpint.add hqint).const_mul 2)
        filter_upwards [hp, hq] with x hpx hqx
        dsimp [g]
        nlinarith [Real.sq_sqrt hpx, Real.sq_sqrt hqx,
          sq_nonneg (Real.sqrt (p x) - Real.sqrt (q x))]
      _ = 4 := by
        rw [integral_const_mul, integral_add hpint hqint, hpone, hqone]
        norm_num
  have hgroot : Real.sqrt (∫ x, g x ^ 2 ∂μ) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hprod :
      (∫ x, |p x - q x| ∂μ) = ∫ x, f x * g x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hp, hq] with x hpx hqx
    dsimp [f, g]
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hpx, Real.sq_sqrt hqx]
  have hfhell : (∫ x, f x ^ 2 ∂μ) = hellingerSq μ p q := by
    unfold hellingerSq
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by simp only [f, sq_abs]
  calc
    (∫ x, |p x - q x| ∂μ) = ∫ x, f x * g x ∂μ := hprod
    _ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := hholder'
    _ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * 2 :=
      mul_le_mul_of_nonneg_left hgroot (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (hellingerSq μ p q) := by rw [hfhell]; ring

/-- Scheffé's lemma for real probability densities.  Pointwise almost-everywhere
convergence, nonnegativity, and preservation of total mass upgrade to `L¹`
convergence. -/
theorem tendsto_integral_abs_sub_of_ae_tendsto_of_integral_eq_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ℕ → Ω → ℝ) (q : Ω → ℝ)
    (hpmeas : ∀ n, AEStronglyMeasurable (p n) μ)
    (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ n, ∀ᵐ x ∂μ, 0 ≤ p n x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : ∀ n, Integrable (p n) μ) (hqint : Integrable q μ)
    (hpone : ∀ n, ∫ x, p n x ∂μ = 1) (hqone : ∫ x, q x ∂μ = 1)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ p n x) atTop (𝓝 (q x))) :
    Tendsto (fun n ↦ ∫ x, |p n x - q x| ∂μ) atTop (𝓝 0) := by
  let m : ℕ → Ω → ℝ := fun n x ↦ min (p n x) (q x)
  have hmmeas : ∀ n, AEStronglyMeasurable (m n) μ := fun n ↦ by
    exact ((hpmeas n).aemeasurable.min hqmeas.aemeasurable).aestronglyMeasurable
  have hm_bound : ∀ n, ∀ᵐ x ∂μ, ‖m n x‖ ≤ q x := fun n ↦ by
    filter_upwards [hp n, hq] with x hpx hqx
    dsimp [m]
    rw [abs_of_nonneg (le_min hpx hqx)]
    exact min_le_right _ _
  have hm_lim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ m n x) atTop (𝓝 (q x)) := by
    filter_upwards [hlim] with x hx
    simpa only [m, min_self] using hx.min
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ q x) atTop (𝓝 (q x)))
  have hm_integral :
      Tendsto (fun n ↦ ∫ x, m n x ∂μ) atTop (𝓝 1) := by
    have h := tendsto_integral_of_dominated_convergence q hmmeas hqint hm_bound hm_lim
    simpa only [hqone] using h
  have hmint : ∀ n, Integrable (m n) μ := fun n ↦
    hqint.mono' (hmmeas n) (hm_bound n)
  have hl1eq : ∀ n,
      (∫ x, |p n x - q x| ∂μ) = 2 - 2 * ∫ x, m n x ∂μ := by
    intro n
    calc
      (∫ x, |p n x - q x| ∂μ) =
          ∫ x, p n x + q x - 2 * m n x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        rcases le_total (p n x) (q x) with hle | hle
        · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
          simp only [m, min_eq_left hle]
          ring
        · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
          simp only [m, min_eq_right hle]
          ring
      _ = (∫ x, p n x + q x ∂μ) - ∫ x, 2 * m n x ∂μ := by
        exact integral_sub ((hpint n).add hqint) ((hmint n).const_mul 2)
      _ = (∫ x, p n x ∂μ) + (∫ x, q x ∂μ) -
          2 * ∫ x, m n x ∂μ := by
        rw [integral_add (hpint n) hqint, integral_const_mul]
      _ = 2 - 2 * ∫ x, m n x ∂μ := by rw [hpone n, hqone]; ring
  rw [show (fun n ↦ ∫ x, |p n x - q x| ∂μ) =
      fun n ↦ 2 - 2 * ∫ x, m n x ∂μ by funext n; exact hl1eq n]
  simpa using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2)).sub
      (hm_integral.const_mul 2)

/-- A squared triangle bound requiring only integrability of the three
square-root differences.  It is sufficient for the finite-net transfer and
avoids introducing an additional square-root-distance wrapper. -/
theorem hellingerSq_triangle_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q r : Ω → ℝ)
    (hpq : Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ)
    (hqr : Integrable (fun x ↦ (Real.sqrt (q x) - Real.sqrt (r x)) ^ 2) μ)
    (hpr : Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (r x)) ^ 2) μ) :
    hellingerSq μ p r ≤ 2 * hellingerSq μ p q + 2 * hellingerSq μ q r := by
  unfold hellingerSq
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hpq.const_mul 2) (hqr.const_mul 2)]
  apply integral_mono_ae hpr ((hpq.const_mul 2).add (hqr.const_mul 2))
  exact Filter.Eventually.of_forall fun x ↦ by
    change (Real.sqrt (p x) - Real.sqrt (r x)) ^ 2 ≤
      2 * (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 +
        2 * (Real.sqrt (q x) - Real.sqrt (r x)) ^ 2
    nlinarith [sq_nonneg ((Real.sqrt (p x) - Real.sqrt (q x)) -
      (Real.sqrt (q x) - Real.sqrt (r x)))]

/-- Numerical form of `hellingerSq_triangle_bound`. -/
theorem hellingerSq_le_two_sq_add_two_sq_of_net
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q r : Ω → ℝ) (δ t : ℝ)
    (hpq : Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ)
    (hqr : Integrable (fun x ↦ (Real.sqrt (q x) - Real.sqrt (r x)) ^ 2) μ)
    (hpr : Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (r x)) ^ 2) μ)
    (hnet : hellingerSq μ p q ≤ δ ^ 2)
    (htest : hellingerSq μ q r ≤ t ^ 2) :
    hellingerSq μ p r ≤ 2 * δ ^ 2 + 2 * t ^ 2 := by
  exact (hellingerSq_triangle_bound μ p q r hpq hqr hpr).trans
    (add_le_add (mul_le_mul_of_nonneg_left hnet (by norm_num))
      (mul_le_mul_of_nonneg_left htest (by norm_num)))

theorem hellingerSq_eq_integrals {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ) :
    hellingerSq μ p q =
      (∫ x, p x ∂μ) + (∫ x, q x ∂μ) - 2 * hellingerAffinity μ p q := by
  rw [hellingerSq, hellingerAffinity]
  calc
    (∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ) =
        ∫ x, (p x + q x - 2 * Real.sqrt (p x * q x)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ sqrt_sub_sq (hp x) (hq x)
    _ = (∫ x, p x ∂μ) + (∫ x, q x ∂μ) -
        2 * ∫ x, Real.sqrt (p x * q x) ∂μ := by
      rw [integral_sub (f := fun x ↦ p x + q x)
          (g := fun x ↦ 2 * Real.sqrt (p x * q x))
          (hpint.add hqint) (haint.const_mul 2),
        integral_add hpint hqint, integral_const_mul]

/-- For probability densities, affinity equals `1 - H²/2`. -/
theorem affinity_eq_one_sub_half_hellingerSq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ)
    (hp_one : ∫ x, p x ∂μ = 1) (hq_one : ∫ x, q x ∂μ = 1) :
    hellingerAffinity μ p q = 1 - hellingerSq μ p q / 2 := by
  have h := hellingerSq_eq_integrals μ p q hp hq hpint hqint haint
  rw [hp_one, hq_one] at h
  linarith

theorem hellingerAffinity_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ) : 0 ≤ hellingerAffinity μ p q := by
  apply integral_nonneg
  intro x
  exact Real.sqrt_nonneg _

/-- Under the paper's convention, squared Hellinger distance between densities is at most two. -/
theorem hellingerSq_le_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ)
    (hp_one : ∫ x, p x ∂μ = 1) (hq_one : ∫ x, q x ∂μ = 1) :
    hellingerSq μ p q ≤ 2 := by
  have ha := hellingerAffinity_nonneg μ p q
  rw [affinity_eq_one_sub_half_hellingerSq μ p q hp hq hpint hqint haint hp_one hq_one] at ha
  linarith

/-- Pointwise square-root likelihood-ratio identity. -/
theorem exp_half_log_ratio_eq_sqrt {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.exp (Real.log (p / q) / 2) = Real.sqrt (p / q) := by
  have hpq : 0 < p / q := div_pos hp hq
  symm
  apply (Real.sqrt_eq_iff_mul_self_eq hpq.le (Real.exp_pos _).le).2
  rw [← Real.exp_add, ← two_mul, show 2 * (Real.log (p / q) / 2) =
      Real.log (p / q) by ring, Real.exp_log hpq]

/-- Multiplying the square-root likelihood ratio by the reference density gives affinity. -/
theorem density_mul_exp_half_log_ratio {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    q * Real.exp (Real.log (p / q) / 2) = Real.sqrt (p * q) := by
  rw [exp_half_log_ratio_eq_sqrt hp hq]
  symm
  apply (Real.sqrt_eq_iff_mul_self_eq (mul_pos hp hq).le
    (mul_nonneg hq.le (Real.sqrt_nonneg _))).2
  have hr2 : Real.sqrt (p / q) * Real.sqrt (p / q) = p / q := by
    rw [← pow_two, Real.sq_sqrt (div_pos hp hq).le]
  calc
    p * q = q * q * (p / q) := by field_simp [hq.ne']
    _ = q * q * (Real.sqrt (p / q) * Real.sqrt (p / q)) :=
      congrArg (fun z ↦ q * q * z) hr2.symm
    _ = (q * Real.sqrt (p / q)) * (q * Real.sqrt (p / q)) := by ring

/-- Exponentiating half of a finite log-likelihood ratio turns its sum into
the product of the coordinatewise square-root likelihood ratios. -/
theorem exp_half_sum_log_ratio_eq_prod {Ω : Type*} {n : ℕ}
    (p q : Ω → ℝ) (x : Fin n → Ω) :
    Real.exp ((∑ i, Real.log (p (x i) / q (x i))) / 2) =
      ∏ i, Real.exp (Real.log (p (x i) / q (x i)) / 2) := by
  rw [div_eq_mul_inv, Finset.sum_mul, Real.exp_sum]
  simp only [div_eq_mul_inv]

/-- Independence factors the square-root likelihood-ratio expectation into a
power of its one-observation expectation. -/
theorem product_exp_half_log_ratio_integral {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (ν : Measure Ω) [SigmaFinite ν] (p q : Ω → ℝ) :
    ∫ x : Fin n → Ω,
        Real.exp ((∑ i, Real.log (p (x i) / q (x i))) / 2)
        ∂Measure.pi (fun _ : Fin n ↦ ν) =
      (∫ y, Real.exp (Real.log (p y / q y) / 2) ∂ν) ^ n := by
  calc
    _ = ∫ x : Fin n → Ω,
        ∏ i, Real.exp (Real.log (p (x i) / q (x i)) / 2)
        ∂Measure.pi (fun _ : Fin n ↦ ν) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦
            exp_half_sum_log_ratio_eq_prod p q x
    _ = _ := by
      simpa using
        (integral_fintype_prod_eq_pow (ι := Fin n)
          (μ := ν) (fun y ↦ Real.exp (Real.log (p y / q y) / 2)))

/-- Under the probability law with density `q`, the one-observation
square-root likelihood-ratio expectation is exactly the Hellinger affinity. -/
theorem integral_exp_half_log_ratio_withDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    ∫ x, Real.exp (Real.log (p x / q x) / 2)
        ∂μ.withDensity (fun x ↦ ENNReal.ofReal (q x)) =
      hellingerAffinity μ p q := by
  rw [integral_withDensity_eq_integral_toReal_smul]
  · change (∫ x, (ENNReal.ofReal (q x)).toReal *
        Real.exp (Real.log (p x / q x) / 2) ∂μ) = _
    simp_rw [ENNReal.toReal_ofReal (hq _).le,
      density_mul_exp_half_log_ratio (hp _) (hq _)]
    rfl
  · exact hqmeas.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top

/-- Integrability form of the same change-of-density calculation. -/
theorem integrable_exp_half_log_ratio_withDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ) :
    Integrable (fun x ↦ Real.exp (Real.log (p x / q x) / 2))
      (μ.withDensity fun x ↦ ENNReal.ofReal (q x)) := by
  rw [integrable_withDensity_iff hqmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  apply haint.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    dsimp only
    rw [ENNReal.toReal_ofReal (hq x).le]
    calc
      Real.sqrt (p x * q x) =
          q x * Real.exp (Real.log (p x / q x) / 2) :=
        (density_mul_exp_half_log_ratio (hp x) (hq x)).symm
      _ = Real.exp (Real.log (p x / q x) / 2) * q x := mul_comm _ _

/-- The exact product likelihood-ratio identity used in the finite-net test. -/
theorem product_sqrt_likelihood_ratio_identity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    [SigmaFinite (μ.withDensity fun x ↦ ENNReal.ofReal (q x))] :
    ∫ x : Fin n → Ω,
        Real.exp ((∑ i, Real.log (p (x i) / q (x i))) / 2)
        ∂Measure.pi (fun _ : Fin n ↦
          μ.withDensity (fun y ↦ ENNReal.ofReal (q y))) =
      (hellingerAffinity μ p q) ^ n := by
  rw [product_exp_half_log_ratio_integral]
  rw [integral_exp_half_log_ratio_withDensity μ p q hqmeas hp hq]

/-- Probability-density specialization in exactly the form displayed in the
manuscript: the product expectation is `(1 - H²/2)ⁿ`. -/
theorem product_sqrt_likelihood_ratio_eq_one_sub_half_hellingerSq
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ)
    (hp_one : ∫ x, p x ∂μ = 1) (hq_one : ∫ x, q x ∂μ = 1)
    [SigmaFinite (μ.withDensity fun x ↦ ENNReal.ofReal (q x))] :
    ∫ x : Fin n → Ω,
        Real.exp ((∑ i, Real.log (p (x i) / q (x i))) / 2)
        ∂Measure.pi (fun _ : Fin n ↦
          μ.withDensity (fun y ↦ ENNReal.ofReal (q y))) =
      (1 - hellingerSq μ p q / 2) ^ n := by
  rw [product_sqrt_likelihood_ratio_identity μ p q hqmeas hp hq]
  rw [affinity_eq_one_sub_half_hellingerSq μ p q
    (fun x ↦ (hp x).le) (fun x ↦ (hq x).le) hpint hqint haint hp_one hq_one]

end ReweightedNPMLE
