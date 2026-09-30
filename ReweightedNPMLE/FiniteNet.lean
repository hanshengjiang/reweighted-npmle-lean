import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import ReweightedNPMLE.Hellinger
import Mathlib.Tactic

/-!
# Finite-net likelihood testing

This file isolates the probability-theoretic union-bound step in the proof of
the paper's uniform near-MLE theorem.  The analytic construction of a
Gaussian-mixture net and the fixed-density likelihood-ratio estimate enter as
explicit hypotheses; the passage from those pointwise estimates to one event
which controls every candidate is proved here.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ReweightedNPMLE

/-- The elementary affinity-power bound used in the fixed-net test. -/
theorem affinity_pow_le_exp_neg {h : ℝ} (hh₀ : 0 ≤ h) (hh₂ : h ≤ 2) (n : ℕ) :
    (1 - h / 2) ^ n ≤ Real.exp (-(n : ℝ) * h / 2) := by
  have hbase : 0 ≤ 1 - h / 2 := by linarith
  calc
    (1 - h / 2) ^ n ≤ (Real.exp (-h / 2)) ^ n := by
      convert pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg (h / 2)) n using 1 <;>
        ring
    _ = Real.exp (-(n : ℝ) * h / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/--
The fixed-density likelihood-ratio test in real-valued probability form.
The expectation premise is exactly the square-root likelihood-ratio identity
followed by `affinity_pow_le_exp_neg`.
-/
theorem fixed_likelihood_ratio_test_bound_real
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (logLR : Ω → ℝ) (n : ℕ) (h : ℝ)
    (hint : Integrable (fun ω ↦ Real.exp (logLR ω / 2)) μ)
    (hexpect : ∫ ω, Real.exp (logLR ω / 2) ∂μ ≤
      Real.exp (-(n : ℝ) * h / 2)) :
    μ.real {ω | -2 ≤ logLR ω} ≤ Real.exp (1 - (n : ℝ) * h / 2) := by
  have hset : {ω | Real.exp (-1) ≤ Real.exp (logLR ω / 2)} =
      {ω | -2 ≤ logLR ω} := by
    ext ω
    simp only [mem_setOf_eq]
    rw [Real.exp_le_exp]
    constructor <;> intro hω <;> linarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω ↦ Real.exp (logLR ω / 2))
    (Filter.Eventually.of_forall fun ω ↦ (Real.exp_pos _).le) hint (Real.exp (-1))
  rw [hset] at hmarkov
  have hprod : Real.exp (-1) * μ.real {ω | -2 ≤ logLR ω} ≤
      Real.exp (-(n : ℝ) * h / 2) := hmarkov.trans hexpect
  calc
    μ.real {ω | -2 ≤ logLR ω} =
        Real.exp 1 * (Real.exp (-1) * μ.real {ω | -2 ≤ logLR ω}) := by
          rw [← mul_assoc, ← Real.exp_add]
          norm_num
    _ ≤ Real.exp 1 * Real.exp (-(n : ℝ) * h / 2) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (1 - (n : ℝ) * h / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/--
The fixed-density likelihood-ratio test with all analytic premises discharged.
Samples are drawn independently from the probability density `q` with
respect to `μ`.  The right-hand side is the exponential Hellinger bound used
before taking the finite-net union bound.
-/
theorem fixed_density_likelihood_ratio_test_bound
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ)
    (hp_one : ∫ x, p x ∂μ = 1) (hq_one : ∫ x, q x ∂μ = 1) :
    (Measure.pi (fun _ : Fin n ↦
      μ.withDensity (fun y ↦ ENNReal.ofReal (q y)))).real
        {x | -2 ≤ ∑ i, Real.log (p (x i) / q (x i))} ≤
      Real.exp (1 - (n : ℝ) * hellingerSq μ p q / 2) := by
  let ν : Measure Ω := μ.withDensity fun y ↦ ENNReal.ofReal (q y)
  letI : IsProbabilityMeasure ν := IsProbabilityMeasure.mk (by
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hqint
        (Filter.Eventually.of_forall fun x ↦ (hq x).le), hq_one]
    norm_num)
  let logLR : (Fin n → Ω) → ℝ :=
    fun x ↦ ∑ i, Real.log (p (x i) / q (x i))
  have hbase : Integrable
      (fun y ↦ Real.exp (Real.log (p y / q y) / 2)) ν := by
    exact integrable_exp_half_log_ratio_withDensity μ p q hqmeas hp hq haint
  have hprod : Integrable
      (fun x : Fin n → Ω ↦
        ∏ i, Real.exp (Real.log (p (x i) / q (x i)) / 2))
      (Measure.pi fun _ : Fin n ↦ ν) :=
    Integrable.fintype_prod (fun _ ↦ hbase)
  have hint : Integrable (fun x ↦ Real.exp (logLR x / 2))
      (Measure.pi fun _ : Fin n ↦ ν) := by
    apply hprod.congr
    exact Filter.Eventually.of_forall fun x ↦
      (exp_half_sum_log_ratio_eq_prod p q x).symm
  have hh₀ : 0 ≤ hellingerSq μ p q := hellingerSq_nonneg μ p q
  have hh₂ : hellingerSq μ p q ≤ 2 :=
    hellingerSq_le_two μ p q (fun x ↦ (hp x).le) (fun x ↦ (hq x).le)
      hpint hqint haint hp_one hq_one
  have hexpect :
      ∫ x, Real.exp (logLR x / 2) ∂Measure.pi (fun _ : Fin n ↦ ν) ≤
        Real.exp (-(n : ℝ) * hellingerSq μ p q / 2) := by
    calc
      _ = (1 - hellingerSq μ p q / 2) ^ n := by
        exact product_sqrt_likelihood_ratio_eq_one_sub_half_hellingerSq
          μ p q hqmeas hp hq hpint hqint haint hp_one hq_one
      _ ≤ _ := affinity_pow_le_exp_neg hh₀ hh₂ n
  exact fixed_likelihood_ratio_test_bound_real
    (Measure.pi fun _ : Fin n ↦ ν) logLR n (hellingerSq μ p q) hint hexpect

/-- A finite union of testing events has at most the sum of their bounds. -/
theorem measure_finset_test_union_le {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Finset ι) (test : ι → Set Ω) (bound : ι → ℝ≥0∞)
    (htest : ∀ p ∈ N, μ (test p) ≤ bound p) :
    μ (⋃ p ∈ N, test p) ≤ ∑ p ∈ N, bound p := by
  exact (measure_biUnion_finset_le N test).trans
    (Finset.sum_le_sum fun p hp ↦ htest p hp)

/-- Constant-bound specialization of `measure_finset_test_union_le`. -/
theorem measure_finset_test_union_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Finset ι) (test : ι → Set Ω) (b : ℝ≥0∞)
    (htest : ∀ p ∈ N, μ (test p) ≤ b) :
    μ (⋃ p ∈ N, test p) ≤ N.card * b := by
  calc
    μ (⋃ p ∈ N, test p) ≤ ∑ p ∈ N, b :=
      measure_finset_test_union_le μ N test (fun _ ↦ b) htest
    _ = N.card * b := by simp

/-- Real-valued version of the finite-union bound, convenient when the
pointwise likelihood-ratio estimates are stated using `Measure.real`. -/
theorem measureReal_finset_test_union_le_card_mul
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Finset ι) (test : ι → Set Ω) (b : ℝ)
    (hb : 0 ≤ b) (htest : ∀ p ∈ N, μ.real (test p) ≤ b) :
    μ.real (⋃ p ∈ N, test p) ≤ N.card * b := by
  classical
  induction N using Finset.induction_on with
  | empty => simp
  | @insert p N hp ih =>
      rw [Finset.set_biUnion_insert]
      calc
        μ.real (test p ∪ ⋃ x ∈ N, test x) ≤
            μ.real (test p) + μ.real (⋃ x ∈ N, test x) :=
          measureReal_union_le _ _
        _ ≤ b + N.card * b := add_le_add (htest p (by simp))
          (ih (fun x hx ↦ htest x (by simp [hx])))
        _ = (insert p N).card * b := by
          rw [Finset.card_insert_of_notMem hp]
          push_cast
          ring

/-- Concrete finite-net likelihood test.  Every net density separated by at
least `t²` in squared Hellinger distance has its `logLR ≥ -2` event bounded
by the same exponential; a finite union costs exactly the net cardinality. -/
theorem finite_density_net_likelihood_test_bound
    {Ω ι : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (N : Finset ι) (p : ι → Ω → ℝ) (q : Ω → ℝ)
    (t : ℝ)
    (hqmeas : Measurable q) (hq : ∀ x, 0 < q x)
    (hqint : Integrable q μ) (hq_one : ∫ x, q x ∂μ = 1)
    (hp : ∀ r ∈ N, ∀ x, 0 < p r x)
    (hpint : ∀ r ∈ N, Integrable (p r) μ)
    (haint : ∀ r ∈ N, Integrable (fun x ↦ Real.sqrt (p r x * q x)) μ)
    (hp_one : ∀ r ∈ N, ∫ x, p r x ∂μ = 1)
    (hsep : ∀ r ∈ N, t ^ 2 ≤ hellingerSq μ (p r) q) :
    let ν := Measure.pi (fun _ : Fin n ↦
      μ.withDensity (fun y ↦ ENNReal.ofReal (q y)))
    ν.real (⋃ r ∈ N,
        {x | -2 ≤ ∑ i, Real.log (p r (x i) / q (x i))}) ≤
      N.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
  dsimp only
  apply measureReal_finset_test_union_le_card_mul
  · positivity
  · intro r hr
    calc
      (Measure.pi (fun _ : Fin n ↦
        μ.withDensity (fun y ↦ ENNReal.ofReal (q y)))).real
          {x | -2 ≤ ∑ i, Real.log (p r (x i) / q (x i))} ≤
          Real.exp (1 - (n : ℝ) * hellingerSq μ (p r) q / 2) :=
        fixed_density_likelihood_ratio_test_bound μ (p r) q hqmeas
          (hp r hr) hq (hpint r hr) hqint (haint r hr) (hp_one r hr) hq_one
      _ ≤ Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [hsep r hr]

/-- Deterministic likelihood-transfer calculation from the paper: a candidate
within one log-likelihood unit of the truth and uniformly `δ`-approximated on
all sample points by a net density gives a net log-likelihood ratio at least
`-2`, provided `nδ ≤ 1`. -/
theorem net_logLikelihoodRatio_ge_neg_two
    {Ω : Type*} {n : ℕ} (p f q : Ω → ℝ) (x : Fin n → Ω) (δ : ℝ)
    (hp : ∀ i, 0 < p (x i)) (hq : ∀ i, 0 < q (x i))
    (hnear : (∑ i, Real.log (q (x i))) - 1 ≤
      ∑ i, Real.log (f (x i)))
    (happrox : ∀ i,
      |Real.log (p (x i)) - Real.log (f (x i))| ≤ δ)
    (hnδ : (n : ℝ) * δ ≤ 1) :
    -2 ≤ ∑ i, Real.log (p (x i) / q (x i)) := by
  have hnet : (∑ i, Real.log (f (x i))) - (n : ℝ) * δ ≤
      ∑ i, Real.log (p (x i)) := by
    calc
      (∑ i, Real.log (f (x i))) - (n : ℝ) * δ =
          ∑ i, (Real.log (f (x i)) - δ) := by
        rw [Finset.sum_sub_distrib]
        simp
      _ ≤ ∑ i, Real.log (p (x i)) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := (abs_le.mp (happrox i)).1
        linarith
  rw [show (∑ i, Real.log (p (x i) / q (x i))) =
      (∑ i, Real.log (p (x i))) - ∑ i, Real.log (q (x i)) by
    simp_rw [Real.log_div (hp _).ne' (hq _).ne']
    exact Finset.sum_sub_distrib (s := Finset.univ)
      (fun i ↦ Real.log (p (x i))) (fun i ↦ Real.log (q (x i)))]
  linarith

/-- Deterministic completion of the near-MLE transfer for one candidate.  A
simultaneous testing event only has to control the selected net density; the
squared Hellinger triangle bound then controls the original candidate. -/
theorem nearMLE_hellingerSq_transfer_of_net
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (p f q : Ω → ℝ) (x : Fin n → Ω) (δ t : ℝ)
    (hp : ∀ i, 0 < p (x i)) (hq : ∀ i, 0 < q (x i))
    (hnear : (∑ i, Real.log (q (x i))) - 1 ≤
      ∑ i, Real.log (f (x i)))
    (hlog : ∀ i,
      |Real.log (p (x i)) - Real.log (f (x i))| ≤ δ)
    (hnδ : (n : ℝ) * δ ≤ 1)
    (hfp : Integrable (fun y ↦
      (Real.sqrt (f y) - Real.sqrt (p y)) ^ 2) μ)
    (hpq : Integrable (fun y ↦
      (Real.sqrt (p y) - Real.sqrt (q y)) ^ 2) μ)
    (hfq : Integrable (fun y ↦
      (Real.sqrt (f y) - Real.sqrt (q y)) ^ 2) μ)
    (hnet : hellingerSq μ f p ≤ δ ^ 2)
    (htest : -2 ≤ ∑ i, Real.log (p (x i) / q (x i)) →
      hellingerSq μ p q ≤ t ^ 2) :
    hellingerSq μ f q ≤ 2 * δ ^ 2 + 2 * t ^ 2 := by
  have hlr : -2 ≤ ∑ i, Real.log (p (x i) / q (x i)) :=
    net_logLikelihoodRatio_ge_neg_two p f q x δ hp hq hnear hlog hnδ
  exact hellingerSq_le_two_sq_add_two_sq_of_net
    μ f p q δ t hfp hpq hfq hnet (htest hlr)

/--
Abstract simultaneous near-MLE transfer.

`badCandidate` is the event that at least one near-maximal candidate violates
the desired Hellinger conclusion.  On the radius event, the deterministic net
construction maps every such violation to one of the fixed testing events.
The theorem performs the remaining event inclusion and finite union bound.
-/
theorem uniform_nearMLE_bad_event_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Finset ι)
    (badCandidate radiusBad : Set Ω) (test : ι → Set Ω)
    (radiusBound testBound : ℝ≥0∞)
    (htransfer : badCandidate ⊆ radiusBad ∪ ⋃ p ∈ N, test p)
    (hradius : μ radiusBad ≤ radiusBound)
    (htest : ∀ p ∈ N, μ (test p) ≤ testBound) :
    μ badCandidate ≤ radiusBound + N.card * testBound := by
  calc
    μ badCandidate ≤ μ (radiusBad ∪ ⋃ p ∈ N, test p) :=
      measure_mono htransfer
    _ ≤ μ radiusBad + μ (⋃ p ∈ N, test p) := measure_union_le _ _
    _ ≤ radiusBound + N.card * testBound := add_le_add hradius
      (measure_finset_test_union_le_card_mul μ N test testBound htest)

/--
The exact deterministic selection implication used by the likelihood net:
if every near candidate on the radius event has an associated net point whose
test statistic crosses the threshold, then a bad candidate lies in the
corresponding finite union.
-/
theorem candidate_event_subset_test_union {Ω ι Γ : Type*}
    (N : Finset ι) (radius : Ω → Prop) (near bad : Ω → Γ → Prop)
    (choose : Ω → Γ → ι) (test : ι → Ω → Prop)
    (hchoose : ∀ ω G, radius ω → near ω G → bad ω G →
      choose ω G ∈ N ∧ test (choose ω G) ω) :
    {ω | ∃ G : Γ, radius ω ∧ near ω G ∧ bad ω G} ⊆
      ⋃ p ∈ N, {ω | test p ω} := by
  intro ω hω
  rcases hω with ⟨G, hr, hn, hb⟩
  obtain ⟨hpN, hp⟩ := hchoose ω G hr hn hb
  simp only [mem_iUnion]
  exact ⟨choose ω G, ⟨hpN, hp⟩⟩

/-- Concrete uniform near-MLE theorem for an arbitrary finite density net.
On a supplied radius event, every candidate has a selected net density with
local log error `δ` and global squared-Hellinger error `globalSq`.  The bad
near-MLE event is then controlled by the radius failure probability plus the
finite square-root likelihood-ratio union bound. -/
theorem uniform_nearMLE_hellinger_bad_event_bound
    {Ω ι Γ : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (N : Finset ι) (p : ι → Ω → ℝ)
    (q : Ω → ℝ) (f : Γ → Ω → ℝ) (select : Γ → ι)
    (radius : Set (Fin n → Ω)) (δ globalSq t radiusBound : ℝ)
    (hqmeas : Measurable q) (hq : ∀ x, 0 < q x)
    (hqint : Integrable q μ) (hq_one : ∫ x, q x ∂μ = 1)
    (hp : ∀ r ∈ N, ∀ x, 0 < p r x)
    (hpint : ∀ r ∈ N, Integrable (p r) μ)
    (haint : ∀ r ∈ N,
      Integrable (fun x ↦ Real.sqrt (p r x * q x)) μ)
    (hp_one : ∀ r ∈ N, ∫ x, p r x ∂μ = 1)
    (hf : ∀ G x, 0 < f G x) (hfint : ∀ G, Integrable (f G) μ)
    (hselect : ∀ G, select G ∈ N)
    (hglobal : ∀ G, hellingerSq μ (f G) (p (select G)) ≤ globalSq)
    (hlocal : ∀ x ∈ radius, ∀ G i,
      |Real.log (p (select G) (x i)) - Real.log (f G (x i))| ≤ δ)
    (hnδ : (n : ℝ) * δ ≤ 1)
    (hradius :
      (Measure.pi (fun _ : Fin n ↦
        μ.withDensity (fun y ↦ ENNReal.ofReal (q y)))).real radiusᶜ ≤
          radiusBound) :
    (Measure.pi (fun _ : Fin n ↦
      μ.withDensity (fun y ↦ ENNReal.ofReal (q y)))).real
        {x | ∃ G,
          (∑ i, Real.log (q (x i))) - 1 ≤ ∑ i, Real.log (f G (x i)) ∧
          2 * globalSq + 2 * t ^ 2 < hellingerSq μ (f G) q} ≤
      radiusBound + N.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
  classical
  let ν₀ : Measure Ω := μ.withDensity (fun y ↦ ENNReal.ofReal (q y))
  letI : IsProbabilityMeasure ν₀ := IsProbabilityMeasure.mk (by
    dsimp [ν₀]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hqint
        (Filter.Eventually.of_forall fun x ↦ (hq x).le), hq_one]
    norm_num)
  let ν : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n ↦ ν₀)
  letI : IsProbabilityMeasure ν := Measure.pi.instIsProbabilityMeasure _
  let Nfar := N.filter fun r ↦ t ^ 2 < hellingerSq μ (p r) q
  let test : ι → Set (Fin n → Ω) := fun r ↦
    {x | -2 ≤ ∑ i, Real.log (p r (x i) / q (x i))}
  have htestBound :
      ν.real (⋃ r ∈ Nfar, test r) ≤
        Nfar.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
    exact finite_density_net_likelihood_test_bound μ Nfar p q t hqmeas hq
      hqint hq_one
      (fun r hr ↦ hp r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ hpint r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ haint r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ hp_one r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ (Finset.mem_filter.mp hr).2.le)
  have hsubset :
      {x | ∃ G,
        (∑ i, Real.log (q (x i))) - 1 ≤ ∑ i, Real.log (f G (x i)) ∧
        2 * globalSq + 2 * t ^ 2 < hellingerSq μ (f G) q} ⊆
        radiusᶜ ∪ ⋃ r ∈ Nfar, test r := by
    rintro x ⟨G, hnear, hbad⟩
    by_cases hx : x ∈ radius
    · right
      have hrN : select G ∈ N := hselect G
      have hfar : t ^ 2 < hellingerSq μ (p (select G)) q := by
        by_contra hnot
        have hpqle : hellingerSq μ (p (select G)) q ≤ t ^ 2 := le_of_not_gt hnot
        have hfp : Integrable (fun y ↦
            (Real.sqrt (f G y) - Real.sqrt (p (select G) y)) ^ 2) μ :=
          hellingerIntegrand_integrable_of_integrable μ (f G) (p (select G))
            (hfint G).aestronglyMeasurable (hpint _ hrN).aestronglyMeasurable
            (Filter.Eventually.of_forall fun y ↦ (hf G y).le)
            (Filter.Eventually.of_forall fun y ↦ (hp _ hrN y).le)
            (hfint G) (hpint _ hrN)
        have hpq : Integrable (fun y ↦
            (Real.sqrt (p (select G) y) - Real.sqrt (q y)) ^ 2) μ :=
          hellingerIntegrand_integrable_of_integrable μ (p (select G)) q
            (hpint _ hrN).aestronglyMeasurable hqint.aestronglyMeasurable
            (Filter.Eventually.of_forall fun y ↦ (hp _ hrN y).le)
            (Filter.Eventually.of_forall fun y ↦ (hq y).le)
            (hpint _ hrN) hqint
        have hfq : Integrable (fun y ↦
            (Real.sqrt (f G y) - Real.sqrt (q y)) ^ 2) μ :=
          hellingerIntegrand_integrable_of_integrable μ (f G) q
            (hfint G).aestronglyMeasurable hqint.aestronglyMeasurable
            (Filter.Eventually.of_forall fun y ↦ (hf G y).le)
            (Filter.Eventually.of_forall fun y ↦ (hq y).le)
            (hfint G) hqint
        have htri := hellingerSq_triangle_bound
          μ (f G) (p (select G)) q hfp hpq hfq
        have htri' : hellingerSq μ (f G) q ≤
            2 * globalSq + 2 * t ^ 2 :=
          htri.trans (add_le_add
            (mul_le_mul_of_nonneg_left (hglobal G) (by norm_num))
            (mul_le_mul_of_nonneg_left hpqle (by norm_num)))
        exact (not_lt_of_ge htri') hbad
      have hlr := net_logLikelihoodRatio_ge_neg_two
        (p (select G)) (f G) q x δ
        (fun i ↦ hp _ hrN (x i)) (fun i ↦ hq (x i)) hnear
        (hlocal x hx G) hnδ
      simp only [Set.mem_iUnion]
      exact ⟨select G, ⟨Finset.mem_filter.mpr ⟨hrN, hfar⟩, hlr⟩⟩
    · left
      exact hx
  calc
    ν.real {x | ∃ G,
        (∑ i, Real.log (q (x i))) - 1 ≤ ∑ i, Real.log (f G (x i)) ∧
        2 * globalSq + 2 * t ^ 2 < hellingerSq μ (f G) q} ≤
        ν.real (radiusᶜ ∪ ⋃ r ∈ Nfar, test r) :=
      measureReal_mono hsubset (by finiteness)
    _ ≤ ν.real radiusᶜ + ν.real (⋃ r ∈ Nfar, test r) :=
      measureReal_union_le _ _
    _ ≤ radiusBound +
        Nfar.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) :=
      add_le_add hradius htestBound
    _ ≤ radiusBound + N.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
      have hcard : (Nfar.card : ℝ) ≤ N.card := by
        exact_mod_cast Finset.card_filter_le N _
      have hmul :
          (Nfar.card : ℝ) * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) ≤
            (N.card : ℝ) * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      linarith

end ReweightedNPMLE
