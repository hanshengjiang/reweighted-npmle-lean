import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

/-!
# Extreme finite mixture fibers

This file isolates the finite-dimensional core of the paper's optimizer-fiber
lemma.  A probability vector represents a finite mixing law.  If the
dictionary vectors indexed by its nonzero masses are linearly independent,
then that representation is an extreme point of the fiber of all probability
vectors with the same fitted value.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE

/-- The probability simplex on a finite dictionary. -/
def finiteSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

theorem finiteSimplex_eq_stdSimplex (m : ℕ) :
    finiteSimplex m = stdSimplex ℝ (Fin m) := rfl

theorem isCompact_finiteSimplex (m : ℕ) : IsCompact (finiteSimplex m) := by
  rw [finiteSimplex_eq_stdSimplex]
  exact isCompact_stdSimplex ℝ (Fin m)

theorem convex_finiteSimplex (m : ℕ) : Convex ℝ (finiteSimplex m) := by
  rw [finiteSimplex_eq_stdSimplex]
  exact convex_stdSimplex ℝ (Fin m)

/-- Fitted value of a finite mixture. -/
def finiteMixtureValue {m : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (A : Fin m → E) (p : Fin m → ℝ) : E :=
  ∑ i, p i • A i

theorem continuous_finiteMixtureValue
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin m → E) : Continuous (finiteMixtureValue A) := by
  unfold finiteMixtureValue
  fun_prop

/-- Adding the total-mass coordinate turns affine independence of a finite
dictionary into ordinary linear independence. -/
def augmentedDictionary {m : ℕ} {E : Type*} (A : Fin m → E) : Fin m → ℝ × E :=
  fun i ↦ (1, A i)

/-- Fiber of all finite mixing weights representing the fitted value `v`. -/
def finiteMixtureFiber {m : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (A : Fin m → E) (v : E) :
    Set (Fin m → ℝ) :=
  {p | p ∈ finiteSimplex m ∧ finiteMixtureValue A p = v}

theorem isCompact_finiteMixtureFiber
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin m → E) (v : E) : IsCompact (finiteMixtureFiber A v) := by
  have hclosed : IsClosed {p | finiteMixtureValue A p = v} :=
    isClosed_eq (continuous_finiteMixtureValue A) continuous_const
  exact (isCompact_finiteSimplex m).inter_right hclosed

theorem convex_finiteMixtureFiber
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) : Convex ℝ (finiteMixtureFiber A v) := by
  intro p hp q hq a b ha hb hab
  refine ⟨convex_finiteSimplex m hp.1 hq.1 ha hb hab, ?_⟩
  calc
    finiteMixtureValue A (a • p + b • q) =
        a • finiteMixtureValue A p + b • finiteMixtureValue A q := by
      simp only [finiteMixtureValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    _ = a • v + b • v := by rw [hp.2, hq.2]
    _ = v := by rw [← add_smul, hab, one_smul]

/-- Indices carrying nonzero mass. -/
noncomputable def coefficientSupport {m : ℕ} (p : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ p i ≠ 0

@[simp] theorem mem_coefficientSupport {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    i ∈ coefficientSupport p ↔ p i ≠ 0 := by
  simp [coefficientSupport]

theorem not_mem_coefficientSupport_iff {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    i ∉ coefficientSupport p ↔ p i = 0 := by
  simp [coefficientSupport]

/-- Linear independence on the positive support makes a finite mixing law an
extreme point of its fitted-value fiber. -/
theorem finiteMixtureFiber_extreme_of_linearIndepOn
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ)
    (hp : p ∈ finiteMixtureFiber A v)
    (hlin : LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m))) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ := by
  classical
  rw [mem_extremePoints_iff_left]
  refine ⟨hp, ?_⟩
  intro q hq r hr hpqr
  rw [openSegment_eq_image] at hpqr
  rcases hpqr with ⟨t, ht, hrepr⟩
  rcases ht with ⟨htzero, htone⟩
  let S := coefficientSupport p
  have hqnonneg (i : Fin m) : 0 ≤ q i := hq.1.1 i
  have hrnonneg (i : Fin m) : 0 ≤ r i := hr.1.1 i
  have hqzero (i : Fin m) (hi : i ∉ S) : q i = 0 := by
    have hpzero : p i = 0 :=
      (not_mem_coefficientSupport_iff p i).mp hi
    have hcoord := congrFun hrepr i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcoord
    rw [hpzero] at hcoord
    have hleft : 0 ≤ (1 - t) * q i :=
      mul_nonneg (sub_nonneg.mpr htone.le) (hqnonneg i)
    have hright : 0 ≤ t * r i := mul_nonneg htzero.le (hrnonneg i)
    have hleftzero : (1 - t) * q i = 0 := by linarith
    rcases mul_eq_zero.mp hleftzero with ht | hq
    · linarith
    · exact hq
  have hpzero (i : Fin m) (hi : i ∉ S) : p i = 0 :=
    (not_mem_coefficientSupport_iff p i).mp hi
  have hall : ∑ i : Fin m, (q i - p i) • A i = 0 := by
    calc
      (∑ i : Fin m, (q i - p i) • A i) =
          finiteMixtureValue A q - finiteMixtureValue A p := by
        simp [finiteMixtureValue, sub_smul, Finset.sum_sub_distrib]
      _ = 0 := by rw [hq.2, hp.2, sub_self]
  have hsupport : ∑ i ∈ S, (q i - p i) • A i = 0 := by
    calc
      (∑ i ∈ S, (q i - p i) • A i) =
          ∑ i : Fin m, (q i - p i) • A i := by
        rw [← Finset.sum_subset (Finset.subset_univ S)]
        intro i _ hi
        rw [hqzero i hi, hpzero i hi, sub_self, zero_smul]
      _ = 0 := hall
  have hcoeff : ∀ i ∈ S, q i - p i = 0 :=
    (linearIndepOn_finset_iff.mp hlin) (fun i ↦ q i - p i) hsupport
  funext i
  by_cases hi : i ∈ S
  · exact sub_eq_zero.mp (hcoeff i hi)
  · rw [hqzero i hi, hpzero i hi]

/-- Consequently the number of nonzero masses of such an extreme
representation is at most the ambient linear dimension. -/
theorem coefficientSupport_card_le_finrank_of_linearIndepOn
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]
    (A : Fin m → E) (p : Fin m → ℝ)
    (hlin : LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m))) :
    (coefficientSupport p).card ≤ Module.finrank ℝ E := by
  rw [← Fintype.card_coe]
  exact hlin.fintype_card_le_finrank

/-- Specialization: a linearly independent finite optimizer over `Fin n`
has at most `n` nonzero masses. -/
theorem coefficientSupport_card_le_fin
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (p : Fin m → ℝ)
    (hlin : LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m))) :
    (coefficientSupport p).card ≤ n := by
  simpa [Module.finrank_fin_fun] using
    coefficientSupport_card_le_finrank_of_linearIndepOn A p hlin

/-- The exact finite-fiber criterion: a probability vector is extreme when
the augmented dictionary vectors on its support are linearly independent.
The extra coordinate records the total-mass constraint. -/
theorem finiteMixtureFiber_extreme_of_augmented_linearIndepOn
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ)
    (hp : p ∈ finiteMixtureFiber A v)
    (hlin : LinearIndepOn ℝ (augmentedDictionary A)
      (coefficientSupport p : Set (Fin m))) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ := by
  classical
  rw [mem_extremePoints_iff_left]
  refine ⟨hp, ?_⟩
  intro q hq r hr hpqr
  rw [openSegment_eq_image] at hpqr
  rcases hpqr with ⟨t, ht, hrepr⟩
  rcases ht with ⟨htzero, htone⟩
  let S := coefficientSupport p
  have hqnonneg (i : Fin m) : 0 ≤ q i := hq.1.1 i
  have hrnonneg (i : Fin m) : 0 ≤ r i := hr.1.1 i
  have hqzero (i : Fin m) (hi : i ∉ S) : q i = 0 := by
    have hpzero : p i = 0 :=
      (not_mem_coefficientSupport_iff p i).mp hi
    have hcoord := congrFun hrepr i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcoord
    rw [hpzero] at hcoord
    have hleft : 0 ≤ (1 - t) * q i :=
      mul_nonneg (sub_nonneg.mpr htone.le) (hqnonneg i)
    have hright : 0 ≤ t * r i := mul_nonneg htzero.le (hrnonneg i)
    have hleftzero : (1 - t) * q i = 0 := by linarith
    rcases mul_eq_zero.mp hleftzero with ht | hq
    · linarith
    · exact hq
  have hpzero (i : Fin m) (hi : i ∉ S) : p i = 0 :=
    (not_mem_coefficientSupport_iff p i).mp hi
  have hall : ∑ i : Fin m, (q i - p i) • augmentedDictionary A i = 0 := by
    apply Prod.ext
    · rw [Prod.fst_sum]
      simp [augmentedDictionary, Finset.sum_sub_distrib, hq.1.2, hp.1.2]
    · rw [Prod.snd_sum]
      simp only [augmentedDictionary]
      calc
        (∑ i : Fin m, (q i - p i) • A i) =
            finiteMixtureValue A q - finiteMixtureValue A p := by
          simp [finiteMixtureValue, sub_smul, Finset.sum_sub_distrib]
        _ = 0 := by rw [hq.2, hp.2, sub_self]
  have hsupport : ∑ i ∈ S, (q i - p i) • augmentedDictionary A i = 0 := by
    calc
      (∑ i ∈ S, (q i - p i) • augmentedDictionary A i) =
          ∑ i : Fin m, (q i - p i) • augmentedDictionary A i := by
        rw [← Finset.sum_subset (Finset.subset_univ S)]
        intro i _ hi
        rw [hqzero i hi, hpzero i hi, sub_self, zero_smul]
      _ = 0 := hall
  have hcoeff : ∀ i ∈ S, q i - p i = 0 :=
    (linearIndepOn_finset_iff.mp hlin) (fun i ↦ q i - p i) hsupport
  funext i
  by_cases hi : i ∈ S
  · exact sub_eq_zero.mp (hcoeff i hi)
  · rw [hqzero i hi, hpzero i hi]

/-- Conversely, every extreme point of a finite probability-mixture fiber has
an affinely independent active dictionary. -/
theorem augmented_linearIndepOn_of_finiteMixtureFiber_extreme
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ)
    (hp : p ∈ (finiteMixtureFiber A v).extremePoints ℝ) :
    LinearIndepOn ℝ (augmentedDictionary A)
      (coefficientSupport p : Set (Fin m)) := by
  classical
  let S := coefficientSupport p
  rw [linearIndepOn_finset_iff]
  intro f hf
  by_contra hcoeff
  push Not at hcoeff
  obtain ⟨i₀, hi₀S, hi₀⟩ := hcoeff
  have hpFiber : p ∈ finiteMixtureFiber A v := hp.1
  have hSnonempty : S.Nonempty := ⟨i₀, hi₀S⟩
  let P : Finset ℝ := S.image p
  have hPnonempty : P.Nonempty := hSnonempty.image p
  let δ : ℝ := P.min' hPnonempty
  have hδmem : δ ∈ P := Finset.min'_mem P hPnonempty
  have hδpos : 0 < δ := by
    rcases Finset.mem_image.mp hδmem with ⟨i, hiS, hiδ⟩
    rw [← hiδ]
    exact lt_of_le_of_ne (hpFiber.1.1 i)
      (mem_coefficientSupport p i |>.mp hiS).symm
  have hδle (i : Fin m) (hiS : i ∈ S) : δ ≤ p i := by
    exact Finset.min'_le P (p i) (Finset.mem_image.mpr ⟨i, hiS, rfl⟩)
  let M : ℝ := ∑ i ∈ S, |f i|
  have hMnonneg : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  let ε : ℝ := δ / (2 * (M + 1))
  have hdenpos : 0 < 2 * (M + 1) := mul_pos (by norm_num) (by linarith)
  have hεpos : 0 < ε := div_pos hδpos hdenpos
  let c : Fin m → ℝ := fun i ↦ if i ∈ S then f i else 0
  have hc_eq (i : Fin m) (hiS : i ∈ S) : c i = f i := by simp [c, hiS]
  have hc_zero (i : Fin m) (hiS : i ∉ S) : c i = 0 := by simp [c, hiS]
  have hc_aug : ∑ i : Fin m, c i • augmentedDictionary A i = 0 := by
    have hfull : (∑ i : Fin m, c i • augmentedDictionary A i) =
        ∑ i ∈ S, c i • augmentedDictionary A i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hiS
      rw [hc_zero i hiS, zero_smul]
    rw [hfull]
    calc
      (∑ i ∈ S, c i • augmentedDictionary A i) =
          ∑ i ∈ S, f i • augmentedDictionary A i := by
        apply Finset.sum_congr rfl
        intro i hiS
        rw [hc_eq i hiS]
      _ = 0 := by simpa [S] using hf
  have hc_sum : ∑ i : Fin m, c i = 0 := by
    have hfirst := congrArg (AddMonoidHom.fst ℝ E) hc_aug
    simpa [augmentedDictionary] using hfirst
  have hc_value : ∑ i : Fin m, c i • A i = 0 := by
    have hsecond := congrArg (AddMonoidHom.snd ℝ E) hc_aug
    simpa [augmentedDictionary] using hsecond
  have hc_bound (i : Fin m) : |ε * c i| ≤ p i := by
    by_cases hiS : i ∈ S
    · have hfi_le : |f i| ≤ M := by
        exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (f j)) hiS
      have hfi_den : |f i| ≤ 2 * (M + 1) := by linarith
      have heq : ε * (2 * (M + 1)) = δ := by
        dsimp [ε]
        field_simp
      calc
        |ε * c i| = ε * |f i| := by
          rw [hc_eq i hiS, abs_mul, abs_of_pos hεpos]
        _ ≤ ε * (2 * (M + 1)) := mul_le_mul_of_nonneg_left hfi_den hεpos.le
        _ = δ := heq
        _ ≤ p i := hδle i hiS
    · rw [hc_zero i hiS, mul_zero, abs_zero]
      exact hpFiber.1.1 i
  let q : Fin m → ℝ := fun i ↦ p i + ε * c i
  let r : Fin m → ℝ := fun i ↦ p i - ε * c i
  have hqnonneg (i : Fin m) : 0 ≤ q i := by
    have h := (abs_le.mp (hc_bound i)).1
    dsimp [q]
    linarith
  have hrnonneg (i : Fin m) : 0 ≤ r i := by
    have h := (abs_le.mp (hc_bound i)).2
    dsimp [r]
    linarith
  have hqsum : ∑ i : Fin m, q i = 1 := by
    simp only [q, Finset.sum_add_distrib, ← Finset.mul_sum, hc_sum, mul_zero, add_zero,
      hpFiber.1.2]
  have hrsum : ∑ i : Fin m, r i = 1 := by
    simp only [r, Finset.sum_sub_distrib, ← Finset.mul_sum, hc_sum, mul_zero, sub_zero,
      hpFiber.1.2]
  have hqvalue : finiteMixtureValue A q = v := by
    calc
      finiteMixtureValue A q = finiteMixtureValue A p + ε • (∑ i, c i • A i) := by
        simp [finiteMixtureValue, q, add_smul, Finset.sum_add_distrib,
          Finset.smul_sum, smul_smul]
      _ = v := by rw [hc_value, smul_zero, add_zero, hpFiber.2]
  have hrvalue : finiteMixtureValue A r = v := by
    calc
      finiteMixtureValue A r = finiteMixtureValue A p - ε • (∑ i, c i • A i) := by
        simp [finiteMixtureValue, r, sub_smul, Finset.sum_sub_distrib,
          Finset.smul_sum, smul_smul]
      _ = v := by rw [hc_value, smul_zero, sub_zero, hpFiber.2]
  have hqFiber : q ∈ finiteMixtureFiber A v := ⟨⟨hqnonneg, hqsum⟩, hqvalue⟩
  have hrFiber : r ∈ finiteMixtureFiber A v := ⟨⟨hrnonneg, hrsum⟩, hrvalue⟩
  have hqne : q ≠ p := by
    intro hqp
    have hi := congrFun hqp i₀
    have hc0 : c i₀ = f i₀ := hc_eq i₀ hi₀S
    dsimp [q] at hi
    rw [hc0] at hi
    have : ε * f i₀ ≠ 0 := mul_ne_zero hεpos.ne' hi₀
    apply this
    linarith
  have hpseg : p ∈ openSegment ℝ q r := by
    rw [openSegment_eq_image]
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    funext i
    dsimp [q, r]
    ring
  exact hqne (hp.2 hqFiber hrFiber hpseg)

/-- Characterization of the extreme points of a finite mixture fiber. -/
theorem finiteMixtureFiber_extreme_iff_augmented_linearIndepOn
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ ↔
      p ∈ finiteMixtureFiber A v ∧
        LinearIndepOn ℝ (augmentedDictionary A)
          (coefficientSupport p : Set (Fin m)) := by
  constructor
  · intro hp
    exact ⟨hp.1, augmented_linearIndepOn_of_finiteMixtureFiber_extreme A v p hp⟩
  · rintro ⟨hp, hlin⟩
    exact finiteMixtureFiber_extreme_of_augmented_linearIndepOn A v p hp hlin

/-- On a contact hyperplane, affine independence and linear independence
coincide.  This is the finite-dimensional version of the likelihood contact
identity used for optimizer supports in the paper. -/
theorem augmented_linearIndepOn_iff_of_contact
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (S : Finset (Fin m)) (b : E →ₗ[ℝ] ℝ)
    (hcontact : ∀ i ∈ S, b (A i) = 1) :
    LinearIndepOn ℝ (augmentedDictionary A) (S : Set (Fin m)) ↔
      LinearIndepOn ℝ A (S : Set (Fin m)) := by
  classical
  rw [linearIndepOn_finset_iff, linearIndepOn_finset_iff]
  constructor
  · intro haug f hf
    have hsum : ∑ i ∈ S, f i = 0 := by
      calc
        (∑ i ∈ S, f i) = ∑ i ∈ S, f i * 1 := by simp
        _ = ∑ i ∈ S, f i * b (A i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcontact i hi]
        _ = b (∑ i ∈ S, f i • A i) := by
          rw [map_sum]
          simp
        _ = 0 := by rw [hf, map_zero]
    apply haug f
    apply Prod.ext
    · rw [Prod.fst_sum]
      simpa [augmentedDictionary] using hsum
    · rw [Prod.snd_sum]
      simpa [augmentedDictionary] using hf
  · intro hA f hf
    apply hA f
    have hsnd := congrArg (AddMonoidHom.snd ℝ E) hf
    simpa [augmentedDictionary] using hsnd

/-- A supporting functional which is at most one on the dictionary equals one
at every active atom of a probability mixture on its contact hyperplane. -/
theorem contact_eq_one_on_coefficientSupport
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ) (b : E →ₗ[ℝ] ℝ)
    (hp : p ∈ finiteMixtureFiber A v) (hbv : b v = 1)
    (hbA : ∀ i, b (A i) ≤ 1) :
    ∀ i ∈ coefficientSupport p, b (A i) = 1 := by
  classical
  have hterm_nonneg (i : Fin m) : 0 ≤ p i * (1 - b (A i)) :=
    mul_nonneg (hp.1.1 i) (sub_nonneg.mpr (hbA i))
  have hsumzero : ∑ i : Fin m, p i * (1 - b (A i)) = 0 := by
    calc
      (∑ i : Fin m, p i * (1 - b (A i))) =
          ∑ i, (p i - p i * b (A i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, p i) - ∑ i, p i * b (A i) :=
        Finset.sum_sub_distrib (s := Finset.univ)
          (fun i ↦ p i) (fun i ↦ p i * b (A i))
      _ = 1 - b (finiteMixtureValue A p) := by
        rw [hp.1.2, finiteMixtureValue, map_sum]
        simp only [map_smul, smul_eq_mul]
      _ = 0 := by rw [hp.2, hbv, sub_self]
  intro i hi
  have hzero : p i * (1 - b (A i)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hterm_nonneg j).mp hsumzero i
      (Finset.mem_univ i)
  have hpne : p i ≠ 0 := (mem_coefficientSupport p i).mp hi
  rcases mul_eq_zero.mp hzero with hpi | hcontact
  · exact (hpne hpi).elim
  · linarith

/-- With a contact functional, the paper's stated linear-independence
characterization of an extreme optimizer is exact. -/
theorem finiteMixtureFiber_extreme_iff_linearIndepOn_of_contact
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ) (b : E →ₗ[ℝ] ℝ)
    (hcontact : ∀ i ∈ coefficientSupport p, b (A i) = 1) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ ↔
      p ∈ finiteMixtureFiber A v ∧
        LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m)) := by
  rw [finiteMixtureFiber_extreme_iff_augmented_linearIndepOn]
  exact and_congr_right fun _ ↦
    augmented_linearIndepOn_iff_of_contact A (coefficientSupport p) b hcontact

/-- Hence a contact-supported extreme finite mixture has at most the ambient
linear dimension many active atoms. -/
theorem coefficientSupport_card_le_finrank_of_extreme_contact
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ) (b : E →ₗ[ℝ] ℝ)
    (hp : p ∈ (finiteMixtureFiber A v).extremePoints ℝ)
    (hcontact : ∀ i ∈ coefficientSupport p, b (A i) = 1) :
    (coefficientSupport p).card ≤ Module.finrank ℝ E := by
  apply coefficientSupport_card_le_finrank_of_linearIndepOn A p
  exact (finiteMixtureFiber_extreme_iff_linearIndepOn_of_contact
    A v p b hcontact).mp hp |>.2

/-- If the dictionary vectors in the union of any two extreme supports are
linearly independent, the compact finite mixture fiber is a singleton.  This
is the finite-dimensional Krein--Milman step behind the paper's generic
uniqueness argument. -/
theorem finiteMixtureFiber_eq_singleton_of_extreme_union_linearIndepOn
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin m → E) (v : E) (hnonempty : (finiteMixtureFiber A v).Nonempty)
    (hunion : ∀ p ∈ (finiteMixtureFiber A v).extremePoints ℝ,
      ∀ q ∈ (finiteMixtureFiber A v).extremePoints ℝ,
        LinearIndepOn ℝ A
          ((coefficientSupport p ∪ coefficientSupport q : Finset (Fin m)) :
            Set (Fin m))) :
    ∃ p, finiteMixtureFiber A v = {p} := by
  classical
  let F := finiteMixtureFiber A v
  have hcompact : IsCompact F := isCompact_finiteMixtureFiber A v
  have hconvex : Convex ℝ F := convex_finiteMixtureFiber A v
  obtain ⟨e, he⟩ := hcompact.extremePoints_nonempty hnonempty
  have heq (p : Fin m → ℝ) (hp : p ∈ F.extremePoints ℝ)
      (q : Fin m → ℝ) (hq : q ∈ F.extremePoints ℝ) : p = q := by
    let U := coefficientSupport p ∪ coefficientSupport q
    have hpzero (i : Fin m) (hi : i ∉ U) : p i = 0 := by
      apply (not_mem_coefficientSupport_iff p i).mp
      exact fun hip ↦ hi (Finset.mem_union_left _ hip)
    have hqzero (i : Fin m) (hi : i ∉ U) : q i = 0 := by
      apply (not_mem_coefficientSupport_iff q i).mp
      exact fun hiq ↦ hi (Finset.mem_union_right _ hiq)
    have hall : ∑ i : Fin m, (p i - q i) • A i = 0 := by
      calc
        (∑ i : Fin m, (p i - q i) • A i) =
            finiteMixtureValue A p - finiteMixtureValue A q := by
          simp [finiteMixtureValue, sub_smul, Finset.sum_sub_distrib]
        _ = 0 := by rw [hp.1.2, hq.1.2, sub_self]
    have hU : ∑ i ∈ U, (p i - q i) • A i = 0 := by
      calc
        (∑ i ∈ U, (p i - q i) • A i) =
            ∑ i : Fin m, (p i - q i) • A i := by
          rw [← Finset.sum_subset (Finset.subset_univ U)]
          intro i _ hi
          rw [hpzero i hi, hqzero i hi, sub_self, zero_smul]
        _ = 0 := hall
    have hcoeff : ∀ i ∈ U, p i - q i = 0 :=
      (linearIndepOn_finset_iff.mp (hunion p hp q hq))
        (fun i ↦ p i - q i) hU
    funext i
    by_cases hi : i ∈ U
    · exact sub_eq_zero.mp (hcoeff i hi)
    · rw [hpzero i hi, hqzero i hi]
  have hextreme : F.extremePoints ℝ = {e} := by
    ext p
    constructor
    · intro hp
      exact Set.mem_singleton_iff.mpr (heq p hp e he)
    · intro hp
      exact Set.mem_singleton_iff.mp hp ▸ he
  have hKM := closure_convexHull_extremePoints hcompact hconvex
  rw [hextreme, convexHull_singleton, closure_singleton] at hKM
  exact ⟨e, hKM.symm⟩

/-- Cardinal form: if all extreme supports have at most `M` atoms and every
dictionary subfamily of size at most `2M` is independent, then the fiber is a
singleton. -/
theorem finiteMixtureFiber_eq_singleton_of_support_bound
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin m → E) (v : E) (M : ℕ)
    (hnonempty : (finiteMixtureFiber A v).Nonempty)
    (hsupport : ∀ p ∈ (finiteMixtureFiber A v).extremePoints ℝ,
      (coefficientSupport p).card ≤ M)
    (hgeneric : ∀ S : Finset (Fin m), S.card ≤ 2 * M →
      LinearIndepOn ℝ A (S : Set (Fin m))) :
    ∃ p, finiteMixtureFiber A v = {p} := by
  apply finiteMixtureFiber_eq_singleton_of_extreme_union_linearIndepOn
    A v hnonempty
  intro p hp q hq
  apply hgeneric
  calc
    (coefficientSupport p ∪ coefficientSupport q).card ≤
        (coefficientSupport p).card + (coefficientSupport q).card :=
      Finset.card_union_le _ _
    _ ≤ M + M := Nat.add_le_add (hsupport p hp) (hsupport q hq)
    _ = 2 * M := by omega

end ReweightedNPMLE
