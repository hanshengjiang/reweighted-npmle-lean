import Mathlib.Data.Sym.Card
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import ReweightedNPMLE.Gaussian
import ReweightedNPMLE.CompactConvexHull
import ReweightedNPMLE.Taylor
import Mathlib.Analysis.Convex.Integral

namespace ReweightedNPMLE

open scoped BigOperators
open Finset Fintype

/--
Coordinates for monomials of total degree at most `D` in `d` variables.

The extra element `0 : Fin (d + 1)` is a homogenizing (slack) variable
whose value is fixed to one.  The remaining elements `Fin.succ i`
represent the `d` genuine variables.
-/
abbrev MonomialCoord (d D : ℕ) := Sym (Fin (d + 1)) D

/-- There are exactly `choose (D + d) d` monomials of total degree at most `D`. -/
theorem card_monomialCoord (d D : ℕ) :
    Fintype.card (MonomialCoord d D) = (D + d).choose d := by
  rw [Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have h : d + 1 + D - 1 = D + d := by omega
  rw [h, Nat.choose_symm_add]

/-- Evaluate a homogenized variable: the slack variable is `1`. -/
def homogenizedVariable {d : ℕ} (θ : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases 1 θ

/-- Evaluate a monomial coordinate at `θ`. -/
def monomialEval {d D : ℕ} (θ : Fin d → ℝ) (m : MonomialCoord d D) : ℝ :=
  (m.val.map (homogenizedVariable θ)).prod

/-- Vector of all monomials of total degree at most `D`. -/
noncomputable def monomialFeature (d D : ℕ) :
    (Fin d → ℝ) → (MonomialCoord d D → ℝ) :=
  fun θ m ↦ monomialEval θ m

theorem continuous_monomialFeature (d D : ℕ) :
    Continuous (monomialFeature d D) := by
  apply continuous_pi
  intro m
  unfold monomialFeature monomialEval homogenizedVariable
  have hvar : ∀ i : Fin (d + 1), Continuous
      (fun a : Fin d → ℝ ↦ Fin.cases (motive := fun _ ↦ ℝ) 1 a i) := by
    intro i
    refine Fin.cases continuous_const (fun j ↦ continuous_apply j) i
  have hprod : ∀ s : Multiset (Fin (d + 1)),
      Continuous (fun a : Fin d → ℝ ↦
        (s.map (fun i ↦ Fin.cases (motive := fun _ ↦ ℝ) 1 a i)).prod) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simpa using (continuous_const : Continuous (fun _ : Fin d → ℝ ↦ (1 : ℝ)))
    | cons i s ih => simpa using (hvar i).mul ih
  exact hprod m.val

/-- Every finite monomial feature vector is integrable under a finite measure
when the parameter map is measurable and almost surely compactly supported. -/
theorem monomialFeature_integrable_of_compact_support
    {Θ : Type*} [MeasurableSpace Θ] {d D : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsFiniteMeasure μ]
    (θ : Θ → Fin d → ℝ) (hθmeas : Measurable θ)
    (K : Set (Fin d → ℝ)) (hKcompact : IsCompact K)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K) :
    MeasureTheory.Integrable (fun a ↦ monomialFeature d D (θ a)) μ := by
  obtain ⟨C, hC⟩ :=
    (hKcompact.image (continuous_monomialFeature d D)).isBounded.exists_norm_le
  apply MeasureTheory.Integrable.of_bound
    ((continuous_monomialFeature d D).measurable.comp hθmeas).aestronglyMeasurable C
  filter_upwards [hθK] with a ha
  exact hC (monomialFeature d D (θ a)) ⟨θ a, ha, rfl⟩

/-- The ambient dimension of the moment feature is the number of monomials. -/
theorem finrank_monomialFeature (d D : ℕ) :
    Module.finrank ℝ (MonomialCoord d D → ℝ) = (D + d).choose d := by
  rw [Module.finrank_fintype_fun_eq_card, card_monomialCoord]

/-- Compact-support moment matching: every probability-law moment vector has
an exactly matching discrete law with at most `choose(D+d,d)+1` slots.  Zero
masses pad representations using fewer atoms. -/
theorem exists_finite_monomial_moment_matching
    {Θ : Type*} [MeasurableSpace Θ] {d D : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Fin d → ℝ) (K : Set (Fin d → ℝ))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K)
    (hint : MeasureTheory.Integrable (fun a ↦ monomialFeature d D (θ a)) μ) :
    ∃ (w : Fin (Module.finrank ℝ (MonomialCoord d D → ℝ) + 1) → ℝ)
      (θ' : Fin (Module.finrank ℝ (MonomialCoord d D → ℝ) + 1) → Fin d → ℝ),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d D → ℝ) + 1)) ∧
      (∀ i, θ' i ∈ K) ∧
        ∑ i, w i • monomialFeature d D (θ' i) =
          ∫ a, monomialFeature d D (θ a) ∂μ := by
  let C := convexHull ℝ (monomialFeature d D '' K)
  have hCcompact : IsCompact C := isCompact_convexHull_of_isCompact
    (hKcompact.image (continuous_monomialFeature d D))
  have hmean : (∫ a, monomialFeature d D (θ a) ∂μ) ∈ C := by
    apply (convex_convexHull ℝ _).integral_mem hCcompact.isClosed
    · filter_upwards [hθK] with a ha
      exact subset_convexHull ℝ _ ⟨θ a, ha, rfl⟩
    · exact hint
  have himage : (monomialFeature d D '' K).Nonempty := hKnonempty.image _
  obtain ⟨w, z, hw, hz, hsum⟩ :=
    exists_fixed_barycentric_representation himage hmean
  have hchoice : ∀ i, ∃ θ, θ ∈ K ∧ monomialFeature d D θ = z i := by
    intro i
    rcases hz i with ⟨θ, hθ, hθz⟩
    exact ⟨θ, hθ, hθz⟩
  choose θ' hθ'K hθ'z using hchoice
  refine ⟨w, θ', hw, hθ'K, ?_⟩
  simpa only [hθ'z] using hsum

/-- The all-slack coordinate represents the constant monomial `1`. -/
def constantCoord (d D : ℕ) : MonomialCoord d D :=
  Sym.replicate D (0 : Fin (d + 1))

@[simp]
theorem monomialEval_constant (d D : ℕ) (θ : Fin d → ℝ) :
    monomialEval θ (constantCoord d D) = 1 := by
  simp only [monomialEval, constantCoord, Sym.val_replicate]
  simp [homogenizedVariable]

/-- Appending coordinates multiplies their monomial evaluations. -/
@[simp]
theorem monomialEval_append {d D E : ℕ} (θ : Fin d → ℝ)
    (m : MonomialCoord d D) (n : MonomialCoord d E) :
    monomialEval θ (m.append n) = monomialEval θ m * monomialEval θ n := by
  simp [monomialEval, Sym.append, Multiset.map_add]

/-- Pad a monomial with slack variables, without changing its value. -/
def padCoord {d D : ℕ} (E : ℕ) (m : MonomialCoord d D) :
    MonomialCoord d (D + E) :=
  m.append (constantCoord d E)

@[simp]
theorem monomialEval_pad {d D : ℕ} (E : ℕ) (θ : Fin d → ℝ)
    (m : MonomialCoord d D) :
    monomialEval θ (padCoord E m) = monomialEval θ m := by
  simp [padCoord]

/-- A function is a linear combination of the degree-at-most-`D` monomial coordinates. -/
def IsMonomialCombination {d D : ℕ} (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ c : MonomialCoord d D → ℝ,
    ∀ θ, f θ = ∑ m, c m * monomialEval θ m

/-- Equality of moment-feature barycenters preserves the weighted average of
every polynomial represented in those coordinates. -/
theorem IsMonomialCombination.weighted_sum_eq_of_feature_eq
    {d D : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (d := d) (D := D) f)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (z : ι → Fin d → ℝ)
    (w' : κ → ℝ) (z' : κ → Fin d → ℝ)
    (hmom : ∑ i, w i • monomialFeature d D (z i) =
      ∑ j, w' j • monomialFeature d D (z' j)) :
    ∑ i, w i * f (z i) = ∑ j, w' j * f (z' j) := by
  classical
  obtain ⟨c, hc⟩ := hf
  have hm : ∀ m : MonomialCoord d D,
      (∑ i, w i * monomialEval (z i) m) =
        ∑ j, w' j * monomialEval (z' j) m := by
    intro m
    have h := congrFun hmom m
    simpa [monomialFeature] using h
  calc
    (∑ i, w i * f (z i)) =
        ∑ m, c m * (∑ i, w i * monomialEval (z i) m) := by
          simp_rw [hc, mul_sum]
          rw [sum_comm]
          apply Fintype.sum_congr
          intro m
          apply Fintype.sum_congr
          intro i
          ring
    _ = ∑ m, c m * (∑ j, w' j * monomialEval (z' j) m) := by
          apply Fintype.sum_congr
          intro m
          rw [hm m]
    _ = ∑ j, w' j * f (z' j) := by
          simp_rw [hc, mul_sum]
          rw [sum_comm]
          apply Fintype.sum_congr
          intro m
          apply Fintype.sum_congr
          intro j
          ring

/-- A finite law and an integrable law with the same feature barycenter have
the same average for every polynomial represented by those features. -/
theorem IsMonomialCombination.weighted_sum_eq_integral
    {Θ : Type*} [MeasurableSpace Θ] {d D : ℕ}
    {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (d := d) (D := D) f)
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → Fin d → ℝ)
    (μ : MeasureTheory.Measure Θ) (θ : Θ → Fin d → ℝ)
    (hint : MeasureTheory.Integrable (fun a ↦ monomialFeature d D (θ a)) μ)
    (hmom : ∑ i, w i • monomialFeature d D (z i) =
      ∫ a, monomialFeature d D (θ a) ∂μ) :
    ∑ i, w i * f (z i) = ∫ a, f (θ a) ∂μ := by
  classical
  obtain ⟨c, hc⟩ := hf
  let L : (MonomialCoord d D → ℝ) →L[ℝ] ℝ :=
    ∑ m, c m • ContinuousLinearMap.proj m
  have hL (u : Fin d → ℝ) : L (monomialFeature d D u) = f u := by
    rw [hc]
    dsimp only [L]
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, monomialFeature]
  calc
    (∑ i, w i * f (z i)) = L (∑ i, w i • monomialFeature d D (z i)) := by
      rw [map_sum]
      apply Fintype.sum_congr
      intro i
      rw [map_smul, hL]
      rfl
    _ = L (∫ a, monomialFeature d D (θ a) ∂μ) := congrArg L hmom
    _ = ∫ a, L (monomialFeature d D (θ a)) ∂μ :=
      (L.integral_comp_comm hint).symm
    _ = ∫ a, f (θ a) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun a ↦ hL (θ a)

/-- Integrability of the whole finite feature vector implies integrability of
each polynomial represented by that vector. -/
theorem IsMonomialCombination.integrable_comp_of_feature
    {Θ : Type*} [MeasurableSpace Θ] {d D : ℕ}
    {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (d := d) (D := D) f)
    (μ : MeasureTheory.Measure Θ) (θ : Θ → Fin d → ℝ)
    (hint : MeasureTheory.Integrable (fun a ↦ monomialFeature d D (θ a)) μ) :
    MeasureTheory.Integrable (fun a ↦ f (θ a)) μ := by
  classical
  obtain ⟨c, hc⟩ := hf
  let L : (MonomialCoord d D → ℝ) →L[ℝ] ℝ :=
    ∑ m, c m • ContinuousLinearMap.proj m
  have hL (u : Fin d → ℝ) : L (monomialFeature d D u) = f u := by
    rw [hc]
    dsimp only [L]
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, monomialFeature]
  exact (L.integrable_comp hint).congr
    (Filter.Eventually.of_forall fun a ↦ hL (θ a))

/-- A sum indexed by any finite type can be collected into monomial coordinates. -/
private theorem isMonomialCombination_reindex {d D : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq (MonomialCoord d D)]
    (c : ι → ℝ) (m : ι → MonomialCoord d D) :
    IsMonomialCombination (d := d) (D := D)
      (fun θ => ∑ i, c i * monomialEval θ (m i)) := by
  classical
  refine ⟨fun q => ∑ i, if m i = q then c i else 0, fun θ => ?_⟩
  simp_rw [sum_mul]
  rw [sum_comm]
  simp

/-- Every monomial coordinate is itself a monomial combination. -/
theorem isMonomialCombination_monomial {d D : ℕ} (m : MonomialCoord d D) :
    IsMonomialCombination (d := d) (D := D) (fun θ => monomialEval θ m) := by
  simpa using
    (isMonomialCombination_reindex (d := d) (D := D) (ι := Fin 1)
      (fun _ => 1) (fun _ => m))

/-- Constant functions are represented by the all-slack coordinate. -/
theorem isMonomialCombination_const {d D : ℕ} (a : ℝ) :
    IsMonomialCombination (d := d) (D := D) (fun _ : Fin d → ℝ => a) := by
  simpa using
    (isMonomialCombination_reindex (d := d) (D := D) (ι := Fin 1)
      (fun _ => a) (fun _ => constantCoord d D))

theorem IsMonomialCombination.add {d D : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f)
    (hg : IsMonomialCombination (D := D) g) :
    IsMonomialCombination (d := d) (D := D) (fun θ => f θ + g θ) := by
  classical
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun m => a m + b m, fun θ => ?_⟩
  simp_rw [add_mul, sum_add_distrib, ← ha θ, ← hb θ]

theorem IsMonomialCombination.smul {d D : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f) (a : ℝ) :
    IsMonomialCombination (d := d) (D := D) (fun θ => a * f θ) := by
  classical
  obtain ⟨c, hc⟩ := hf
  refine ⟨fun m => a * c m, fun θ => ?_⟩
  change a * f θ = _
  rw [hc θ, mul_sum]
  simp only [mul_assoc]

theorem IsMonomialCombination.neg {d D : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f) :
    IsMonomialCombination (d := d) (D := D) (fun θ => -f θ) := by
  simpa using hf.smul (-1)

theorem IsMonomialCombination.sub {d D : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f)
    (hg : IsMonomialCombination (D := D) g) :
    IsMonomialCombination (d := d) (D := D) (fun θ => f θ - g θ) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- Finite sums of represented functions remain represented. -/
theorem isMonomialCombination_finsetSum {d D : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → (Fin d → ℝ) → ℝ)
    (hf : ∀ i ∈ s, IsMonomialCombination (D := D) (f i)) :
    IsMonomialCombination (d := d) (D := D) (fun θ => ∑ i ∈ s, f i θ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using isMonomialCombination_const (d := d) (D := D) 0
  | @insert a s ha ih =>
      obtain ⟨c, hc⟩ :=
        (hf a (mem_insert_self a s)).add
          (ih (fun i hi => hf i (mem_insert_of_mem hi)))
      refine ⟨c, fun θ => ?_⟩
      change (∑ i ∈ insert a s, f i θ) = _
      rw [sum_insert ha]
      exact hc θ

/-- Adding slack degree preserves representability. -/
theorem IsMonomialCombination.pad {d D : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f) (E : ℕ) :
    IsMonomialCombination (d := d) (D := D + E) f := by
  classical
  obtain ⟨c, hc⟩ := hf
  obtain ⟨a, ha⟩ :=
    isMonomialCombination_reindex (d := d) (D := D + E)
      c (fun m => padCoord E m)
  refine ⟨a, fun θ => ?_⟩
  rw [hc θ]
  simpa using ha θ

/-- Products of represented functions are represented at the sum of the degrees. -/
theorem IsMonomialCombination.mul {d D E : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f)
    (hg : IsMonomialCombination (D := E) g) :
    IsMonomialCombination (d := d) (D := D + E) (fun θ => f θ * g θ) := by
  classical
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  obtain ⟨c, hc⟩ :=
    isMonomialCombination_reindex (d := d) (D := D + E)
      (fun p : MonomialCoord d D × MonomialCoord d E => a p.1 * b p.2)
      (fun p => p.1.append p.2)
  refine ⟨c, fun θ => ?_⟩
  change f θ * g θ = _
  rw [ha θ, hb θ, sum_mul]
  simp_rw [mul_sum]
  rw [← Fintype.sum_prod_type']
  calc
    (∑ p : MonomialCoord d D × MonomialCoord d E,
        (a p.1 * monomialEval θ p.1) * (b p.2 * monomialEval θ p.2)) =
        ∑ p : MonomialCoord d D × MonomialCoord d E,
          (a p.1 * b p.2) * monomialEval θ (p.1.append p.2) := by
            refine Fintype.sum_congr _ _ fun p => ?_
            simp only [monomialEval_append]
            ring
    _ = ∑ q, c q * monomialEval θ q := hc θ

/-- Degree-one coordinate for the genuine variable `θ i`. -/
def linearCoordOne {d : ℕ} (i : Fin d) : MonomialCoord d 1 :=
  Fin.succ i ::ₛ Sym.nil

@[simp]
theorem monomialEval_linearOne {d : ℕ} (θ : Fin d → ℝ) (i : Fin d) :
    monomialEval θ (linearCoordOne i) = θ i := by
  simp only [monomialEval, linearCoordOne, Sym.val_eq_coe]
  rw [Sym.coe_cons, Sym.coe_nil]
  simp [homogenizedVariable]

/-- Degree-two coordinate for the linear monomial `θ i` (one slack factor). -/
def linearCoord {d : ℕ} (i : Fin d) : MonomialCoord d 2 :=
  (0 : Fin (d + 1)) ::ₛ Fin.succ i ::ₛ Sym.nil

/-- Degree-two coordinate for the quadratic monomial `(θ i)^2`. -/
def squareCoord {d : ℕ} (i : Fin d) : MonomialCoord d 2 :=
  Fin.succ i ::ₛ Fin.succ i ::ₛ Sym.nil

@[simp]
theorem monomialEval_linear {d : ℕ} (θ : Fin d → ℝ) (i : Fin d) :
    monomialEval θ (linearCoord i) = θ i := by
  simp only [monomialEval, linearCoord, Sym.val_eq_coe]
  rw [Sym.coe_cons, Sym.coe_cons, Sym.coe_nil]
  simp [homogenizedVariable]

@[simp]
theorem monomialEval_square {d : ℕ} (θ : Fin d → ℝ) (i : Fin d) :
    monomialEval θ (squareCoord i) = (θ i) ^ 2 := by
  simp only [monomialEval, squareCoord, Sym.val_eq_coe]
  rw [Sym.coe_cons, Sym.coe_cons, Sym.coe_nil]
  simp [homogenizedVariable, pow_two]

/-- The Euclidean dot product, written explicitly in finite coordinates. -/
def coordinateDot {d : ℕ} (x θ : Fin d → ℝ) : ℝ :=
  ∑ i, x i * θ i

/-- Native Euclidean inner products agree with the explicit coordinate dot
product. -/
theorem inner_eq_coordinateDot {d : ℕ} (x θ : Point d) :
    inner ℝ x θ = coordinateDot (fun i ↦ x i) (fun i ↦ θ i) := by
  rw [coordinateDot, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  apply Fintype.sum_congr
  intro i
  ring

/-- A coordinate dot product is a polynomial of total degree at most one. -/
theorem coordinateDot_isMonomialCombination_one {d : ℕ} (x : Fin d → ℝ) :
    IsMonomialCombination (d := d) (D := 1) (coordinateDot x) := by
  simpa [coordinateDot] using
    (isMonomialCombination_reindex (d := d) (D := 1)
      x (fun i ↦ linearCoordOne i))

/-- The `ell`th power of a dot product has degree at most `ell`. -/
theorem coordinateDot_pow_isMonomialCombination {d : ℕ}
    (x : Fin d → ℝ) (ell : ℕ) :
    IsMonomialCombination (d := d) (D := ell)
      (fun θ ↦ (coordinateDot x θ) ^ ell) := by
  induction ell with
  | zero => simpa using isMonomialCombination_const (d := d) (D := 0) 1
  | succ ell ih =>
      simpa [pow_succ] using ih.mul (coordinateDot_isMonomialCombination_one x)

/-- The exponential series in a dot product, truncated after order `L`. -/
noncomputable def coordinateTruncatedInnerExp {d : ℕ} (L : ℕ)
    (x θ : Fin d → ℝ) : ℝ :=
  ∑ ell ∈ range (L + 1), (coordinateDot x θ) ^ ell / ell.factorial

/-- Taylor polynomial for `exp ⟪θ,η⟫`, expressed on the native Euclidean
parameter space. -/
noncomputable def pointTruncatedInnerExp {d : ℕ} (L : ℕ)
    (θ η : Point d) : ℝ :=
  ∑ ell ∈ range (L + 1), (inner ℝ θ η) ^ ell / ell.factorial

/-- The truncated inner-product exponential has degree at most `L`. -/
theorem coordinateTruncatedInnerExp_isMonomialCombination {d : ℕ}
    (L : ℕ) (x : Fin d → ℝ) :
    IsMonomialCombination (d := d) (D := L)
      (coordinateTruncatedInnerExp L x) := by
  have hterm : ∀ ell ∈ range (L + 1),
      IsMonomialCombination (d := d) (D := L)
        (fun θ ↦ (coordinateDot x θ) ^ ell / ell.factorial) := by
    intro ell hell
    have hell_le : ell ≤ L := Nat.le_of_lt_succ (mem_range.mp hell)
    have hpadded := (coordinateDot_pow_isMonomialCombination x ell).pad (L - ell)
    have hdegree : ell + (L - ell) = L := Nat.add_sub_of_le hell_le
    rw [hdegree] at hpadded
    simpa [div_eq_mul_inv, mul_comm] using
      hpadded.smul ((ell.factorial : ℝ)⁻¹)
  exact isMonomialCombination_finsetSum (range (L + 1))
    (fun ell θ ↦ (coordinateDot x θ) ^ ell / ell.factorial) hterm

/-- Equality of finite moment vectors through degree `L` makes the Taylor
polynomial of `exp ⟪θ,y⟫` agree for every fixed `y`. -/
theorem finite_moment_matching_pointTruncatedInnerExp
    {d L : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (θ : ι → Point d)
    (v : κ → ℝ) (η : κ → Point d)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ θ i r) =
      ∑ j, v j • monomialFeature d L (fun r ↦ η j r))
    (y : Point d) :
    ∑ i, w i * pointTruncatedInnerExp L (θ i) y =
      ∑ j, v j * pointTruncatedInnerExp L (η j) y := by
  have h := (coordinateTruncatedInnerExp_isMonomialCombination
    L (fun r ↦ y r)).weighted_sum_eq_of_feature_eq
      w (fun i r ↦ θ i r) v (fun j r ↦ η j r) hmom
  simpa only [pointTruncatedInnerExp, coordinateTruncatedInnerExp,
    inner_eq_coordinateDot, real_inner_comm] using h

/-- The squared Euclidean norm, written explicitly in finite coordinates. -/
def coordinateNormSq {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  ∑ i, (θ i) ^ 2

/-- The Gaussian score `x · θ - ‖θ‖² / 2`. -/
noncomputable def coordinateGaussianScore {d : ℕ} (x θ : Fin d → ℝ) : ℝ :=
  coordinateDot x θ - (1 / 2 : ℝ) * coordinateNormSq θ

/-- Coordinate and inner-product definitions of the Gaussian score agree. -/
theorem gaussianScore_eq_coordinateGaussianScore
    {d : ℕ} (x θ : Point d) :
    gaussianScore x θ =
      coordinateGaussianScore (fun i ↦ x i) (fun i ↦ θ i) := by
  rw [gaussianScore, coordinateGaussianScore, coordinateDot, coordinateNormSq,
    PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq]
  simp only [RCLike.inner_apply, conj_trivial]
  have hdot :
      (∑ i, θ i * x i) = ∑ i, x i * θ i := by
    apply Fintype.sum_congr
    intro i
    ring
  rw [hdot]
  ring

/-- The Gaussian score is a combination of monomials of degree at most two. -/
theorem coordinateGaussianScore_isMonomialCombination {d : ℕ} (x : Fin d → ℝ) :
    IsMonomialCombination (d := d) (D := 2) (coordinateGaussianScore x) := by
  have hdot :
      IsMonomialCombination (d := d) (D := 2) (coordinateDot x) := by
    simpa [coordinateDot] using
      (isMonomialCombination_reindex (d := d) (D := 2)
        x (fun i => linearCoord i))
  have hnorm :
      IsMonomialCombination (d := d) (D := 2) coordinateNormSq := by
    simpa [coordinateNormSq] using
      (isMonomialCombination_reindex (d := d) (D := 2)
        (fun _ : Fin d => (1 : ℝ)) (fun i => squareCoord i))
  change IsMonomialCombination (d := d) (D := 2)
    (fun θ => coordinateDot x θ - (1 / 2 : ℝ) * coordinateNormSq θ)
  exact hdot.sub (hnorm.smul (1 / 2))

/-- The `ell`th power of the Gaussian score has total degree at most `2 * ell`. -/
theorem coordinateGaussianScore_pow_isMonomialCombination
    {d : ℕ} (x : Fin d → ℝ) (ell : ℕ) :
    IsMonomialCombination (d := d) (D := 2 * ell)
      (fun θ => (coordinateGaussianScore x θ) ^ ell) := by
  induction ell with
  | zero =>
      simpa using isMonomialCombination_const (d := d) (D := 0) 1
  | succ ell ih =>
      simpa [pow_succ, Nat.mul_succ] using
        ih.mul (coordinateGaussianScore_isMonomialCombination x)

/-- The exponential series in the Gaussian score, truncated after order `L`. -/
noncomputable def coordinateGaussianTruncatedScoreExp {d : ℕ} (L : ℕ)
    (x θ : Fin d → ℝ) : ℝ :=
  ∑ ell ∈ range (L + 1), (coordinateGaussianScore x θ) ^ ell / ell.factorial

/--
The Gaussian score exponential truncated after order `L` is a linear
combination of monomial coordinates of total degree at most `2 * L`.
-/
theorem coordinateGaussianTruncatedScoreExp_isMonomialCombination {d : ℕ}
    (L : ℕ) (x : Fin d → ℝ) :
    IsMonomialCombination (d := d) (D := 2 * L)
      (coordinateGaussianTruncatedScoreExp L x) := by
  have hterm : ∀ ell ∈ range (L + 1),
      IsMonomialCombination (d := d) (D := 2 * L)
        (fun θ => (coordinateGaussianScore x θ) ^ ell / ell.factorial) := by
    intro ell hell
    have hell_le : ell ≤ L := Nat.le_of_lt_succ (mem_range.mp hell)
    have hpadded :=
      (coordinateGaussianScore_pow_isMonomialCombination x ell).pad (2 * (L - ell))
    have hdegree : 2 * ell + 2 * (L - ell) = 2 * L := by omega
    rw [hdegree] at hpadded
    simpa [div_eq_mul_inv, mul_comm] using
      hpadded.smul ((ell.factorial : ℝ)⁻¹)
  change IsMonomialCombination (d := d) (D := 2 * L)
    (fun θ => ∑ ell ∈ range (L + 1),
      (coordinateGaussianScore x θ) ^ ell / ell.factorial)
  exact isMonomialCombination_finsetSum (range (L + 1))
    (fun ell θ => (coordinateGaussianScore x θ) ^ ell / ell.factorial) hterm

/-- The Carathéodory law matches the Gaussian-score Taylor polynomial at
every observation vector simultaneously.  Its slot count is
`choose (2*L+d) d + 1` by `finrank_monomialFeature`; unused slots have zero
mass. -/
theorem exists_finite_gaussian_truncated_score_matching
    {Θ : Type*} [MeasurableSpace Θ] {d : ℕ} (L : ℕ)
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Fin d → ℝ) (K : Set (Fin d → ℝ))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K)
    (hint : MeasureTheory.Integrable
      (fun a ↦ monomialFeature d (2 * L) (θ a)) μ) :
    ∃ (w : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) → ℝ)
      (θ' : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) →
        Fin d → ℝ),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1)) ∧
      (∀ i, θ' i ∈ K) ∧
      ∀ x : Fin d → ℝ,
        ∑ i, w i * coordinateGaussianTruncatedScoreExp L x (θ' i) =
          ∫ a, coordinateGaussianTruncatedScoreExp L x (θ a) ∂μ := by
  obtain ⟨w, θ', hw, hθ'K, hmom⟩ :=
    exists_finite_monomial_moment_matching μ θ K hKcompact hKnonempty hθK hint
  refine ⟨w, θ', hw, hθ'K, fun x ↦ ?_⟩
  exact (coordinateGaussianTruncatedScoreExp_isMonomialCombination L x).weighted_sum_eq_integral
    w θ' μ θ hint hmom

/-- Exact matching through degree `2*L` turns the two Taylor remainders into
the paper's `2 exp(B) B^(L+1)/(L+1)!` mixture approximation bound. -/
theorem gaussian_score_exp_average_error_of_moment_match
    {Θ : Type*} [MeasurableSpace Θ] {d L : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Fin d → ℝ)
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → Fin d → ℝ)
    (hw : w ∈ stdSimplex ℝ ι)
    (hint : MeasureTheory.Integrable
      (fun a ↦ monomialFeature d (2 * L) (θ a)) μ)
    (hmom : ∑ i, w i • monomialFeature d (2 * L) (z i) =
      ∫ a, monomialFeature d (2 * L) (θ a) ∂μ)
    (x : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hzB : ∀ i, |coordinateGaussianScore x (z i)| ≤ B)
    (hθB : ∀ᵐ a ∂μ, |coordinateGaussianScore x (θ a)| ≤ B)
    (hexp : MeasureTheory.Integrable
      (fun a ↦ Real.exp (coordinateGaussianScore x (θ a))) μ) :
    |(∑ i, w i * Real.exp (coordinateGaussianScore x (z i))) -
        ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ| ≤
      2 * (Real.exp B * B ^ (L + 1) / (L + 1).factorial) := by
  classical
  let trunc : (Fin d → ℝ) → ℝ := coordinateGaussianTruncatedScoreExp L x
  let R : ℝ := Real.exp B * B ^ (L + 1) / (L + 1).factorial
  have htruncPoly : IsMonomialCombination (d := d) (D := 2 * L) trunc :=
    coordinateGaussianTruncatedScoreExp_isMonomialCombination L x
  have htruncInt : MeasureTheory.Integrable (fun a ↦ trunc (θ a)) μ :=
    htruncPoly.integrable_comp_of_feature μ θ hint
  have hpoly : ∑ i, w i * trunc (z i) = ∫ a, trunc (θ a) ∂μ :=
    htruncPoly.weighted_sum_eq_integral w z μ θ hint hmom
  have hfinite :
      |(∑ i, w i * Real.exp (coordinateGaussianScore x (z i))) -
          ∑ i, w i * trunc (z i)| ≤ R := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i, (w i * Real.exp (coordinateGaussianScore x (z i)) -
          w i * trunc (z i))| ≤
          ∑ i, |w i * Real.exp (coordinateGaussianScore x (z i)) -
            w i * trunc (z i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, w i *
          |Real.exp (coordinateGaussianScore x (z i)) - trunc (z i)| := by
            apply Fintype.sum_congr
            intro i
            rw [← mul_sub, abs_mul, abs_of_nonneg (hw.1 i)]
      _ ≤ ∑ i, w i * R := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left
              (real_exp_taylor_remainder_bound L hB (hzB i)) (hw.1 i)
      _ = R := by rw [← Finset.sum_mul, hw.2, one_mul]
  have hintegral :
      |(∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ) -
          ∫ a, trunc (θ a) ∂μ| ≤ R := by
    rw [← MeasureTheory.integral_sub hexp htruncInt]
    have hnorm := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := μ) (C := R) (f := fun a ↦
        Real.exp (coordinateGaussianScore x (θ a)) - trunc (θ a))
      (hθB.mono fun a ha ↦ real_exp_taylor_remainder_bound L hB ha)
    simpa only [Real.norm_eq_abs, MeasureTheory.probReal_univ, mul_one] using hnorm
  have hdecomp :
      (∑ i, w i * Real.exp (coordinateGaussianScore x (z i))) -
          ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ =
        ((∑ i, w i * Real.exp (coordinateGaussianScore x (z i))) -
          ∑ i, w i * trunc (z i)) +
        ((∫ a, trunc (θ a) ∂μ) -
          ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ) := by
    rw [hpoly]
    ring
  rw [hdecomp]
  calc
    |_ + _| ≤
        |(∑ i, w i * Real.exp (coordinateGaussianScore x (z i))) -
          ∑ i, w i * trunc (z i)| +
        |(∫ a, trunc (θ a) ∂μ) -
          ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ| := abs_add_le _ _
    _ ≤ R + R := add_le_add hfinite (by simpa [abs_sub_comm] using hintegral)
    _ = 2 * R := by ring

/-- A probability average of exponentials whose scores are bounded below by
`-B` is at least `exp (-B)`. -/
theorem exp_neg_bound_le_gaussian_score_average
    {Θ : Type*} [MeasurableSpace Θ] {d : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Fin d → ℝ) (x : Fin d → ℝ) {B : ℝ}
    (hθB : ∀ᵐ a ∂μ, |coordinateGaussianScore x (θ a)| ≤ B)
    (hexp : MeasureTheory.Integrable
      (fun a ↦ Real.exp (coordinateGaussianScore x (θ a))) μ) :
    Real.exp (-B) ≤ ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ := by
  have hmono : (fun _ : Θ ↦ Real.exp (-B)) ≤ᵐ[μ]
      (fun a ↦ Real.exp (coordinateGaussianScore x (θ a))) := by
    filter_upwards [hθB] with a ha
    exact Real.exp_le_exp.mpr (neg_le_of_abs_le ha)
  have h := MeasureTheory.integral_mono_ae
    (MeasureTheory.integrable_const (c := Real.exp (-B))) hexp hmono
  simpa only [MeasureTheory.integral_const, MeasureTheory.probReal_univ,
    one_smul] using h

/-- Dividing the absolute Taylor error by an `exp (-B)` lower bound gives
the relative `2 exp(2B)` factor used in the manuscript. -/
theorem relative_error_of_exp_lower_bound {a b B r : ℝ}
    (hlower : Real.exp (-B) ≤ b)
    (herror : |a - b| ≤ 2 * Real.exp B * r) :
    |a / b - 1| ≤ 2 * Real.exp (2 * B) * r := by
  have hb : 0 < b := (Real.exp_pos (-B)).trans_le hlower
  have hnonneg : 0 ≤ 2 * Real.exp B * r := (abs_nonneg (a - b)).trans herror
  rw [div_sub_one hb.ne', abs_div, abs_of_pos hb]
  calc
    |a - b| / b ≤ (2 * Real.exp B * r) / Real.exp (-B) :=
      div_le_div₀ hnonneg herror (Real.exp_pos (-B)) hlower
    _ = 2 * Real.exp (2 * B) * r := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      calc
        2 * Real.exp B * r * Real.exp (- -B) =
            2 * (Real.exp B * Real.exp (- -B)) * r := by ring
        _ = 2 * Real.exp (2 * B) * r := by
          rw [← Real.exp_add]
          congr 3 <;> ring

/-- Compact-support specialization: a probability mixture admits a finite
moment-matching mixture with the uniform local exponential-score error from
the finite-net proof. -/
theorem exists_finite_gaussian_score_exp_approximation
    {Θ : Type*} [MeasurableSpace Θ] {d L : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Fin d → ℝ) (K : Set (Fin d → ℝ))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K)
    (hint : MeasureTheory.Integrable
      (fun a ↦ monomialFeature d (2 * L) (θ a)) μ)
    (x : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hscore : ∀ u ∈ K, |coordinateGaussianScore x u| ≤ B)
    (hexp : MeasureTheory.Integrable
      (fun a ↦ Real.exp (coordinateGaussianScore x (θ a))) μ) :
    ∃ (w : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) → ℝ)
      (θ' : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) →
        Fin d → ℝ),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1)) ∧
      (∀ i, θ' i ∈ K) ∧
      |(∑ i, w i * Real.exp (coordinateGaussianScore x (θ' i))) -
          ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ| ≤
        2 * (Real.exp B * B ^ (L + 1) / (L + 1).factorial) := by
  obtain ⟨w, θ', hw, hθ'K, hmom⟩ :=
    exists_finite_monomial_moment_matching μ θ K hKcompact hKnonempty hθK hint
  refine ⟨w, θ', hw, hθ'K, ?_⟩
  apply gaussian_score_exp_average_error_of_moment_match μ θ w θ' hw hint hmom x hB
  · exact fun i ↦ hscore (θ' i) (hθ'K i)
  · filter_upwards [hθK] with a ha
    exact hscore (θ a) ha
  · exact hexp

/-- Relative form of the compact-support finite approximation.  This is the
displayed local bound in the proof of the simultaneous likelihood net. -/
theorem exists_finite_gaussian_score_exp_relative_approximation
    {Θ : Type*} [MeasurableSpace Θ] {d L : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Fin d → ℝ) (K : Set (Fin d → ℝ))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K)
    (hint : MeasureTheory.Integrable
      (fun a ↦ monomialFeature d (2 * L) (θ a)) μ)
    (x : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hscore : ∀ u ∈ K, |coordinateGaussianScore x u| ≤ B)
    (hexp : MeasureTheory.Integrable
      (fun a ↦ Real.exp (coordinateGaussianScore x (θ a))) μ) :
    ∃ (w : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) → ℝ)
      (θ' : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) →
        Fin d → ℝ),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1)) ∧
      (∀ i, θ' i ∈ K) ∧
      |(∑ i, w i * Real.exp (coordinateGaussianScore x (θ' i))) /
          (∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ) - 1| ≤
        2 * Real.exp (2 * B) * (B ^ (L + 1) / (L + 1).factorial) := by
  obtain ⟨w, θ', hw, hθ'K, habs⟩ :=
    exists_finite_gaussian_score_exp_approximation μ θ K hKcompact hKnonempty
      hθK hint x hB hscore hexp
  refine ⟨w, θ', hw, hθ'K, ?_⟩
  have hlower : Real.exp (-B) ≤
      ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ := by
    apply exp_neg_bound_le_gaussian_score_average μ θ x
    · filter_upwards [hθK] with a ha
      exact hscore (θ a) ha
    · exact hexp
  apply relative_error_of_exp_lower_bound hlower
  convert habs using 1 <;> ring

/-- Monomial evaluation on the Euclidean-space representation used by the NPMLE theorem. -/
def pointMonomialEval {d D : ℕ}
    (θ : Point d) (m : MonomialCoord d D) : ℝ :=
  monomialEval (fun i ↦ θ i) m

@[simp]
theorem pointMonomialEval_constant (d D : ℕ) (θ : Point d) :
    pointMonomialEval θ (constantCoord d D) = 1 :=
  monomialEval_constant d D (fun i ↦ θ i)

/-- The inner-product exponential Taylor polynomial uses exactly the
degree-at-most-`L` monomial coordinates appearing in Proposition 4.1. -/
theorem truncatedInnerExp_isPointMonomialCombination
    {d : ℕ} (L : ℕ) (x : Point d) :
    ∃ c : MonomialCoord d L → ℝ,
      ∀ θ : Point d,
        (∑ ell ∈ range (L + 1),
          (inner ℝ x θ) ^ ell / ell.factorial) =
            ∑ m, c m * pointMonomialEval θ m := by
  obtain ⟨c, hc⟩ :=
    coordinateTruncatedInnerExp_isMonomialCombination L (fun i ↦ x i)
  refine ⟨c, fun θ ↦ ?_⟩
  have hinner : inner ℝ x θ = coordinateDot (fun i ↦ x i) (fun i ↦ θ i) := by
    rw [coordinateDot, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [coordinateTruncatedInnerExp] at hc
  rw [hinner]
  exact hc (fun i ↦ θ i)

/--
The actual inner-product Gaussian Taylor polynomial is represented by the
`choose (2L+d) d` Euclidean monomial coordinates.
-/
theorem gaussianTruncatedScoreExp_isPointMonomialCombination
    {d : ℕ} (L : ℕ) (x : Point d) :
    ∃ c : MonomialCoord d (2 * L) → ℝ,
      ∀ θ : Point d,
        (∑ ell ∈ range (L + 1),
          (gaussianScore x θ) ^ ell / ell.factorial) =
            ∑ m, c m * pointMonomialEval θ m := by
  obtain ⟨c, hc⟩ :=
    coordinateGaussianTruncatedScoreExp_isMonomialCombination
      L (fun i ↦ x i)
  refine ⟨c, fun θ ↦ ?_⟩
  calc
    (∑ ell ∈ range (L + 1),
        (gaussianScore x θ) ^ ell / ell.factorial) =
        coordinateGaussianTruncatedScoreExp
          L (fun i ↦ x i) (fun i ↦ θ i) := by
            simp only [coordinateGaussianTruncatedScoreExp]
            rw [gaussianScore_eq_coordinateGaussianScore]
    _ = ∑ m, c m * monomialEval (fun i ↦ θ i) m :=
      hc (fun i ↦ θ i)
    _ = ∑ m, c m * pointMonomialEval θ m := rfl

/-- Native Euclidean-space form of the local finite-mixture approximation:
every compactly supported probability mixture has a discrete mixture with at
most `choose(2L+d,d)+1` slots and the paper's explicit relative Gaussian
score error at the observation `x`. -/
theorem exists_finite_gaussian_mixture_relative_approximation
    {Θ : Type*} [MeasurableSpace Θ] {d L : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Point d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K)
    (hint : MeasureTheory.Integrable
      (fun a ↦ monomialFeature d (2 * L) (fun i ↦ θ a i)) μ)
    (x : Point d) {B : ℝ} (hB : 0 ≤ B)
    (hscore : ∀ u ∈ K, |gaussianScore x u| ≤ B)
    (hexp : MeasureTheory.Integrable
      (fun a ↦ Real.exp (gaussianScore x (θ a))) μ) :
    ∃ (w : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) → ℝ)
      (θ' : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) → Point d),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1)) ∧
      (∀ i, θ' i ∈ K) ∧
      |(∑ i, w i * Real.exp (gaussianScore x (θ' i))) /
          (∫ a, Real.exp (gaussianScore x (θ a)) ∂μ) - 1| ≤
        2 * Real.exp (2 * B) * (B ^ (L + 1) / (L + 1).factorial) := by
  let toCoord : Point d → (Fin d → ℝ) := fun u i ↦ u i
  let Kc : Set (Fin d → ℝ) := toCoord '' K
  have htoCoord : Continuous toCoord := by
    unfold toCoord
    fun_prop
  have hKccompact : IsCompact Kc := hKcompact.image htoCoord
  have hKcnonempty : Kc.Nonempty := hKnonempty.image toCoord
  have hθKc : ∀ᵐ a ∂μ, toCoord (θ a) ∈ Kc := by
    filter_upwards [hθK] with a ha
    exact ⟨θ a, ha, rfl⟩
  have hscorec : ∀ u ∈ Kc,
      |coordinateGaussianScore (fun i ↦ x i) u| ≤ B := by
    rintro u ⟨z, hz, rfl⟩
    simpa only [toCoord, gaussianScore_eq_coordinateGaussianScore] using hscore z hz
  have hexpc : MeasureTheory.Integrable
      (fun a ↦ Real.exp
        (coordinateGaussianScore (fun i ↦ x i) (toCoord (θ a)))) μ := by
    apply hexp.congr
    exact Filter.Eventually.of_forall fun a ↦ by
      simpa only [toCoord] using
        congrArg Real.exp (gaussianScore_eq_coordinateGaussianScore x (θ a))
  obtain ⟨w, zc, hw, hzcK, hrel⟩ :=
    exists_finite_gaussian_score_exp_relative_approximation
      μ (fun a ↦ toCoord (θ a)) Kc hKccompact hKcnonempty hθKc hint
      (fun i ↦ x i) hB hscorec hexpc
  have hchoice : ∀ i, ∃ z, z ∈ K ∧ toCoord z = zc i := by
    intro i
    rcases hzcK i with ⟨z, hzK, hz⟩
    exact ⟨z, hzK, hz⟩
  choose θ' hθ'K hθ' using hchoice
  refine ⟨w, θ', hw, hθ'K, ?_⟩
  have hsum :
      (∑ i, w i * Real.exp
        (coordinateGaussianScore (fun j ↦ x j) (zc i))) =
        ∑ i, w i * Real.exp (gaussianScore x (θ' i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← hθ' i, ← gaussianScore_eq_coordinateGaussianScore]
  have hintEq :
      (∫ a, Real.exp
        (coordinateGaussianScore (fun i ↦ x i) (toCoord (θ a))) ∂μ) =
        ∫ a, Real.exp (gaussianScore x (θ a)) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun a ↦ by
      simpa only [toCoord] using
        (congrArg Real.exp (gaussianScore_eq_coordinateGaussianScore x (θ a))).symm
  rw [hsum, hintEq] at hrel
  exact hrel

/-- Density-level form of the finite-mixture approximation.  The common
centered Gaussian density cancels from the relative error, so the score
approximation above gives the same bound for the actual Gaussian kernels. -/
theorem exists_finite_gaussian_kernel_relative_approximation
    {Θ : Type*} [MeasurableSpace Θ] {d L : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Point d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K)
    (hint : MeasureTheory.Integrable
      (fun a ↦ monomialFeature d (2 * L) (fun i ↦ θ a i)) μ)
    (x : Point d) {B : ℝ} (hB : 0 ≤ B)
    (hscore : ∀ u ∈ K, |gaussianScore x u| ≤ B)
    (hexp : MeasureTheory.Integrable
      (fun a ↦ Real.exp (gaussianScore x (θ a))) μ) :
    ∃ (w : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) → ℝ)
      (θ' : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) → Point d),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1)) ∧
      (∀ i, θ' i ∈ K) ∧
      |(∑ i, w i * gaussianKernel d x (θ' i)) /
          (∫ a, gaussianKernel d x (θ a) ∂μ) - 1| ≤
        2 * Real.exp (2 * B) * (B ^ (L + 1) / (L + 1).factorial) := by
  obtain ⟨w, θ', hw, hθ'K, hrel⟩ :=
    exists_finite_gaussian_mixture_relative_approximation
      μ θ K hKcompact hKnonempty hθK hint x hB hscore hexp
  refine ⟨w, θ', hw, hθ'K, ?_⟩
  have hnum :
      (∑ i, w i * gaussianKernel d x (θ' i)) =
        gaussianDensity d x *
          ∑ i, w i * Real.exp (gaussianScore x (θ' i)) := by
    simp_rw [gaussianKernel_eq_density_mul_exp_score]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hden :
      (∫ a, gaussianKernel d x (θ a) ∂μ) =
        gaussianDensity d x *
          ∫ a, Real.exp (gaussianScore x (θ a)) ∂μ := by
    simp_rw [gaussianKernel_eq_density_mul_exp_score]
    exact MeasureTheory.integral_const_mul _ _
  rw [hnum, hden, mul_div_mul_left _ _ (ne_of_gt (gaussianDensity_pos d x))]
  exact hrel

/-- Uniform density-level approximation on an arbitrary observation set.
The discrete law is chosen once by matching the full monomial feature vector;
the concluding estimate therefore holds simultaneously for every `x ∈ X`. -/
theorem exists_finite_gaussian_kernel_uniform_relative_approximation
    {Θ : Type*} [MeasurableSpace Θ] {d L : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Point d) (K X : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K)
    (hint : MeasureTheory.Integrable
      (fun a ↦ monomialFeature d (2 * L) (fun i ↦ θ a i)) μ)
    {B : ℝ} (hB : 0 ≤ B)
    (hscore : ∀ x ∈ X, ∀ u ∈ K, |gaussianScore x u| ≤ B)
    (hexp : ∀ x ∈ X, MeasureTheory.Integrable
      (fun a ↦ Real.exp (gaussianScore x (θ a))) μ) :
    ∃ (w : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) → ℝ)
      (θ' : Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1) → Point d),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1)) ∧
      (∀ i, θ' i ∈ K) ∧
      ∀ x ∈ X,
        |(∑ i, w i * gaussianKernel d x (θ' i)) /
            (∫ a, gaussianKernel d x (θ a) ∂μ) - 1| ≤
          2 * Real.exp (2 * B) * (B ^ (L + 1) / (L + 1).factorial) := by
  let toCoord : Point d → (Fin d → ℝ) := fun u i ↦ u i
  let Kc : Set (Fin d → ℝ) := toCoord '' K
  have htoCoord : Continuous toCoord := by
    unfold toCoord
    fun_prop
  have hKccompact : IsCompact Kc := hKcompact.image htoCoord
  have hKcnonempty : Kc.Nonempty := hKnonempty.image toCoord
  have hθKc : ∀ᵐ a ∂μ, toCoord (θ a) ∈ Kc := by
    filter_upwards [hθK] with a ha
    exact ⟨θ a, ha, rfl⟩
  obtain ⟨w, zc, hw, hzcK, hmom⟩ :=
    exists_finite_monomial_moment_matching μ
      (fun a ↦ toCoord (θ a)) Kc hKccompact hKcnonempty hθKc hint
  have hchoice : ∀ i, ∃ z, z ∈ K ∧ toCoord z = zc i := by
    intro i
    rcases hzcK i with ⟨z, hzK, hz⟩
    exact ⟨z, hzK, hz⟩
  choose θ' hθ'K hθ' using hchoice
  refine ⟨w, θ', hw, hθ'K, ?_⟩
  intro x hx
  have hscorec : ∀ u ∈ Kc,
      |coordinateGaussianScore (fun i ↦ x i) u| ≤ B := by
    rintro u ⟨z, hz, rfl⟩
    simpa only [toCoord, gaussianScore_eq_coordinateGaussianScore] using
      hscore x hx z hz
  have hexpc : MeasureTheory.Integrable
      (fun a ↦ Real.exp
        (coordinateGaussianScore (fun i ↦ x i) (toCoord (θ a)))) μ := by
    apply (hexp x hx).congr
    exact Filter.Eventually.of_forall fun a ↦ by
      simpa only [toCoord] using
        congrArg Real.exp (gaussianScore_eq_coordinateGaussianScore x (θ a))
  have hzB : ∀ i,
      |coordinateGaussianScore (fun j ↦ x j) (zc i)| ≤ B :=
    fun i ↦ hscorec (zc i) (hzcK i)
  have hθB : ∀ᵐ a ∂μ,
      |coordinateGaussianScore (fun j ↦ x j) (toCoord (θ a))| ≤ B := by
    filter_upwards [hθKc] with a ha
    exact hscorec (toCoord (θ a)) ha
  have habs := gaussian_score_exp_average_error_of_moment_match
    μ (fun a ↦ toCoord (θ a)) w zc hw hint hmom
      (fun i ↦ x i) hB hzB hθB hexpc
  have hlower := exp_neg_bound_le_gaussian_score_average
    μ (fun a ↦ toCoord (θ a)) (fun i ↦ x i) hθB hexpc
  have herror :
      |(∑ i, w i * Real.exp
          (coordinateGaussianScore (fun j ↦ x j) (zc i))) -
        ∫ a, Real.exp
          (coordinateGaussianScore (fun j ↦ x j) (toCoord (θ a))) ∂μ| ≤
        2 * Real.exp B * (B ^ (L + 1) / (L + 1).factorial) := by
    calc
      _ ≤ 2 * (Real.exp B * B ^ (L + 1) / (L + 1).factorial) := habs
      _ = 2 * Real.exp B * (B ^ (L + 1) / (L + 1).factorial) := by ring
  have hrel := relative_error_of_exp_lower_bound
    (a := ∑ i, w i * Real.exp
      (coordinateGaussianScore (fun j ↦ x j) (zc i)))
    (b := ∫ a, Real.exp
      (coordinateGaussianScore (fun j ↦ x j) (toCoord (θ a))) ∂μ)
    (B := B) (r := B ^ (L + 1) / (L + 1).factorial) hlower herror
  have hsum :
      (∑ i, w i * Real.exp
        (coordinateGaussianScore (fun j ↦ x j) (zc i))) =
        ∑ i, w i * Real.exp (gaussianScore x (θ' i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← hθ' i, ← gaussianScore_eq_coordinateGaussianScore]
  have hintEq :
      (∫ a, Real.exp
        (coordinateGaussianScore (fun i ↦ x i) (toCoord (θ a))) ∂μ) =
        ∫ a, Real.exp (gaussianScore x (θ a)) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun a ↦ by
      simpa only [toCoord] using
        (congrArg Real.exp (gaussianScore_eq_coordinateGaussianScore x (θ a))).symm
  rw [hsum, hintEq] at hrel
  have hnum :
      (∑ i, w i * gaussianKernel d x (θ' i)) =
        gaussianDensity d x *
          ∑ i, w i * Real.exp (gaussianScore x (θ' i)) := by
    simp_rw [gaussianKernel_eq_density_mul_exp_score]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hden :
      (∫ a, gaussianKernel d x (θ a) ∂μ) =
        gaussianDensity d x *
          ∫ a, Real.exp (gaussianScore x (θ a)) ∂μ := by
    simp_rw [gaussianKernel_eq_density_mul_exp_score]
    exact MeasureTheory.integral_const_mul _ _
  rw [hnum, hden, mul_div_mul_left _ _ (ne_of_gt (gaussianDensity_pos d x))]
  exact hrel

end ReweightedNPMLE
