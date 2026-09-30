import Mathlib.Tactic

/-! # Sound exact rational interval arithmetic for finite report calculations

Expressions return no enclosure when a division denominator is not certified
strictly positive. Successful enclosures contain the actual real expression.
-/

namespace ReweightedNPMLE.NumericalStudy

set_option autoImplicit false

structure NumericalInterval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq

def NumericalInterval.Contains (I : NumericalInterval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

def NumericalInterval.point (q : ℚ) : NumericalInterval := ⟨q, q⟩

def NumericalInterval.add (I J : NumericalInterval) : NumericalInterval :=
  ⟨I.lower + J.lower, I.upper + J.upper⟩

def NumericalInterval.sub (I J : NumericalInterval) : NumericalInterval :=
  ⟨I.lower - J.upper, I.upper - J.lower⟩

def NumericalInterval.mul (I J : NumericalInterval) : NumericalInterval :=
  ⟨min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper)),
   max (max (I.lower * J.lower) (I.lower * J.upper))
    (max (I.upper * J.lower) (I.upper * J.upper))⟩

def NumericalInterval.inv (I : NumericalInterval) : NumericalInterval :=
  ⟨I.upper⁻¹, I.lower⁻¹⟩

theorem numerical_interval_add_sound {I J : NumericalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.add J).Contains (x + y) := by
  simp only [NumericalInterval.Contains, NumericalInterval.add, Rat.cast_add] at *
  constructor <;> linarith

theorem numerical_interval_sub_sound {I J : NumericalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.sub J).Contains (x - y) := by
  simp only [NumericalInterval.Contains, NumericalInterval.sub, Rat.cast_sub] at *
  constructor <;> linarith

private theorem real_mul_interval_one {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) (c : ℝ) :
    min (a * c) (b * c) ≤ x * c ∧ x * c ≤ max (a * c) (b * c) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hc),
      (mul_le_mul_of_nonneg_right hx.2 hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hc),
      (mul_le_mul_of_nonpos_right hx.1 hc).trans (le_max_left _ _)⟩

theorem numerical_interval_mul_sound {I J : NumericalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (I.mul J).Contains (x * y) := by
  have h := real_mul_interval_one hx y
  have ha := real_mul_interval_one hy (I.lower : ℝ)
  have hb := real_mul_interval_one hy (I.upper : ℝ)
  simp only [NumericalInterval.Contains, NumericalInterval.mul, Rat.cast_min,
    Rat.cast_max, Rat.cast_mul]
  have ha' : min ((I.lower : ℝ) * J.lower) ((I.lower : ℝ) * J.upper) ≤ (I.lower : ℝ) * y ∧
      (I.lower : ℝ) * y ≤ max ((I.lower : ℝ) * J.lower) ((I.lower : ℝ) * J.upper) := by
    simpa only [mul_comm] using ha
  have hb' : min ((I.upper : ℝ) * J.lower) ((I.upper : ℝ) * J.upper) ≤ (I.upper : ℝ) * y ∧
      (I.upper : ℝ) * y ≤ max ((I.upper : ℝ) * J.lower) ((I.upper : ℝ) * J.upper) := by
    simpa only [mul_comm] using hb
  constructor
  · exact (le_min ((min_le_left _ _).trans ha'.1) ((min_le_right _ _).trans hb'.1)).trans h.1
  · exact h.2.trans (max_le (ha'.2.trans (le_max_left _ _)) (hb'.2.trans (le_max_right _ _)))

theorem numerical_interval_inv_sound {I : NumericalInterval} {x : ℝ}
    (hx : I.Contains x) (hpos : 0 < I.lower) : I.inv.Contains x⁻¹ := by
  have hl : (0 : ℝ) < I.lower := by exact_mod_cast hpos
  have hxp : 0 < x := hl.trans_le hx.1
  have hu : (0 : ℝ) < I.upper := hxp.trans_le hx.2
  simp only [NumericalInterval.Contains, NumericalInterval.inv, Rat.cast_inv]
  exact ⟨(inv_le_inv₀ hu hxp).2 hx.2, (inv_le_inv₀ hxp hl).2 hx.1⟩

inductive NumericalExpr where
  | constant : ℚ → NumericalExpr
  | input : Nat → NumericalExpr
  | add : NumericalExpr → NumericalExpr → NumericalExpr
  | sub : NumericalExpr → NumericalExpr → NumericalExpr
  | mul : NumericalExpr → NumericalExpr → NumericalExpr
  | div : NumericalExpr → NumericalExpr → NumericalExpr

noncomputable def NumericalExpr.eval (values : Nat → ℝ) : NumericalExpr → ℝ
  | .constant q => q
  | .input i => values i
  | .add a b => a.eval values + b.eval values
  | .sub a b => a.eval values - b.eval values
  | .mul a b => a.eval values * b.eval values
  | .div a b => a.eval values / b.eval values

def NumericalExpr.enclosure (intervals : Nat → NumericalInterval) : NumericalExpr → Option NumericalInterval
  | .constant q => some (.point q)
  | .input i => some (intervals i)
  | .add a b => match a.enclosure intervals, b.enclosure intervals with
    | some I, some J => some (I.add J)
    | _, _ => none
  | .sub a b => match a.enclosure intervals, b.enclosure intervals with
    | some I, some J => some (I.sub J)
    | _, _ => none
  | .mul a b => match a.enclosure intervals, b.enclosure intervals with
    | some I, some J => some (I.mul J)
    | _, _ => none
  | .div a b => match a.enclosure intervals, b.enclosure intervals with
    | some I, some J => if 0 < J.lower then some (I.mul J.inv) else none
    | _, _ => none

theorem numerical_expression_enclosure_sound (e : NumericalExpr)
    (values : Nat → ℝ) (intervals : Nat → NumericalInterval)
    (hv : ∀ i, (intervals i).Contains (values i)) {I : NumericalInterval}
    (he : e.enclosure intervals = some I) : I.Contains (e.eval values) := by
  induction e generalizing I with
  | constant q =>
    simp only [NumericalExpr.enclosure, Option.some.injEq] at he
    subst I
    exact ⟨le_rfl, le_rfl⟩
  | input i =>
    simp only [NumericalExpr.enclosure, Option.some.injEq] at he
    subst I
    exact hv i
  | add a b iha ihb =>
    cases ha : a.enclosure intervals <;> cases hb : b.enclosure intervals <;>
      simp [NumericalExpr.enclosure, ha, hb] at he
    subst I
    exact numerical_interval_add_sound (iha ha) (ihb hb)
  | sub a b iha ihb =>
    cases ha : a.enclosure intervals <;> cases hb : b.enclosure intervals <;>
      simp [NumericalExpr.enclosure, ha, hb] at he
    subst I
    exact numerical_interval_sub_sound (iha ha) (ihb hb)
  | mul a b iha ihb =>
    cases ha : a.enclosure intervals <;> cases hb : b.enclosure intervals <;>
      simp [NumericalExpr.enclosure, ha, hb] at he
    subst I
    exact numerical_interval_mul_sound (iha ha) (ihb hb)
  | div a b iha ihb =>
    cases ha : a.enclosure intervals <;> cases hb : b.enclosure intervals <;>
      simp [NumericalExpr.enclosure, ha, hb] at he
    rcases he with ⟨hpos, he⟩
    subst I
    simpa only [NumericalExpr.eval, div_eq_mul_inv] using
      numerical_interval_mul_sound (iha ha) (numerical_interval_inv_sound (ihb hb) hpos)

theorem numerical_division_enclosure_denominator_positive (a b : NumericalExpr)
    (values : Nat → ℝ) (intervals : Nat → NumericalInterval)
    (hv : ∀ i, (intervals i).Contains (values i)) {I : NumericalInterval}
    (he : (NumericalExpr.div a b).enclosure intervals = some I) : 0 < b.eval values := by
  cases ha : a.enclosure intervals <;> cases hb : b.enclosure intervals <;>
    simp [NumericalExpr.enclosure, ha, hb] at he
  have hp : (0 : ℝ) < _ := (Rat.cast_pos (K := ℝ)).2 he.1
  exact hp.trans_le (numerical_expression_enclosure_sound b values intervals hv hb).1

end ReweightedNPMLE.NumericalStudy
