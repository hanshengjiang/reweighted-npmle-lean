import Mathlib.Algebra.Order.Floor.Ring
import ReweightedNPMLE.Gaussian

/-!
# Explicit finite nets for bounded Euclidean sets

This module implements the coordinate-cell construction used in the paper's
entropy argument.  A set contained in the radius-`S` Euclidean ball is split
into cells of coordinate width `ε / (d + 2)`.  Choosing one point of the set
from each occupied cell gives an internal `ε`-net with an explicit cardinality
bound.
-/

open scoped BigOperators

namespace ReweightedNPMLE

/-- Coordinate width in the explicit bounded-set location net.  The harmless
`d + 2` denominator gives a strict Euclidean error smaller than `ε` in every
dimension, including dimension zero. -/
noncomputable def boundedLocationCellWidth (d : ℕ) (ε : ℝ) : ℝ :=
  ε / (d + 2)

/-- Number of coordinate cells needed on the interval `[-S,S]`. -/
noncomputable def boundedLocationCellCount (d : ℕ) (S ε : ℝ) : ℕ :=
  Nat.floor (2 * S / boundedLocationCellWidth d ε) + 1

theorem boundedLocationCellWidth_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < boundedLocationCellWidth d ε := by
  unfold boundedLocationCellWidth
  positivity

/-- Each coordinate of a Euclidean point is bounded by its Euclidean norm. -/
theorem abs_coord_le_norm {d : ℕ} (u : Point d) (i : Fin d) :
    |u i| ≤ ‖u‖ := by
  have hsq : (u i) ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (u j)) (Finset.mem_univ i)
  nlinarith [abs_nonneg (u i), norm_nonneg u, sq_abs (u i)]

theorem boundedLocation_scaled_coord_nonneg {d : ℕ} {S ε : ℝ}
    (hε : 0 < ε) (u : Point d) (hu : ‖u‖ ≤ S) (i : Fin d) :
    0 ≤ (u i + S) / boundedLocationCellWidth d ε := by
  have hi := (abs_coord_le_norm u i).trans hu
  have hlo : -S ≤ u i := neg_le_of_abs_le hi
  exact div_nonneg (by linarith) (boundedLocationCellWidth_pos d hε).le

theorem boundedLocation_scaled_coord_le {d : ℕ} {S ε : ℝ}
    (hε : 0 < ε) (u : Point d) (hu : ‖u‖ ≤ S) (i : Fin d) :
    (u i + S) / boundedLocationCellWidth d ε ≤
      2 * S / boundedLocationCellWidth d ε := by
  have hi := (abs_coord_le_norm u i).trans hu
  have hup : u i ≤ S := (le_abs_self (u i)).trans hi
  exact div_le_div_of_nonneg_right (by linarith)
    (boundedLocationCellWidth_pos d hε).le

/-- Coordinate-cell code of a point in a bounded set. -/
noncomputable def boundedLocationCellCode {d : ℕ} {K : Set (Point d)}
    (S ε : ℝ) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (u : K) :
    Fin d → Fin (boundedLocationCellCount d S ε) := fun i =>
  ⟨Nat.floor (((u : Point d) i + S) / boundedLocationCellWidth d ε), by
    unfold boundedLocationCellCount
    exact Nat.lt_succ_of_le (Nat.floor_mono
      (boundedLocation_scaled_coord_le hε (u : Point d)
        (hKbound u u.property) i))⟩

/-- Points with the same coordinate-cell code are strictly closer than `ε`. -/
theorem norm_sub_lt_of_boundedLocationCellCode_eq
    {d : ℕ} {K : Set (Point d)} {S ε : ℝ} (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (u v : K)
    (hcode : boundedLocationCellCode S ε hε hKbound u =
      boundedLocationCellCode S ε hε hKbound v) :
    ‖(u : Point d) - (v : Point d)‖ < ε := by
  have hcoord : ∀ i : Fin d,
      |((u : Point d) - (v : Point d)) i| <
        boundedLocationCellWidth d ε := by
    intro i
    change |(u : Point d) i - (v : Point d) i| <
      boundedLocationCellWidth d ε
    have hfloorNat :
        Nat.floor ((((u : Point d) i + S) /
            boundedLocationCellWidth d ε)) =
          Nat.floor ((((v : Point d) i + S) /
            boundedLocationCellWidth d ε)) := by
      exact Fin.ext_iff.mp (congrFun hcode i)
    have hu0 := boundedLocation_scaled_coord_nonneg hε (u : Point d)
      (hKbound u u.property) i
    have hv0 := boundedLocation_scaled_coord_nonneg hε (v : Point d)
      (hKbound v v.property) i
    have hfloorInt :
        ⌊(((u : Point d) i + S) / boundedLocationCellWidth d ε)⌋ =
          ⌊(((v : Point d) i + S) / boundedLocationCellWidth d ε)⌋ := by
      rw [← Int.natCast_floor_eq_floor hu0,
        ← Int.natCast_floor_eq_floor hv0]
      exact_mod_cast hfloorNat
    have hscaled := Int.abs_sub_lt_one_of_floor_eq_floor hfloorInt
    have hwpos := boundedLocationCellWidth_pos d hε
    have heq :
        ((u : Point d) i + S) / boundedLocationCellWidth d ε -
            ((v : Point d) i + S) / boundedLocationCellWidth d ε =
          ((u : Point d) i - (v : Point d) i) /
            boundedLocationCellWidth d ε := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hwpos, div_lt_one hwpos] at hscaled
    exact hscaled
  have hsum :
      ∑ i : Fin d, (((u : Point d) - (v : Point d)) i) ^ 2 ≤
        ∑ _i : Fin d, (boundedLocationCellWidth d ε) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hi := (sq_le_sq₀ (abs_nonneg _)
      (boundedLocationCellWidth_pos d hε).le).2 (hcoord i).le
    simpa only [sq_abs] using hi
  have hnormsq : ‖(u : Point d) - (v : Point d)‖ ^ 2 ≤
      (d : ℝ) * (boundedLocationCellWidth d ε) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa using hsum
  have hnorm : ‖(u : Point d) - (v : Point d)‖ ≤
      Real.sqrt d * boundedLocationCellWidth d ε := by
    have hsqrt0 : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have hsqrtd : (Real.sqrt (d : ℝ)) ^ 2 = d :=
      Real.sq_sqrt (Nat.cast_nonneg d)
    have hrhs : 0 ≤ Real.sqrt d * boundedLocationCellWidth d ε :=
      mul_nonneg hsqrt0 (boundedLocationCellWidth_pos d hε).le
    apply (sq_le_sq₀ (norm_nonneg _) hrhs).1
    rw [mul_pow, hsqrtd]
    exact hnormsq
  have hsqrt : Real.sqrt d < (d : ℝ) + 2 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg d),
      Real.sqrt_nonneg (d : ℝ)]
  have hw : Real.sqrt d * boundedLocationCellWidth d ε < ε := by
    unfold boundedLocationCellWidth
    have hd : (0 : ℝ) < (d : ℝ) + 2 := by positivity
    calc
      Real.sqrt d * (ε / ((d : ℝ) + 2)) <
          ((d : ℝ) + 2) * (ε / ((d : ℝ) + 2)) := by
        gcongr
      _ = ε := by field_simp
  exact hnorm.trans_lt hw

/-- A representative in `K` for a cell.  Empty cells use an arbitrary point
of the nonempty set; duplicates are discarded when the finite net is formed. -/
noncomputable def boundedLocationRepresentative {d : ℕ} (K : Set (Point d))
    (hKnonempty : K.Nonempty) (S ε : ℝ) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S)
    (c : Fin d → Fin (boundedLocationCellCount d S ε)) : K := by
  classical
  exact if h : ∃ u : K,
      boundedLocationCellCode S ε hε hKbound u = c then h.choose
    else ⟨hKnonempty.choose, hKnonempty.choose_spec⟩

theorem boundedLocationRepresentative_code {d : ℕ} {K : Set (Point d)}
    (hKnonempty : K.Nonempty) {S ε : ℝ} (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (u : K) :
    boundedLocationCellCode S ε hε hKbound
        (boundedLocationRepresentative K hKnonempty S ε hε hKbound
          (boundedLocationCellCode S ε hε hKbound u)) =
      boundedLocationCellCode S ε hε hKbound u := by
  let h : ∃ v : K, boundedLocationCellCode S ε hε hKbound v =
      boundedLocationCellCode S ε hε hKbound u := ⟨u, rfl⟩
  rw [boundedLocationRepresentative, dif_pos h]
  exact h.choose_spec

/-- The explicit finite internal net of a nonempty bounded Euclidean set. -/
noncomputable def boundedLocationNet {d : ℕ} (K : Set (Point d))
    (hKnonempty : K.Nonempty) (S ε : ℝ) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) : Finset (Point d) := by
  classical
  exact (Finset.univ : Finset
      (Fin d → Fin (boundedLocationCellCount d S ε))).image
    (fun c ↦ (boundedLocationRepresentative K hKnonempty S ε hε
      hKbound c : Point d))

theorem boundedLocationNet_subset {d : ℕ} (K : Set (Point d))
    (hKnonempty : K.Nonempty) {S ε : ℝ} (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ↑(boundedLocationNet K hKnonempty S ε hε hKbound) ⊆ K := by
  classical
  intro u hu
  rw [Finset.mem_coe, boundedLocationNet, Finset.mem_image] at hu
  rcases hu with ⟨c, _hc, rfl⟩
  exact (boundedLocationRepresentative K hKnonempty S ε hε hKbound c).property

/-- Explicit polynomial cardinality bound for the internal location net. -/
theorem card_boundedLocationNet_le {d : ℕ} (K : Set (Point d))
    (hKnonempty : K.Nonempty) {S ε : ℝ} (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    (boundedLocationNet K hKnonempty S ε hε hKbound).card ≤
      (boundedLocationCellCount d S ε) ^ d := by
  classical
  calc
    (boundedLocationNet K hKnonempty S ε hε hKbound).card ≤
        (Finset.univ : Finset
          (Fin d → Fin (boundedLocationCellCount d S ε))).card := by
      exact Finset.card_image_le
    _ = (boundedLocationCellCount d S ε) ^ d := by simp

/-- Every point of `K` is within `ε` of a point of the explicit internal net. -/
theorem exists_mem_boundedLocationNet_norm_sub_le {d : ℕ}
    (K : Set (Point d)) (hKnonempty : K.Nonempty)
    {S ε : ℝ} (hε : 0 < ε) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S)
    (u : Point d) (hu : u ∈ K) :
    ∃ v ∈ boundedLocationNet K hKnonempty S ε hε hKbound,
      ‖u - v‖ ≤ ε := by
  classical
  let uK : K := ⟨u, hu⟩
  let c := boundedLocationCellCode S ε hε hKbound uK
  let vK := boundedLocationRepresentative K hKnonempty S ε hε hKbound c
  refine ⟨(vK : Point d), ?_, ?_⟩
  · rw [boundedLocationNet, Finset.mem_image]
    exact ⟨c, Finset.mem_univ c, rfl⟩
  · exact (norm_sub_lt_of_boundedLocationCellCode_eq hε hKbound uK vK
      (boundedLocationRepresentative_code hKnonempty hε hKbound uK).symm).le

end ReweightedNPMLE
