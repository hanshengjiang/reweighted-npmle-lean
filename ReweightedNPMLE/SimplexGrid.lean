import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic
import ReweightedNPMLE.Weights

/-!
# Finite simplex-grid rounding

The deterministic denominator-grid construction used to discretize the
Carathéodory mixture weights in the likelihood net.
-/

open scoped BigOperators

namespace ReweightedNPMLE

/-- Round a nonnegative real down to the nearest multiple of `1 / M`. -/
noncomputable def nonnegativeGridFloor (M : ℕ) (x : ℝ) : ℝ :=
  (⌊(M : ℝ) * x⌋₊ : ℝ) / M

theorem nonnegativeGridFloor_nonneg (M : ℕ) (x : ℝ) :
    0 ≤ nonnegativeGridFloor M x := by
  unfold nonnegativeGridFloor
  positivity

theorem nonnegativeGridFloor_le {M : ℕ} (hM : 0 < M)
    {x : ℝ} (hx : 0 ≤ x) :
    nonnegativeGridFloor M x ≤ x := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  rw [nonnegativeGridFloor, div_le_iff₀ hMreal]
  simpa only [mul_comm] using Nat.floor_le (mul_nonneg hMreal.le hx)

theorem sub_nonnegativeGridFloor_lt {M : ℕ} (hM : 0 < M)
    (x : ℝ) :
    x - nonnegativeGridFloor M x < 1 / M := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  rw [sub_lt_iff_lt_add]
  calc
    x = ((M : ℝ) * x) / M := by field_simp
    _ < ((⌊(M : ℝ) * x⌋₊ : ℝ) + 1) / M :=
      div_lt_div_of_pos_right (Nat.lt_floor_add_one ((M : ℝ) * x)) hMreal
    _ = 1 / M + nonnegativeGridFloor M x := by
      rw [nonnegativeGridFloor, add_div]
      ring

/-- Round every coordinate except the last down to the denominator-`M` grid;
the last coordinate receives the remaining mass. -/
noncomputable def simplexGridRound (k M : ℕ)
    (w : Fin (k + 1) → ℝ) : Fin (k + 1) → ℝ :=
  fun i ↦ if i = Fin.last k then
      1 - ∑ j ∈ (Finset.univ.erase (Fin.last k)), nonnegativeGridFloor M (w j)
    else nonnegativeGridFloor M (w i)

theorem simplexGridRound_apply_of_ne {k M : ℕ}
    (w : Fin (k + 1) → ℝ) {i : Fin (k + 1)} (hi : i ≠ Fin.last k) :
    simplexGridRound k M w i = nonnegativeGridFloor M (w i) := by
  simp [simplexGridRound, hi]

@[simp]
theorem simplexGridRound_apply_last {k M : ℕ}
    (w : Fin (k + 1) → ℝ) :
    simplexGridRound k M w (Fin.last k) =
      1 - ∑ j ∈ (Finset.univ.erase (Fin.last k)),
        nonnegativeGridFloor M (w j) := by
  simp [simplexGridRound]

theorem sum_simplexGridRound {k M : ℕ} (w : Fin (k + 1) → ℝ) :
    ∑ i, simplexGridRound k M w i = 1 := by
  let last := Fin.last k
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ last)]
  have hsum :
      (∑ i ∈ Finset.univ.erase last, simplexGridRound k M w i) =
        ∑ i ∈ Finset.univ.erase last, nonnegativeGridFloor M (w i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact simplexGridRound_apply_of_ne w (Finset.ne_of_mem_erase hi)
  rw [hsum]
  simp only [last, simplexGridRound_apply_last]
  ring

theorem simplexGridRound_nonneg {k M : ℕ} (hM : 0 < M)
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) (i : Fin (k + 1)) :
    0 ≤ simplexGridRound k M w i := by
  by_cases hi : i = Fin.last k
  · subst i
    rw [simplexGridRound_apply_last]
    have hroundsum :
        ∑ j ∈ Finset.univ.erase (Fin.last k), nonnegativeGridFloor M (w j) ≤
          ∑ j ∈ Finset.univ.erase (Fin.last k), w j := by
      apply Finset.sum_le_sum
      intro j _
      exact nonnegativeGridFloor_le hM (hw j)
    have hdecomp :
        (∑ j ∈ Finset.univ.erase (Fin.last k), w j) + w (Fin.last k) = 1 := by
      calc
        (∑ j ∈ Finset.univ.erase (Fin.last k), w j) + w (Fin.last k) =
            ∑ j ∈ (Finset.univ : Finset (Fin (k + 1))), w j :=
          Finset.sum_erase_add Finset.univ w (Finset.mem_univ (Fin.last k))
        _ = 1 := by simpa using hwsum
    have hsum_le_one :
        (∑ j ∈ Finset.univ.erase (Fin.last k), w j) ≤ 1 := by
      linarith [hw (Fin.last k)]
    exact sub_nonneg.mpr (hroundsum.trans hsum_le_one)
  · rw [simplexGridRound_apply_of_ne w hi]
    exact nonnegativeGridFloor_nonneg M (w i)

/-- The denominator-grid rounding error in `ℓ¹` is at most `2k/M` for a
simplex with `k+1` slots. -/
theorem sum_abs_simplexGridRound_sub_le {k M : ℕ} (hM : 0 < M)
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) :
    ∑ i, |simplexGridRound k M w i - w i| ≤
      2 * k / M := by
  let last := Fin.last k
  let E := ∑ i ∈ Finset.univ.erase last,
    (w i - nonnegativeGridFloor M (w i))
  have herr_nonneg (i : Fin (k + 1)) :
      0 ≤ w i - nonnegativeGridFloor M (w i) :=
    sub_nonneg.mpr (nonnegativeGridFloor_le hM (hw i))
  have hlast : simplexGridRound k M w last - w last = E := by
    have hdecomp :
        (∑ i ∈ Finset.univ.erase last, w i) + w last = 1 := by
      calc
        (∑ i ∈ Finset.univ.erase last, w i) + w last =
            ∑ i ∈ (Finset.univ : Finset (Fin (k + 1))), w i :=
          Finset.sum_erase_add Finset.univ w (Finset.mem_univ last)
        _ = 1 := by simpa using hwsum
    rw [show simplexGridRound k M w last =
        1 - ∑ i ∈ Finset.univ.erase last,
          nonnegativeGridFloor M (w i) by
      simp only [last, simplexGridRound_apply_last]]
    dsimp only [E]
    rw [Finset.sum_sub_distrib]
    linarith
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact Finset.sum_nonneg fun i _ ↦ herr_nonneg i
  have hl1eq :
      (∑ i, |simplexGridRound k M w i - w i|) = 2 * E := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ last)]
    have herase :
        (∑ i ∈ Finset.univ.erase last,
          |simplexGridRound k M w i - w i|) = E := by
      dsimp only [E]
      apply Finset.sum_congr rfl
      intro i hi
      rw [simplexGridRound_apply_of_ne w (Finset.ne_of_mem_erase hi)]
      rw [abs_sub_comm, abs_of_nonneg (herr_nonneg i)]
    rw [herase, hlast, abs_of_nonneg hE]
    ring
  rw [hl1eq]
  have hEbound : E ≤ k * (1 / (M : ℝ)) := by
    dsimp only [E]
    calc
      (∑ i ∈ Finset.univ.erase last,
          (w i - nonnegativeGridFloor M (w i))) ≤
          ∑ _i ∈ Finset.univ.erase last, (1 / (M : ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        exact (sub_nonnegativeGridFloor_lt hM (w i)).le
      _ = k * (1 / (M : ℝ)) := by simp [last]
  calc
    2 * E ≤ 2 * (k * (1 / (M : ℝ))) :=
      mul_le_mul_of_nonneg_left hEbound (by norm_num)
    _ = 2 * k / M := by ring

/-- A simplex coordinate is at most one. -/
theorem simplex_coordinate_le_one {k : ℕ} (w : Fin (k + 1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (i : Fin (k + 1)) :
    w i ≤ 1 := by
  calc
    w i ≤ ∑ j, w j :=
      Finset.single_le_sum (fun j _ ↦ hw j) (Finset.mem_univ i)
    _ = 1 := hwsum

/-- The integer numerator obtained by rounding a simplex coordinate down is
bounded by the grid denominator. -/
theorem nonnegativeGridNumerator_le {M : ℕ} {x : ℝ}
    (hx1 : x ≤ 1) :
    ⌊(M : ℝ) * x⌋₊ ≤ M := by
  apply Nat.floor_le_of_le
  exact mul_le_of_le_one_right (Nat.cast_nonneg M) hx1

/-- Delete the last coordinate from a finite sum. -/
theorem sum_erase_last_eq_sum_castSucc {k : ℕ} (f : Fin (k + 1) → ℝ) :
    ∑ i ∈ Finset.univ.erase (Fin.last k), f i =
      ∑ i : Fin k, f i.castSucc := by
  have herase := Finset.sum_erase_add
    (Finset.univ : Finset (Fin (k + 1))) f (Finset.mem_univ (Fin.last k))
  rw [Fin.sum_univ_castSucc] at herase
  exact add_right_cancel herase

/-- A point in the denominator-`M` simplex weight grid.  The first `k`
coordinates are grid multiples; the final coordinate receives the residual,
so every grid point has total mass one. -/
noncomputable def simplexGridPoint (k M : ℕ)
    (a : Fin k → Fin (M + 1)) : Fin (k + 1) → ℝ :=
  Fin.snoc (fun i ↦ (a i : ℝ) / M)
    (1 - ∑ i, (a i : ℝ) / M)

theorem sum_simplexGridPoint (k M : ℕ) (a : Fin k → Fin (M + 1)) :
    ∑ i, simplexGridPoint k M a i = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp [simplexGridPoint]

/-- The finite denominator-`M` grid of simplex weights with `k+1` slots. -/
noncomputable def simplexWeightGrid (k M : ℕ) :
    Finset (Fin (k + 1) → ℝ) :=
  Finset.univ.image (simplexGridPoint k M)

/-- The simplex grid has at most `(M+1)^k` points. -/
theorem card_simplexWeightGrid_le (k M : ℕ) :
    (simplexWeightGrid k M).card ≤ (M + 1) ^ k := by
  calc
    (simplexWeightGrid k M).card ≤
        (Finset.univ : Finset (Fin k → Fin (M + 1))).card := by
      exact Finset.card_image_le
    _ = (M + 1) ^ k := by simp

/-- The valid part of the ambient weight grid, obtained by retaining only
nonnegative vectors.  Every such vector already has total mass one. -/
noncomputable def validSimplexWeightGrid (k M : ℕ) :
    Finset (Fin (k + 1) → ℝ) :=
  (simplexWeightGrid k M).filter fun w ↦ ∀ i, 0 ≤ w i

theorem mem_validSimplexWeightGrid_iff {k M : ℕ}
    {w : Fin (k + 1) → ℝ} :
    w ∈ validSimplexWeightGrid k M ↔
      w ∈ simplexWeightGrid k M ∧ ∀ i, 0 ≤ w i := by
  simp [validSimplexWeightGrid]

theorem validSimplexWeightGrid_nonneg {k M : ℕ}
    {w : Fin (k + 1) → ℝ} (hw : w ∈ validSimplexWeightGrid k M) (i : Fin (k + 1)) :
    0 ≤ w i :=
  (mem_validSimplexWeightGrid_iff.mp hw).2 i

theorem validSimplexWeightGrid_sum {k M : ℕ}
    {w : Fin (k + 1) → ℝ} (hw : w ∈ validSimplexWeightGrid k M) :
    ∑ i, w i = 1 := by
  rcases (Finset.mem_image.mp
    (mem_validSimplexWeightGrid_iff.mp hw).1) with ⟨a, _, rfl⟩
  exact sum_simplexGridPoint k M a

theorem card_validSimplexWeightGrid_le (k M : ℕ) :
    (validSimplexWeightGrid k M).card ≤ (M + 1) ^ k :=
  (Finset.card_filter_le _ _).trans (card_simplexWeightGrid_le k M)

/-- Rounding a simplex vector produces a member of the finite weight grid. -/
theorem simplexGridRound_mem_simplexWeightGrid {k M : ℕ}
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) :
    simplexGridRound k M w ∈ simplexWeightGrid k M := by
  let a : Fin k → Fin (M + 1) := fun i ↦
    ⟨⌊(M : ℝ) * w i.castSucc⌋₊,
      Nat.lt_succ_of_le (nonnegativeGridNumerator_le
        (simplex_coordinate_le_one w hw hwsum i.castSucc))⟩
  rw [simplexWeightGrid, Finset.mem_image]
  refine ⟨a, Finset.mem_univ a, ?_⟩
  funext i
  cases i using Fin.lastCases with
  | last =>
      rw [simplexGridRound_apply_last, simplexGridPoint]
      simp only [Fin.snoc_last]
      congr 1
      rw [sum_erase_last_eq_sum_castSucc]
      simp only [a, nonnegativeGridFloor]
  | cast i =>
      rw [simplexGridRound_apply_of_ne w (Fin.castSucc_ne_last i),
        simplexGridPoint]
      simp only [Fin.snoc_castSucc, a, nonnegativeGridFloor]

theorem simplexGridRound_mem_validSimplexWeightGrid {k M : ℕ}
    (hM : 0 < M) (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) :
    simplexGridRound k M w ∈ validSimplexWeightGrid k M := by
  rw [mem_validSimplexWeightGrid_iff]
  exact ⟨simplexGridRound_mem_simplexWeightGrid w hw hwsum,
    simplexGridRound_nonneg hM w hw hwsum⟩

end ReweightedNPMLE
