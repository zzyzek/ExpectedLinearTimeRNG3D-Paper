/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Mathlib

@[expose] public section

/-!
# Definitions of the statements

Every definition that the statements of `Rng3d.output_iff` and `Rng3d.expected_linear` use, in
one module. The other files prove things about them. The Palomar Challenge (`Challenge.lean`)
is a verbatim copy of this module followed by the two statements.

The subject is the relative neighborhood graph (RNG) of `N` points in `ℝ^3`: `p` and `w` are
joined when no third point `u` has both `|p - u| < |p - w|` and `|w - u| < |p - w|` (no point
in the open lune of `p` and `w`).

The algorithm is SPoIF (Secure Posts on Increasing Fence), for points in the unit cube
`[0,1)^3`. It handles one point at a time, the anchor `p`.

* The points are binned into a grid of `n × n × n` cells, `n` the least natural number with
  `N ≤ n^3`, of cell side `ds = 1/n`.
* The fence of integer radius `r` is the cube centred at the centre `c` of the anchor's cell
  with half-width `(r + 1/2) ds`. It is the outer boundary of the cells at Chebyshev cell
  distance at most `r` from the anchor's cell, whose points have been collected.
* Each of the six faces of the fence is cut into four square patches (its quadrants), whose
  corners are the fence posts. A patch is secured at radius `r` when all four of its corners
  lie outside the unit cube, or when some collected point `q` has, for every corner `v`,
  `(q - p) · (v - q) > 0` and `(q - p) · (v - c) > 0`. The first inequality puts the patch
  strictly beyond the plane through `q` with normal `q - p`, so every point beyond the patch
  has `q` in its lune with `p`. The second keeps the patch beyond that plane when the fence
  grows.
* The radius grows from `0` until all 24 patches are secured or the whole grid is collected.
  The points collected so far are the candidates.
* More shells are collected, up to cell distance `⌈D/ds + 1/2⌉` with `D` the largest distance
  from the anchor to a candidate, so that the lune of the anchor with any candidate is covered.
* A candidate is reported when no collected point lies in its lune with the anchor.

The points are `N` independent uniform points of the unit cube, and the running time is the
operation count `totalCost`.
-/

open Finset

namespace Rng3d

/-! ### Points and the relative neighborhood graph -/

/-- Points of `ℝ^3`. -/
abbrev V := Fin 3 → ℝ

/-- Squared Euclidean distance. -/
def dd (a b : V) : ℝ := (a - b) ⬝ᵥ (a - b)

/-- Euclidean distance. -/
noncomputable def ed (a b : V) : ℝ := Real.sqrt (dd a b)

/-- `u` lies in the open lune of `p` and `w`, so it blocks the edge between `p` and `w`. -/
def blocks (p w u : V) : Prop := dd p u < dd p w ∧ dd w u < dd p w

/-- The half-open unit cube `[0,1)^3`, the domain of the points. -/
def unitCube : Set V := {y | ∀ m, 0 ≤ y m ∧ y m < 1}

variable {N : ℕ}

/-- `i` and `k` are joined in the relative neighborhood graph of the points `x`: they are
different indices and no other point lies in the open lune of `x i` and `x k`. -/
def isRNGEdge (x : Fin N → V) (i k : Fin N) : Prop :=
  i ≠ k ∧ ∀ j, j ≠ i → j ≠ k → ¬ blocks (x i) (x k) (x j)

/-! ### The grid -/

open Classical

lemma exists_grid (N : ℕ) : ∃ n : ℕ, N ≤ n ^ 3 :=
  ⟨N, by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ 3 := Nat.pow_le_pow_right h (by norm_num)⟩

/-- Grid cells per side: the least `n` with `N ≤ n^3`, which is `⌈N^{1/3}⌉`. -/
noncomputable def gridN (N : ℕ) : ℕ := Nat.find (exists_grid N)

/-- Side length of a grid cell. -/
noncomputable def ds (N : ℕ) : ℝ := 1 / (gridN N : ℝ)

/-- Integer cell coordinates of a point. -/
noncomputable def cellOf (N : ℕ) (y : V) : Fin 3 → ℤ :=
  fun m => ⌊(gridN N : ℝ) * y m⌋

/-- Chebyshev distance between the cells of two points. -/
noncomputable def cheb (N : ℕ) (y z : V) : ℕ :=
  Finset.univ.sup fun m => (cellOf N y m - cellOf N z m).natAbs

/-- Centre of the cell of `y`. -/
noncomputable def center (N : ℕ) (y : V) : V :=
  fun m => ((cellOf N y m : ℝ) + 1 / 2) * ds N

/-- Half-width of the fence of integer radius `r`. -/
noncomputable def hR (N : ℕ) (r : ℕ) : ℝ := ((r : ℝ) + 1 / 2) * ds N

/-- The points other than the anchor `i` in cells at Chebyshev distance at most `r` from the
anchor's cell. These are the points collected when the fence has radius `r`. -/
noncomputable def Q (x : Fin N → V) (i : Fin N) (r : ℕ) : Finset (Fin N) :=
  univ.filter fun j => j ≠ i ∧ cheb N (x j) (x i) ≤ r

/-! ### Fence patches -/

/-- A patch of the fence: the face axis `P.1`, the side `P.2 P.1` of the face along that axis,
and the quadrant of the face, given by the sides `P.2 m` along the two other axes `m`. There
are `3 · 8 = 24` patches. -/
abbrev Patch := Fin 3 × (Fin 3 → Bool)

/-- The sign `+1` or `-1` of a side. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- A corner of a patch, relative to the fence centre, in units of the fence half-width. Along
the face axis the coordinate is `±1`. Along each other axis `m` the corner is on the midline of
the face (`κ m = false`, coordinate `0`) or on the edge of the face (`κ m = true`, coordinate
`±1`). The four corners of a patch are the values over all `κ`. -/
def cornerDir (P : Patch) (κ : Fin 3 → Bool) : V :=
  fun m => if m = P.1 then sgn (P.2 m) else if κ m then sgn (P.2 m) else 0

/-- A corner (fence post) of patch `P` of the fence of radius `r` of anchor `i`. -/
noncomputable def corner (x : Fin N → V) (i : Fin N) (r : ℕ) (P : Patch)
    (κ : Fin 3 → Bool) : V :=
  center N (x i) + hR N r • cornerDir P κ

/-- Every corner of the patch is outside the unit cube. -/
def OOB (x : Fin N → V) (i : Fin N) (r : ℕ) (P : Patch) : Prop :=
  ∀ κ, corner x i r P κ ∉ unitCube

/-- The point `j` secures patch `P` of the fence of radius `r` of anchor `i`: every corner `v`
is strictly beyond the plane through `x j` with normal `x j - x i`, and `v - c` has positive
inner product with that normal, `c` being the fence centre. -/
def securesBy (x : Fin N → V) (i : Fin N) (r : ℕ) (P : Patch) (j : Fin N) :
    Prop :=
  ∀ κ, 0 < (x j - x i) ⬝ᵥ (corner x i r P κ - x j) ∧
    0 < (x j - x i) ⬝ᵥ (hR N r • cornerDir P κ)

/-- Patch `P` has been secured at some radius `r' ≤ r`, by being outside the unit cube or by a
point collected at radius `r'`. -/
def securedAt (x : Fin N → V) (i : Fin N) (r : ℕ) (P : Patch) : Prop :=
  ∃ r' ≤ r, OOB x i r' P ∨ ∃ j ∈ Q x i r', securesBy x i r' P j

/-- All 24 patches have been secured by radius `r`. -/
def allSecured (x : Fin N → V) (i : Fin N) (r : ℕ) : Prop :=
  ∀ P, securedAt x i r P

/-! ### The procedure at one anchor -/

lemma exists_stop (x : Fin N → V) (i : Fin N) :
    ∃ r, allSecured x i r ∨ gridN N - 1 ≤ r := ⟨gridN N - 1, Or.inr le_rfl⟩

/-- Final fence radius: the least radius at which all patches are secured or the whole grid has
been collected. -/
noncomputable def Rstar (x : Fin N → V) (i : Fin N) : ℕ :=
  Nat.find (exists_stop x i)

/-- The candidates: the points collected when the fence stops growing. -/
noncomputable def cand (x : Fin N → V) (i : Fin N) : Finset (Fin N) :=
  Q x i (Rstar x i)

/-- Largest distance from the anchor to a candidate. -/
noncomputable def maxd (x : Fin N → V) (i : Fin N) : ℝ :=
  ((cand x i).sup fun j => (ed (x i) (x j)).toNNReal : NNReal)

/-- Cell distance reached by the extension, `⌈maxd / ds + 1/2⌉`. -/
noncomputable def Mx (x : Fin N → V) (i : Fin N) : ℕ :=
  ⌈maxd x i / ds N + 1 / 2⌉₊

/-- Largest cell distance collected. -/
noncomputable def Tx (x : Fin N → V) (i : Fin N) : ℕ := max (Rstar x i) (Mx x i)

/-- All collected points: the candidates and the points of the extension. -/
noncomputable def blk (x : Fin N → V) (i : Fin N) : Finset (Fin N) :=
  Q x i (Tx x i)

/-- The neighbours reported at anchor `i`: the candidates `k` with no collected point in the
open lune of `x i` and `x k`. -/
noncomputable def output (x : Fin N → V) (i : Fin N) : Finset (Fin N) :=
  (cand x i).filter fun k => ∀ j ∈ blk x i, j ≠ k → ¬ blocks (x i) (x k) (x j)

/-! ### Operation count -/

/-- Operation count of the procedure at anchor `i`, with `R = Rstar x i` and `T = Tx x i`.

* For each radius `r = 0, …, R` of the main loop: `(2r+1)^3` bounds the number of cells of the
  shell swept, and `100 (|Q r| + 1)` bounds the tests of the 24 patches, 4 corners each, against
  every collected point, together with the out-of-bounds tests.
* For each radius `r = R+1, …, T` of the extension: the cells swept and the points collected.
* The lune test of every candidate against every collected point. -/
noncomputable def cost (x : Fin N → V) (i : Fin N) : ℕ :=
  (∑ r ∈ range (Rstar x i + 1), ((2 * r + 1) ^ 3 + 100 * ((Q x i r).card + 1))) +
  (∑ r ∈ Ioc (Rstar x i) (Tx x i), ((2 * r + 1) ^ 3 + (Q x i r).card)) +
  (cand x i).card * ((blk x i).card + 1)

/-- Operation count of the whole algorithm: binning the `N` points, allocating the `n^3` cells,
and the procedure at every anchor. -/
noncomputable def totalCost (x : Fin N → V) : ℕ :=
  N + gridN N ^ 3 + ∑ i, cost x i

/-! ### Random points -/

/-- The uniform distribution on the unit cube. -/
noncomputable def μc : MeasureTheory.Measure V := MeasureTheory.volume.restrict unitCube

/-- The distribution of `N` independent uniform points of the unit cube. -/
noncomputable def PN (N : ℕ) : MeasureTheory.Measure (Fin N → V) :=
  MeasureTheory.Measure.pi fun _ => μc

/-! ### The statements -/

/-- **Correctness.** For `N ≥ 1` points of the unit cube and every anchor `i`, the neighbours
that the procedure reports at `i` are exactly the neighbours of `i` in the relative neighborhood
graph. The points are arbitrary points of the cube, coincident points included. -/
theorem output_iff (hN : 1 ≤ N) {x : Fin N → V} (hx : ∀ j, x j ∈ unitCube) (i k : Fin N) :
    k ∈ output x i ↔ isRNGEdge x i k := by
  sorry

open MeasureTheory in
/-- **Expected linear time.** There is a constant `C` such that for every `N ≥ 1`, for `N`
independent uniform points of the unit cube, the expected operation count of the whole
algorithm is at most `C · N`. -/
theorem expected_linear :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫⁻ x, (totalCost x : ENNReal) ∂(PN N) ≤ ENNReal.ofReal (C * N) := by
  sorry

end Rng3d
