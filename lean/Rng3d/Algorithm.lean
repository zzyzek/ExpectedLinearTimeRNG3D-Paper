/-
Model of the SPoIF algorithm (Secure Posts on Increasing Fence) for one
anchor point, following the paper with its sign errors corrected and
matching the C++ `SPoIF_3d_v` except for two speed-only shortcuts
(skipping the face opposite to `q - p`, and skipping the securing tests
for the first few radii), which only delay securing.

* The `N` points are binned into an `n × n × n` grid, `n` the least
  natural with `N ≤ n^3`, cell side `ds = 1/n`.
* For anchor `i` the fence at integer radius `r` is the cube centred at
  the centre `c` of the anchor's cell with half-width `(r + 1/2) ds`,
  i.e. the outer boundary of the cells at Chebyshev cell distance `≤ r`.
* Each face is split into four square patches (quadrants), whose
  corners are the fence posts.  A patch is secured at radius `r` when all
  its corners are outside the unit cube, or when some collected point
  `q` puts every corner `v` strictly beyond the plane through `q` with
  normal `q - p` and also has `(q - p) ⬝ (v - c) > 0`, so the patch stays
  beyond the plane as the fence grows.
* The fence grows until every patch is secured or the whole grid is
  swept.  Then the collection is extended by enough shells to contain
  the lune of `p` with every collected point, and the naive test is run.
-/
import Rng3d.Basic

open Finset

namespace Rng3d

open Classical

variable {N : ℕ}

lemma exists_grid (N : ℕ) : ∃ n : ℕ, N ≤ n ^ 3 :=
  ⟨N, by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ 3 := Nat.pow_le_pow_right h (by norm_num)⟩

/-- Grid cells per side: the least `n` with `N ≤ n^3`, i.e. `⌈N^{1/3}⌉`. -/
noncomputable def gridN (N : ℕ) : ℕ := Nat.find (exists_grid N)

/-- Grid cell side length. -/
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

/-- Points (other than the anchor) in cells at Chebyshev distance `≤ r`. -/
noncomputable def Q (x : Fin N → V) (i : Fin N) (r : ℕ) : Finset (Fin N) :=
  univ.filter fun j => j ≠ i ∧ cheb N (x j) (x i) ≤ r

/-- A patch: a face axis `P.1`, the face sign `P.2 P.1`, and the quadrant
signs `P.2 m` for the two other axes `m`.  There are `3 · 8 = 24`. -/
abbrev Patch := Fin 3 × (Fin 3 → Bool)

def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Corner directions of a patch (scaled by the fence half-width).
`κ m` selects, for each axis `m` other than the face axis, the corner
at the face midline (`false`) or at the face edge (`true`). -/
def cornerDir (P : Patch) (κ : Fin 3 → Bool) : V :=
  fun m => if m = P.1 then sgn (P.2 m) else if κ m then sgn (P.2 m) else 0

noncomputable def corner (x : Fin N → V) (i : Fin N) (r : ℕ) (P : Patch)
    (κ : Fin 3 → Bool) : V :=
  center N (x i) + hR N r • cornerDir P κ

/-- Every post of the patch is outside the unit cube. -/
def OOB (x : Fin N → V) (i : Fin N) (r : ℕ) (P : Patch) : Prop :=
  ∀ κ, corner x i r P κ ∉ unitCube

/-- Point `j` secures patch `P` of the radius-`r` fence of anchor `i`. -/
def securesBy (x : Fin N → V) (i : Fin N) (r : ℕ) (P : Patch) (j : Fin N) :
    Prop :=
  ∀ κ, 0 < (x j - x i) ⬝ᵥ (corner x i r P κ - x j) ∧
    0 < (x j - x i) ⬝ᵥ (hR N r • cornerDir P κ)

/-- Patch `P` has been secured at some radius `r' ≤ r`. -/
def securedAt (x : Fin N → V) (i : Fin N) (r : ℕ) (P : Patch) : Prop :=
  ∃ r' ≤ r, OOB x i r' P ∨ ∃ j ∈ Q x i r', securesBy x i r' P j

def allSecured (x : Fin N → V) (i : Fin N) (r : ℕ) : Prop :=
  ∀ P, securedAt x i r P

lemma exists_stop (x : Fin N → V) (i : Fin N) :
    ∃ r, allSecured x i r ∨ gridN N - 1 ≤ r := ⟨gridN N - 1, Or.inr le_rfl⟩

/-- Final fence radius of the main loop. -/
noncomputable def Rstar (x : Fin N → V) (i : Fin N) : ℕ :=
  Nat.find (exists_stop x i)

lemma Rstar_spec (x : Fin N → V) (i : Fin N) :
    allSecured x i (Rstar x i) ∨ gridN N - 1 ≤ Rstar x i :=
  Nat.find_spec (exists_stop x i)

lemma Rstar_min (x : Fin N → V) (i : Fin N) {r : ℕ} (h : r < Rstar x i) :
    ¬ (allSecured x i r ∨ gridN N - 1 ≤ r) :=
  Nat.find_min (exists_stop x i) h

lemma Rstar_le (x : Fin N → V) (i : Fin N) : Rstar x i ≤ gridN N - 1 :=
  Nat.find_min' (exists_stop x i) (Or.inr le_rfl)

/-- Candidate neighbours: everything collected by the main loop. -/
noncomputable def cand (x : Fin N → V) (i : Fin N) : Finset (Fin N) :=
  Q x i (Rstar x i)

/-- Largest distance from the anchor to a candidate. -/
noncomputable def maxd (x : Fin N → V) (i : Fin N) : ℝ :=
  ((cand x i).sup fun j => (ed (x i) (x j)).toNNReal : NNReal)

/-- Shell radius reached by the saboteur extension
(`max_ir = ceil(max_dist/ds + 0.5)` in the C++). -/
noncomputable def Mx (x : Fin N → V) (i : Fin N) : ℕ :=
  ⌈maxd x i / ds N + 1 / 2⌉₊

noncomputable def Tx (x : Fin N → V) (i : Fin N) : ℕ := max (Rstar x i) (Mx x i)

/-- Candidates together with the saboteurs. -/
noncomputable def blk (x : Fin N → V) (i : Fin N) : Finset (Fin N) :=
  Q x i (Tx x i)

/-- Naive test: candidates not blocked by any collected point. -/
noncomputable def output (x : Fin N → V) (i : Fin N) : Finset (Fin N) :=
  (cand x i).filter fun k => ∀ j ∈ blk x i, j ≠ k → ¬ blocks (x i) (x k) (x j)

lemma mem_Q {x : Fin N → V} {i j : Fin N} {r : ℕ} :
    j ∈ Q x i r ↔ j ≠ i ∧ cheb N (x j) (x i) ≤ r := by
  unfold Q; rw [mem_filter]; simp

lemma mem_output {x : Fin N → V} {i k : Fin N} :
    k ∈ output x i ↔
      k ∈ cand x i ∧ ∀ j ∈ blk x i, j ≠ k → ¬ blocks (x i) (x k) (x j) := by
  unfold output; rw [mem_filter]

/-- The RNG edges at the anchor `i` (strict lune; duplicates allowed). -/
def isRNGEdge (x : Fin N → V) (i k : Fin N) : Prop :=
  i ≠ k ∧ ∀ j, j ≠ i → j ≠ k → ¬ blocks (x i) (x k) (x j)

/-- Operation count of the per-anchor procedure (an upper bound on the
work of each loop).
* main loop, radius `r = 0 … R*`: sweep the `≤ (2r+1)^3` cells of the
  shell, then test the 24 patches (4 posts each) against every collected
  point;
* extension, radius `R* < r ≤ T`: sweep cells and collect points;
* naive test: every candidate against every collected point. -/
noncomputable def cost (x : Fin N → V) (i : Fin N) : ℕ :=
  (∑ r ∈ range (Rstar x i + 1), ((2 * r + 1) ^ 3 + 100 * ((Q x i r).card + 1))) +
  (∑ r ∈ Ioc (Rstar x i) (Tx x i), ((2 * r + 1) ^ 3 + (Q x i r).card)) +
  (cand x i).card * ((blk x i).card + 1)

/-- Whole algorithm: grid allocation, binning, and each anchor. -/
noncomputable def totalCost (x : Fin N → V) : ℕ :=
  N + gridN N ^ 3 + ∑ i, cost x i

end Rng3d
