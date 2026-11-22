Lean formalization: SPoIF expected linear time
===

Build (from this directory): `./build.sh` (Mathlib, Lean `v4.35.0-rc2`).
`Axioms.lean` prints the axioms of the two main theorems
(`propext`, `Classical.choice`, `Quot.sound` only; no `sorry`, no `native_decide`).

Main theorems
---

* `Rng3d.output_iff` (`Rng3d/Correct.lean`): for `N ≥ 1` points in `[0,1)^3`
  and any anchor `i`, the edges the modelled procedure reports at `i` are
  exactly the RNG edges at `i` (strict lune, duplicates allowed, no
  general-position assumption).
* `Rng3d.expected_linear` (`Rng3d/Main.lean`): there is a constant `C` such
  that for every `N ≥ 1`, for `N` independent uniform points in `[0,1)^3`,
  the expected operation count `totalCost` is at most `C · N`.

What the model is
---

`Rng3d/Algorithm.lean` models the paper's algorithm with its sign errors
corrected:

* grid of `n` cells per side, `n` least with `N ≤ n^3`;
* fence of radius `r` around the anchor's cell, 4 patches (quadrants) per
  face, 24 in all;
* a patch is secured at radius `r` when all four corners are outside the
  unit cube, or when a collected point `q` has every corner `v` with
  `(q-p)·(v-q) > 0` and `(q-p)·(v-c) > 0` (`c` the cell centre);
* the fence grows until all patches are secured or the grid is swept;
* the collection is extended to shell `⌈max_dist/ds + 1/2⌉` and the naive
  test is run.

`cost` is an operation count I defined per loop (shell cells swept,
24 patches × 4 posts per collected point per radius, extension shells,
candidates × collected points); `totalCost` adds `N + n^3` for grid
allocation and binning.

What is not verified
---

* The C++ (`src/cpp/rng_spoif.cpp`) is not verified.  The model differs
  from `SPoIF_3d_v` in two speed-only shortcuts the C++ has and the model
  lacks: skipping the face opposite to `q - p`, and skipping the securing
  tests below radius `m_fpR_max_ir - 1`.  Both only delay securing, so the
  correctness argument covers them informally, but the runtime theorem is
  for the model.
* Floating point: the model is over the reals.
* `cost` is a hand-written count, not derived from an execution semantics.
* The constant `C` is not computed (it exists; it is astronomically large
  because of crude constants such as `λ = 10^-8`).

Proof outline
---

* `Basic`, `Fence`: corrected plane lemma, growth lemma (paper Thm 2),
  segment–fence crossing, affine positivity on a patch (paper Thm 1).
* `Grid`, `Correct`: cell bookkeeping and `output_iff`.
* `Region`: for fence radius `ρ ≥ 16` and a face inside the cube, an
  explicit box of volume `h^3/4000` inside the cube whose points secure all
  four patches of that face.
* `CostBound`: `cost ≤ 1000 (R*+2)^4 (X+1)^2`, `X` the number of points
  within cell distance `2R*+3`.
* `Measure`, `Expect`, `Main`: `(X+1)^2 ≤ C_λ e^{λX}` turns the bound into
  products of one-coordinate factors; independence factorises the integral;
  for `R* = r ≥ 17` some face's box is empty, giving a factor
  `exp(-r/640000)`; the sum over `r` converges.
