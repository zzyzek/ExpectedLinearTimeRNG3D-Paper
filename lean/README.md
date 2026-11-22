Relative neighborhood graph of uniform points in the unit cube: expected linear time (Lean 4)
===

A Lean 4 proof that the SPoIF algorithm (Secure Posts on Increasing Fence) computes the relative
neighborhood graph of points of the unit cube in three dimensions, and that its expected
operation count on `N` independent uniform points is at most `C · N`.

The relative neighborhood graph (RNG) joins two points `p` and `w` when no third point `u` has
both `|p - u| < |p - w|` and `|w - u| < |p - w|`. The set of such `u` is the open lune of `p`
and `w`.

The two theorems
---

* `Rng3d.output_iff` (`Rng3d/Correct.lean`). For `N ≥ 1` points of `[0,1)^3` and every point
  `i`, the neighbours that the procedure reports at `i` are exactly the neighbours of `i` in the
  RNG. The points are arbitrary points of the cube. Coincident points are allowed.
* `Rng3d.expected_linear` (`Rng3d/Main.lean`). There is a constant `C ≥ 0` such that for every
  `N ≥ 1`, for `N` independent uniform points of `[0,1)^3`, the expectation of the operation
  count `totalCost` is at most `C · N`.

Both depend on the axioms `propext`, `Classical.choice` and `Quot.sound`. `Axioms.lean` prints
them.

The algorithm
---

All definitions that the two statements use are in `Rng3d/Defs.lean`.

* The `N` points are binned into a grid of `n × n × n` cells, where `n` is the least natural
  number with `N ≤ n^3`. A cell has side `ds = 1/n`.
* The procedure handles one point at a time, the anchor `p`. The fence of integer radius `r` is
  the cube centred at the centre `c` of the anchor's cell with half-width `(r + 1/2) ds`. It is
  the outer boundary of the cells at Chebyshev cell distance at most `r` from the anchor's
  cell. The points of those cells have been collected.
* Each of the six faces of the fence is cut into four square patches (its quadrants). The
  corners of the patches are the fence posts. A patch is secured at radius `r` when
  - all four of its corners are outside the unit cube, or
  - some collected point `q` has `(q - p) · (v - q) > 0` and `(q - p) · (v - c) > 0` for every
    corner `v` of the patch.

  The first inequality puts the patch strictly beyond the plane through `q` with normal
  `q - p`. Any point `w` beyond that plane has `q` in its lune with `p`, so `w` is not a
  neighbour of `p`. The second inequality keeps the patch beyond the plane when the fence
  grows, so a secured patch stays secured.
* The radius grows from `0` until all 24 patches are secured, or until the whole grid has been
  collected. The points collected at that radius are the candidates. Every neighbour of `p` is
  a candidate.
* More shells of cells are collected, up to cell distance `⌈D/ds + 1/2⌉`, where `D` is the
  largest distance from `p` to a candidate. The lune of `p` with any candidate is then inside
  the collected cells.
* A candidate `w` is reported as a neighbour when no collected point is in the lune of `p` and
  `w`.

The operation count
---

`Rng3d.cost x i` counts the work at anchor `i`, with `R` the final fence radius and `T` the
largest cell distance collected.

* For each radius `r = 0, …, R`: `(2r+1)^3` for the cells of the shell, and
  `100 (|Q r| + 1)` for the tests of the 24 patches, 4 corners each, against the `|Q r|`
  collected points.
* For each radius `r = R+1, …, T`: `(2r+1)^3` for the cells and `|Q r|` for the points.
* `|candidates| · (|collected| + 1)` for the lune tests.

`Rng3d.totalCost x` is `N + n^3` plus the sum of `cost x i` over all points `i`.

Scope
---

* The statements are about the procedure of `Rng3d/Defs.lean` over the real numbers. The C++
  reference implementation (`../src/cpp/rng_spoif.cpp`, `SPoIF_3d_v`) uses floating point and
  is outside the formalization.
* The C++ has two shortcuts that the Lean procedure does not have. It does not test the face
  opposite to the direction from the anchor to the collected point, and it starts the patch
  tests at a fixed small radius. Both can only delay the radius at which the fence is secured.
  The two theorems are for the Lean procedure.
* `cost` is a definition written for this formalization. It is an upper bound on the work of
  each loop of the procedure. It is not derived from an execution semantics.
* The constant `C` is shown to exist. Its value is not computed.
* The points are uniform on the cube. Other distributions and other domains are outside the
  formalization.

Outline of the proofs
---

* `Basic`, `Fence`: a point strictly beyond the plane through `q` with normal `q - p` has `q`
  in its lune with `p`. A secured corner stays beyond the plane when scaled away from the fence
  centre. A segment from inside the fence to a point outside it meets a patch. A function
  `u ↦ n · (u - q)` that is positive at the four corners of a patch is positive on the patch.
* `Grid`, `Algorithm`, `Correct`: cell arithmetic, and `output_iff`.
* `Region`: for fence radius `ρ ≥ 16` and a face whose plane is inside the cube, an explicit
  box of volume `h^3/4000` inside the cube (`h` the fence half-width), every point of which
  secures all four patches of that face.
* `CostBound`: `cost ≤ 1000 (R+2)^4 (X+1)^2`, where `X` is the number of points within cell
  distance `2R+3` of the anchor.
* `Measure`, `Expect`, `Main`: `(X+1)^2 ≤ C_λ e^{λX}` turns the bound into a sum of products of
  functions of one point each, and independence turns the integral of each product into a
  product of integrals. If the final radius is `r ≥ 17`, the box of some face at radius `r - 1`
  contains no other point, which contributes a factor at most `exp(-r/640000)`. The sum over
  `r` converges.

Related work
---

The planar case is known: J. Katajainen, O. Nevalainen and J. Teuhola, A linear expected-time
algorithm for computing planar relative neighbourhood graphs, Inform. Process. Lett. 25 (1987),
77–86. In three dimensions, P. K. Agarwal and J. Matoušek, Relative neighborhood graphs in
three dimensions, Comput. Geom. 2 (1992), 1–14, give expected time `O(n^(3/2+ε))` on
worst-case inputs in general position.

A search in November 2026 found no published algorithm with linear expected time for uniform
points in three dimensions. What the search covered:

* Full text obtained, and the passages on the RNG, on expected time and on open problems read:
  D. Eppstein, Spanning trees and spanners (Tech. Rep. 96-16, UC Irvine, 1996); J. Katajainen
  and O. Nevalainen, An almost naive algorithm for finding relative neighbourhood graphs in
  `L_p` metrics (RAIRO Inform. Théor. Appl. 21 (1987), 199–215); P. D. MacKenzie and
  Q. F. Stout, Ultra-fast expected time parallel algorithms (J. Algorithms 26 (1998), 1–33).
  The expected time results for the RNG in the last two are for the unit square. The eight
  open problems listed by Eppstein are about other graphs.
* Abstract or search summary only: Katajainen, Nevalainen and Teuhola (1987); Agarwal and
  Matoušek (1992); T.-H. Su and R.-C. Chang, On constructing the relative neighborhood graphs
  in Euclidean k-dimensional spaces (Computing 46 (1991), 121–130); J. Katajainen, The region
  approach for computing relative neighbourhood graphs in the `L_p` metric (Computing 40
  (1988), 147–161).
* Could not be read (publisher access): J. W. Jaromczyk and G. T. Toussaint, Relative
  neighborhood graphs and their relatives (Proc. IEEE 80 (1992), 1502–1517); J. W. Jaromczyk
  and M. Kowaluk (Discrete Appl. Math. 31 (1991), 181–191); K. J. Supowit (J. ACM 30 (1983),
  428–448); R. A. Dwyer, Higher-dimensional Voronoi diagrams in linear expected time (Discrete
  Comput. Geom. 6 (1991), 343–367).

Building
---

Lean `v4.35.0-rc2` with Mathlib (pinned in `lake-manifest.json`).

```
./build.sh                    # the library, under a memory cap
./build.sh Challenge Solution
./check.sh Axioms.lean        # prints the axioms of the two theorems
```

Palomar registry files
---

* `Challenge.lean`: a verbatim copy of `Rng3d/Defs.lean` followed by the two statements. It
  imports only Mathlib. `./mkchallenge.sh` regenerates it after a change to `Rng3d/Defs.lean`.
* `Solution.lean`: imports the library, where the two theorems are proved.
* `comparator.json`: the two theorem names and the permitted axioms.
* `formalization.yaml`: the metadata.

License
---

CC0 1.0 Universal. See `LICENSE`.
