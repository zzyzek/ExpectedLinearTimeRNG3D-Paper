#!/bin/bash
# Regenerate Challenge.lean: a verbatim copy of Rng3d/Defs.lean with the
# two registered statements (proofs left as sorry) placed before the
# closing `end Rng3d`.
#
set -e
cd "$(dirname "$0")"
sed '$d' Rng3d/Defs.lean > Challenge.lean
test "$(tail -n 1 Rng3d/Defs.lean)" = "end Rng3d"
cat >> Challenge.lean <<'EOS'
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
EOS
