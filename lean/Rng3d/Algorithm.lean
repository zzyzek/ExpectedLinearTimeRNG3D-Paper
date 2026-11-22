/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Rng3d.Basic

@[expose] public section

/-!
First facts about the definitions of `Rng3d.Defs`: the stopping radius `Rstar`, and membership in
the collected set `Q` and in `output`.
-/

open Finset

namespace Rng3d

open Classical

variable {N : ℕ}

lemma Rstar_spec (x : Fin N → V) (i : Fin N) :
    allSecured x i (Rstar x i) ∨ gridN N - 1 ≤ Rstar x i :=
  Nat.find_spec (exists_stop x i)

lemma Rstar_min (x : Fin N → V) (i : Fin N) {r : ℕ} (h : r < Rstar x i) :
    ¬ (allSecured x i r ∨ gridN N - 1 ≤ r) :=
  Nat.find_min (exists_stop x i) h

lemma Rstar_le (x : Fin N → V) (i : Fin N) : Rstar x i ≤ gridN N - 1 :=
  Nat.find_min' (exists_stop x i) (Or.inr le_rfl)

lemma mem_Q {x : Fin N → V} {i j : Fin N} {r : ℕ} :
    j ∈ Q x i r ↔ j ≠ i ∧ cheb N (x j) (x i) ≤ r := by
  unfold Q; rw [mem_filter]; simp

lemma mem_output {x : Fin N → V} {i k : Fin N} :
    k ∈ output x i ↔
      k ∈ cand x i ∧ ∀ j ∈ blk x i, j ≠ k → ¬ blocks (x i) (x k) (x j) := by
  unfold output; rw [mem_filter]

end Rng3d
