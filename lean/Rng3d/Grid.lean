/-
Elementary facts about the grid: cell bounds, cell centres, and the
relation between Chebyshev cell distance and coordinate distance.
-/
import Rng3d.Algorithm

open Finset

namespace Rng3d

variable {N : ℕ}

lemma gridN_spec (N : ℕ) : N ≤ gridN N ^ 3 := Nat.find_spec (exists_grid N)

lemma gridN_pos (hN : 1 ≤ N) : 0 < gridN N := by
  rcases Nat.eq_zero_or_pos (gridN N) with h | h
  · have := gridN_spec N
    rw [h] at this
    simp at this
    omega
  · exact h

lemma gridN_min (N : ℕ) {m : ℕ} (hm : N ≤ m ^ 3) : gridN N ≤ m :=
  Nat.find_min' (exists_grid N) hm

lemma ds_pos (hN : 1 ≤ N) : 0 < ds N := by
  unfold ds
  have := gridN_pos hN
  positivity

lemma ds_mul (hN : 1 ≤ N) : (gridN N : ℝ) * ds N = 1 := by
  unfold ds
  have : (0 : ℝ) < gridN N := by exact_mod_cast gridN_pos hN
  field_simp

/-- Lower and upper bound of a point inside its cell. -/
lemma cell_bounds (hN : 1 ≤ N) (y : V) (m : Fin 3) :
    (cellOf N y m : ℝ) * ds N ≤ y m ∧ y m < ((cellOf N y m : ℝ) + 1) * ds N := by
  have hn : (0 : ℝ) < gridN N := by exact_mod_cast gridN_pos hN
  have h1 := Int.floor_le ((gridN N : ℝ) * y m)
  have h2 := Int.lt_floor_add_one ((gridN N : ℝ) * y m)
  have hd := ds_mul hN
  have e : (gridN N : ℝ) * y m * ds N = y m := by
    rw [mul_comm _ (y m), mul_assoc, hd, mul_one]
  have hdp := (ds_pos hN).le
  unfold cellOf
  constructor
  · calc (⌊(gridN N : ℝ) * y m⌋ : ℝ) * ds N ≤ (gridN N : ℝ) * y m * ds N :=
          mul_le_mul_of_nonneg_right h1 hdp
      _ = y m := e
  · calc y m = (gridN N : ℝ) * y m * ds N := e.symm
      _ < ((⌊(gridN N : ℝ) * y m⌋ : ℝ) + 1) * ds N :=
          mul_lt_mul_of_pos_right h2 (ds_pos hN)

lemma cell_range (hN : 1 ≤ N) {y : V} (hy : y ∈ unitCube) (m : Fin 3) :
    0 ≤ cellOf N y m ∧ cellOf N y m ≤ (gridN N : ℤ) - 1 := by
  have hn : (0 : ℝ) < gridN N := by exact_mod_cast gridN_pos hN
  obtain ⟨h0, h1⟩ := hy m
  unfold cellOf
  constructor
  · exact Int.floor_nonneg.mpr (by positivity)
  · have : (gridN N : ℝ) * y m < (gridN N : ℝ) := by nlinarith
    have h := Int.floor_le ((gridN N : ℝ) * y m)
    have : ((⌊(gridN N : ℝ) * y m⌋ : ℤ) : ℝ) < (gridN N : ℤ) := by
      push_cast; linarith
    have := Int.cast_lt.mp this
    omega

lemma center_sub (hN : 1 ≤ N) (y : V) (m : Fin 3) :
    -(ds N / 2) ≤ y m - center N y m ∧ y m - center N y m < ds N / 2 := by
  obtain ⟨h1, h2⟩ := cell_bounds hN y m
  unfold center
  constructor <;> nlinarith

lemma abs_center_sub (hN : 1 ≤ N) (y : V) (m : Fin 3) :
    |y m - center N y m| ≤ ds N / 2 := by
  obtain ⟨h1, h2⟩ := center_sub hN y m
  rw [abs_le]; constructor <;> linarith

lemma center_mem (hN : 1 ≤ N) {y : V} (hy : y ∈ unitCube) (m : Fin 3) :
    0 < center N y m ∧ center N y m < 1 := by
  obtain ⟨h0, h1⟩ := cell_range hN hy m
  have hd := ds_mul hN
  have hdp := ds_pos hN
  have h0' : (0 : ℝ) ≤ cellOf N y m := by exact_mod_cast h0
  have h1' : (cellOf N y m : ℝ) ≤ (gridN N : ℝ) - 1 := by exact_mod_cast h1
  unfold center
  constructor
  · nlinarith
  · nlinarith

lemma cheb_le_iff (y z : V) (r : ℕ) :
    cheb N y z ≤ r ↔ ∀ m, (cellOf N y m - cellOf N z m).natAbs ≤ r := by
  unfold cheb
  simp [Finset.sup_le_iff]

lemma cheb_le_grid (hN : 1 ≤ N) {y z : V} (hy : y ∈ unitCube) (hz : z ∈ unitCube) :
    cheb N y z ≤ gridN N - 1 := by
  rw [cheb_le_iff]
  intro m
  have a := cell_range hN hy m
  have b := cell_range hN hz m
  have := gridN_pos hN
  omega

/-- A point whose cell is beyond Chebyshev distance `r` lies on or
outside the radius-`r` fence. -/
lemma far_of_cheb (hN : 1 ≤ N) {y z : V} {r : ℕ} (h : r < cheb N z y) :
    ∃ m, hR N r ≤ |z m - center N y m| := by
  have : ¬ cheb N z y ≤ r := by omega
  rw [cheb_le_iff] at this
  push Not at this
  obtain ⟨m, hm⟩ := this
  refine ⟨m, ?_⟩
  obtain ⟨z1, z2⟩ := cell_bounds hN z m
  have hdp := ds_pos hN
  unfold hR center
  rcases le_or_gt (cellOf N z m) (cellOf N y m) with hle | hlt
  · have hk : (cellOf N z m : ℝ) ≤ (cellOf N y m : ℝ) - r - 1 := by
      have : (cellOf N z m) ≤ cellOf N y m - r - 1 := by omega
      exact_mod_cast this
    rw [abs_sub_comm, le_abs]; left
    nlinarith
  · have hk : (cellOf N y m : ℝ) + r + 1 ≤ (cellOf N z m : ℝ) := by
      have : cellOf N y m + r + 1 ≤ cellOf N z m := by omega
      exact_mod_cast this
    rw [le_abs]; left
    nlinarith

/-- Points within coordinate distance `e` are within cell distance
`⌈e/ds + 1/2⌉`. -/
lemma cheb_le_of_close (hN : 1 ≤ N) {y z : V} {e : ℝ}
    (h : ∀ m, |z m - y m| ≤ e) : cheb N z y ≤ ⌈e / ds N + 1 / 2⌉₊ := by
  rw [cheb_le_iff]
  intro m
  have hdp := ds_pos hN
  obtain ⟨z1, z2⟩ := cell_bounds hN z m
  obtain ⟨y1, y2⟩ := cell_bounds hN y m
  have hzy := abs_le.mp (h m)
  set a := cellOf N z m
  set b := cellOf N y m
  -- `(|a - b| - 1) ds < e`, so `|a - b| < e/ds + 1 ≤ K + 1/2`.
  --
  have key : ((a - b).natAbs : ℝ) - 1 < e / ds N := by
    rw [lt_div_iff₀ hdp]
    rcases le_or_gt a b with hab | hab
    · have : ((a - b).natAbs : ℝ) = (b : ℝ) - a := by
        rw [Nat.cast_natAbs, Int.cast_abs]; push_cast
        rw [abs_of_nonpos (by exact_mod_cast (sub_nonpos.mpr hab))]; ring
      rw [this]; nlinarith
    · have : ((a - b).natAbs : ℝ) = (a : ℝ) - b := by
        rw [Nat.cast_natAbs, Int.cast_abs]; push_cast
        rw [abs_of_pos (by exact_mod_cast (sub_pos.mpr hab))]
      rw [this]; nlinarith
  have hK := Nat.le_ceil (e / ds N + 1 / 2)
  have : ((a - b).natAbs : ℝ) < (⌈e / ds N + 1 / 2⌉₊ : ℝ) + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- Points within cell distance `r` are within coordinate distance
`(r + 1) ds`. -/
lemma close_of_cheb (hN : 1 ≤ N) {y z : V} {r : ℕ} (h : cheb N z y ≤ r)
    (m : Fin 3) : |z m - y m| < ((r : ℝ) + 1) * ds N := by
  rw [cheb_le_iff] at h
  have hm := h m
  have hdp := ds_pos hN
  obtain ⟨z1, z2⟩ := cell_bounds hN z m
  obtain ⟨y1, y2⟩ := cell_bounds hN y m
  have hab : |((cellOf N z m : ℝ) - cellOf N y m)| ≤ r := by
    have : ((cellOf N z m - cellOf N y m).natAbs : ℝ) ≤ r := by exact_mod_cast hm
    rw [Nat.cast_natAbs, Int.cast_abs] at this; push_cast at this; exact this
  rw [abs_le] at hab
  rw [abs_lt]; constructor <;> nlinarith

end Rng3d
