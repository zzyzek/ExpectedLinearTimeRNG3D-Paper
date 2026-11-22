/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Rng3d.Defs

@[expose] public section

/-!
Basic geometry for the 3D relative neighborhood graph (RNG).

Points live in `V = Fin 3 → ℝ`.  Distances are compared through the
squared Euclidean distance `dd`, so no square roots appear in the
RNG definition.
-/

open Finset

namespace Rng3d

lemma dd_eq (a b : V) : dd a b = ∑ m, (a m - b m) ^ 2 := by
  simp [dd, dotProduct, sq]

lemma dd_nonneg (a b : V) : 0 ≤ dd a b := by
  rw [dd_eq]; positivity

lemma dd_comm (a b : V) : dd a b = dd b a := by
  simp only [dd_eq]; congr 1; ext m; ring

lemma coord_sq_le_dd (a b : V) (m : Fin 3) : (a m - b m) ^ 2 ≤ dd a b := by
  rw [dd_eq]
  exact Finset.single_le_sum (f := fun m => (a m - b m) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ m)

lemma abs_coord_le_ed (a b : V) (m : Fin 3) : |a m - b m| ≤ ed a b := by
  unfold ed
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (coord_sq_le_dd a b m)

lemma dd_lt_of_ed_lt {a b c d : V} (h : ed a b < ed c d) : dd a b < dd c d := by
  unfold ed at h
  exact (Real.sqrt_lt_sqrt_iff (dd_nonneg a b)).1 h

lemma ed_lt_of_dd_lt {a b c d : V} (h : dd a b < dd c d) : ed a b < ed c d := by
  unfold ed
  exact Real.sqrt_lt_sqrt (dd_nonneg a b) h

/-- The plane cut: if `w` is strictly
beyond the plane through `q` with normal `q - p`, then `q` lies in the
open lune of `p` and `w`. -/
theorem plane_blocks {p q w : V} (h : 0 < (q - p) ⬝ᵥ (w - q)) : blocks p w q := by
  simp only [blocks, dd_eq]
  simp only [dotProduct, Fin.sum_univ_three, Pi.sub_apply] at h ⊢
  constructor <;> nlinarith [sq_nonneg (w 0 - q 0), sq_nonneg (w 1 - q 1),
    sq_nonneg (w 2 - q 2), sq_nonneg (q 0 - p 0), sq_nonneg (q 1 - p 1),
    sq_nonneg (q 2 - p 2)]

/-- The anchor point is strictly on its own side of every cut plane. -/
lemma self_side_neg {p q : V} (hpq : q ≠ p) : (q - p) ⬝ᵥ (p - q) < 0 := by
  have hne : q - p ≠ 0 := sub_ne_zero.mpr hpq
  have hpos : 0 < (q - p) ⬝ᵥ (q - p) := by
    obtain ⟨m, hm⟩ : ∃ m, (q - p) m ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (funext hc)
    have hm2 := mul_self_pos.mpr hm
    simp only [dotProduct, Fin.sum_univ_three]
    fin_cases m <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hm2 <;>
      nlinarith [mul_self_nonneg ((q - p) 0), mul_self_nonneg ((q - p) 1),
        mul_self_nonneg ((q - p) 2)]
  have : (q - p) ⬝ᵥ (p - q) = -((q - p) ⬝ᵥ (q - p)) := by
    rw [show p - q = -(q - p) by abel, dotProduct_neg]
  linarith

/-- An affine function negative at `p` and positive at a point of the
segment from `p` to `w` is positive at `w`. -/
lemma affine_pos_of_segment {n p q w : V} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : n ⬝ᵥ (p - q) < 0)
    (hz : 0 < n ⬝ᵥ ((1 - t) • p + t • w - q)) : 0 < n ⬝ᵥ (w - q) := by
  have hsplit : n ⬝ᵥ ((1 - t) • p + t • w - q) =
      (1 - t) * (n ⬝ᵥ (p - q)) + t * (n ⬝ᵥ (w - q)) := by
    simp only [dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit] at hz
  by_contra hc
  push Not at hc
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · subst h0; nlinarith
  · nlinarith [mul_nonneg ht0 (neg_nonneg.mpr hc), mul_nonneg (sub_nonneg.mpr ht1) (neg_nonneg.mpr hp.le)]

/-- Growth of the fence: scaling a secured post away from the fence
centre `c` by `L ≥ 1` keeps it strictly beyond the cut plane. -/
lemma scale_secure {n q c v : V} {L : ℝ} (hL : 1 ≤ L)
    (h0 : 0 < n ⬝ᵥ (c + v - q)) (h1 : 0 < n ⬝ᵥ v) :
    0 < n ⬝ᵥ (c + L • v - q) := by
  have : n ⬝ᵥ (c + L • v - q) = n ⬝ᵥ (c + v - q) + (L - 1) * (n ⬝ᵥ v) := by
    simp only [dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [this]
  nlinarith

/-- Bilinear interpolation: an affine function of two parameters that is
positive at the four corners of `[0,1]^2` is positive on the square. -/
lemma affine_square_pos {g0 α β a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (h00 : 0 < g0) (h10 : 0 < g0 + α) (h01 : 0 < g0 + β)
    (h11 : 0 < g0 + α + β) : 0 < g0 + α * a + β * b := by
  have hid : g0 + α * a + β * b =
      (1 - a) * (1 - b) * g0 + a * (1 - b) * (g0 + α) +
      (1 - a) * b * (g0 + β) + a * b * (g0 + α + β) := by ring
  rw [hid]
  have e1 : 0 ≤ (1 - a) * (1 - b) := mul_nonneg (by linarith) (by linarith)
  have e2 : 0 ≤ a * (1 - b) := mul_nonneg ha0 (by linarith)
  have e3 : 0 ≤ (1 - a) * b := mul_nonneg (by linarith) hb0
  have e4 : 0 ≤ a * b := mul_nonneg ha0 hb0
  -- The four weights sum to one, so at least one is positive.
  --
  have hsum : (1 - a) * (1 - b) + a * (1 - b) + (1 - a) * b + a * b = 1 := by ring
  rcases (show 0 < (1 - a) * (1 - b) ∨ 0 < a * (1 - b) ∨ 0 < (1 - a) * b ∨
      0 < a * b by
    by_contra hc; push Not at hc
    linarith [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]) with h | h | h | h
  · nlinarith [mul_pos h h00, mul_nonneg e2 h10.le, mul_nonneg e3 h01.le,
      mul_nonneg e4 h11.le]
  · nlinarith [mul_nonneg e1 h00.le, mul_pos h h10, mul_nonneg e3 h01.le,
      mul_nonneg e4 h11.le]
  · nlinarith [mul_nonneg e1 h00.le, mul_nonneg e2 h10.le, mul_pos h h01,
      mul_nonneg e4 h11.le]
  · nlinarith [mul_nonneg e1 h00.le, mul_nonneg e2 h10.le, mul_nonneg e3 h01.le,
      mul_pos h h11]

end Rng3d
