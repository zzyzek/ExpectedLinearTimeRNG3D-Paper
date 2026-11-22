/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Rng3d.Measure

@[expose] public section

/-!
Expected running time.  Each anchor's operation count is dominated by a
finite sum of products of one-coordinate functions; integrating gives a
bound independent of `N`, so the whole algorithm has expected operation
count `O(N)` for `N` independent uniform points in `[0,1)^3`.
-/

open Finset MeasureTheory ProbabilityTheory

namespace Rng3d

variable {N : ℕ}

/-! ### Real inequalities -/

noncomputable def Clam : ℝ := 2 + 4 / lam ^ 2

lemma Clam_pos : 0 < Clam := by unfold Clam; have := lam_pos; positivity

/-- `(X + 1)^2 ≤ C_λ e^{λ K}` for `0 ≤ X ≤ K`. -/
lemma sq_le_Clam_exp {X K : ℝ} (hX : 0 ≤ X) (hXK : X ≤ K) :
    (X + 1) ^ 2 ≤ Clam * Real.exp (lam * K) := by
  have hl := lam_pos
  have hK : 0 ≤ K := hX.trans hXK
  have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hl.le hK)
  have he1 : 1 ≤ Real.exp (lam * K) := Real.one_le_exp (by positivity)
  have hsq : K ^ 2 ≤ 2 * Real.exp (lam * K) / lam ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (lam * K), mul_nonneg hl.le hK]
  have h1 : (X + 1) ^ 2 ≤ 2 + 2 * K ^ 2 := by
    nlinarith [sq_nonneg (X - 1), mul_le_mul hXK hXK hX hK]
  unfold Clam
  have : 2 * K ^ 2 ≤ 4 / lam ^ 2 * Real.exp (lam * K) := by
    have : 4 / lam ^ 2 * Real.exp (lam * K) = 2 * (2 * Real.exp (lam * K) / lam ^ 2) := by
      ring
    rw [this]; linarith
  nlinarith

/-- Decay rate of the tail. -/
noncomputable def cdec : ℝ := 1 / 640000

lemma cdec_pos : 0 < cdec := by unfold cdec; norm_num

/-- The exponent bound for the tail terms: with `b = ((4r+7) ds)^3` the
box volume and `s = h^3/4000` the securing-region volume,
`(N-1)(α b - s) ≤ -c r`. -/
lemma tail_exponent (hN : 1 ≤ N) {r : ℕ} (hr : 17 ≤ r) (hrn : r < gridN N) :
    ((N : ℝ) - 1) * (alpha * ((2 * hR N (2 * r + 3)) ^ 3) -
      hR N (r - 1) / 10 * (hR N (r - 1) / 20) * (hR N (r - 1) / 20)) ≤ -(cdec * r) := by
  have hdp := ds_pos hN
  have hn18 : 18 ≤ gridN N := by omega
  have hN18 : 18 ≤ N := hn18.trans (gridN_le N)
  have hc8 : ((gridN N : ℝ)) ^ 3 ≤ 8 * N := by exact_mod_cast gridN_cube_le hN
  have hdc := ds_cube hN
  have hr' : (17 : ℝ) ≤ r := by exact_mod_cast hr
  have hNr : (18 : ℝ) ≤ N := by exact_mod_cast hN18
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have eb : 2 * hR N (2 * r + 3) = (4 * r + 7) * ds N := by
    unfold hR; push_cast; ring
  have es : hR N (r - 1) = ((r : ℝ) - 1 / 2) * ds N := by
    unfold hR; rw [hcast]; ring
  rw [eb, es]
  set d := ds N
  set D := d ^ 3
  have hD : 0 < D := by positivity
  -- `(N - 1) D ≥ 1/16`, from `n^3 ≤ 8N` and `N ≥ 2`.
  --
  have hMD : 1 / 16 ≤ ((N : ℝ) - 1) * D := by
    have hnD : (gridN N : ℝ) ^ 3 * D = 1 := hdc
    have : (N : ℝ) * D ≥ 1 / 8 := by nlinarith
    nlinarith
  have hal := alpha_le
  have ha0 := alpha_nonneg
  have hcube1 : (4 * (r : ℝ) + 7) ^ 3 ≤ 125 * (r : ℝ) ^ 3 := by
    have : 4 * (r : ℝ) + 7 ≤ 5 * r := by linarith
    calc (4 * (r : ℝ) + 7) ^ 3 ≤ (5 * (r : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) this 3
      _ = 125 * (r : ℝ) ^ 3 := by ring
  have hcube2 : (r : ℝ) ^ 3 / 8 ≤ ((r : ℝ) - 1 / 2) ^ 3 := by
    have : (r : ℝ) / 2 ≤ (r : ℝ) - 1 / 2 := by linarith
    calc (r : ℝ) ^ 3 / 8 = ((r : ℝ) / 2) ^ 3 := by ring
      _ ≤ ((r : ℝ) - 1 / 2) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
  have hbr : alpha * (4 * (r : ℝ) + 7) ^ 3 - ((r : ℝ) - 1 / 2) ^ 3 / 4000 ≤
      -((r : ℝ) ^ 3 / 40000) := by
    have : alpha * (4 * (r : ℝ) + 7) ^ 3 ≤ 2 / 10 ^ 8 * (125 * (r : ℝ) ^ 3) :=
      mul_le_mul hal hcube1 (by positivity) (by norm_num)
    nlinarith
  have hexpr : alpha * ((4 * (r : ℝ) + 7) * d) ^ 3 -
      ((r : ℝ) - 1 / 2) * d / 10 * (((r : ℝ) - 1 / 2) * d / 20) * (((r : ℝ) - 1 / 2) * d / 20) =
      D * (alpha * (4 * (r : ℝ) + 7) ^ 3 - ((r : ℝ) - 1 / 2) ^ 3 / 4000) := by
    simp only [D]; ring
  rw [hexpr]
  have hr3 : (r : ℝ) ≤ (r : ℝ) ^ 3 := by nlinarith
  have hM : 0 ≤ (N : ℝ) - 1 := by linarith
  calc ((N : ℝ) - 1) * (D * (alpha * (4 * (r : ℝ) + 7) ^ 3 - ((r : ℝ) - 1 / 2) ^ 3 / 4000))
      = (((N : ℝ) - 1) * D) * (alpha * (4 * (r : ℝ) + 7) ^ 3 - ((r : ℝ) - 1 / 2) ^ 3 / 4000) := by
        ring
    _ ≤ (((N : ℝ) - 1) * D) * (-((r : ℝ) ^ 3 / 40000)) :=
        mul_le_mul_of_nonneg_left hbr (by positivity)
    _ ≤ (1 / 16) * (-((r : ℝ) ^ 3 / 40000)) := by
        apply mul_le_mul_of_nonpos_right hMD; nlinarith
    _ ≤ -(cdec * r) := by unfold cdec; nlinarith

/-- The head terms: `(N-1) α b ≤ 1` for `r < 17`. -/
lemma head_exponent (hN : 1 ≤ N) {r : ℕ} (hr : r < 17) :
    ((N : ℝ) - 1) * (alpha * ((2 * hR N (2 * r + 3)) ^ 3)) ≤ 1 := by
  have hdp := ds_pos hN
  have hdc := ds_cube hN
  have hNn : (N : ℝ) ≤ (gridN N : ℝ) ^ 3 := by exact_mod_cast gridN_spec N
  have eb : 2 * hR N (2 * r + 3) = (4 * r + 7) * ds N := by
    unfold hR; push_cast; ring
  rw [eb]
  have hr' : (r : ℝ) ≤ 16 := by exact_mod_cast (by omega : r ≤ 16)
  have h71 : (4 * (r : ℝ) + 7) ^ 3 ≤ 71 ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hal := alpha_le
  have ha0 := alpha_nonneg
  have hND : ((N : ℝ) - 1) * ds N ^ 3 ≤ 1 := by
    have : (N : ℝ) * ds N ^ 3 ≤ 1 := by
      calc (N : ℝ) * ds N ^ 3 ≤ (gridN N : ℝ) ^ 3 * ds N ^ 3 :=
            mul_le_mul_of_nonneg_right hNn (by positivity)
        _ = 1 := hdc
    nlinarith [pow_pos hdp 3]
  have hNd0 : 0 ≤ ((N : ℝ) - 1) * ds N ^ 3 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := pow_pos hdp 3
    nlinarith
  calc ((N : ℝ) - 1) * (alpha * ((4 * (r : ℝ) + 7) * ds N) ^ 3)
      = alpha * (4 * (r : ℝ) + 7) ^ 3 * (((N : ℝ) - 1) * ds N ^ 3) := by ring
    _ ≤ (2 / 10 ^ 8 * 71 ^ 3) * 1 :=
        mul_le_mul (mul_le_mul hal h71 (by positivity) (by norm_num)) hND hNd0 (by norm_num)
    _ ≤ 1 := by norm_num

/-! ### Summable tail -/

noncomputable def tailB (r : ℕ) : ℝ := if r < 17 then 3 else 6 * Real.exp (-(cdec * r))

lemma tailB_nonneg (r : ℕ) : 0 ≤ tailB r := by
  unfold tailB; split_ifs <;> positivity

lemma tailB_le (r : ℕ) : tailB r ≤ 9 * Real.exp (-cdec * r) := by
  have hc := cdec_pos
  unfold tailB
  split_ifs with h
  · have : (r : ℝ) ≤ 17 := by exact_mod_cast h.le
    have : -1 ≤ -cdec * r := by unfold cdec at *; nlinarith
    have he : Real.exp (-1) ≤ Real.exp (-cdec * r) := Real.exp_le_exp.mpr this
    have : (1 : ℝ) / 3 ≤ Real.exp (-1) := by
      have := Real.exp_one_lt_d9
      rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
      norm_num at this ⊢; linarith
    linarith
  · rw [show -(cdec * r) = -cdec * r by ring]
    have := Real.exp_pos (-cdec * r)
    linarith

lemma summable_tail : Summable fun r : ℕ => ((r : ℝ) + 2) ^ 4 * tailB r := by
  have hc := cdec_pos
  have h4 := Real.summable_pow_mul_exp_neg_nat_mul 4 hc
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 hc
  refine Summable.of_nonneg_of_le (fun r => mul_nonneg (by positivity) (tailB_nonneg r))
    (fun r => ?_) ((h4.mul_left 72).add (h0.mul_left 1152))
  have hp : ((r : ℝ) + 2) ^ 4 ≤ 8 * (r : ℝ) ^ 4 + 128 := by
    have hr : (0 : ℝ) ≤ r := by positivity
    nlinarith [sq_nonneg ((r : ℝ) ^ 2 - 4), sq_nonneg ((r : ℝ) - 2), sq_nonneg (r : ℝ),
      mul_nonneg hr (sq_nonneg ((r : ℝ) - 2))]
  have he := Real.exp_pos (-cdec * r)
  calc ((r : ℝ) + 2) ^ 4 * tailB r ≤ (8 * (r : ℝ) ^ 4 + 128) * (9 * Real.exp (-cdec * r)) :=
        mul_le_mul hp (tailB_le r) (tailB_nonneg r) (by positivity)
    _ = 72 * ((r : ℝ) ^ 4 * Real.exp (-cdec * r)) +
        1152 * ((r : ℝ) ^ 0 * Real.exp (-cdec * r)) := by ring

end Rng3d
