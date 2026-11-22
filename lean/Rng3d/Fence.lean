/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Rng3d.Grid

@[expose] public section

/-!
Fence geometry: a segment leaving the fence crosses its surface, and a
point of the surface lies in a patch, on which an affine function that
is positive at the patch corners is positive.
-/

open Finset

namespace Rng3d

/-- Sup-distance from `c` along the segment from `p` to `w`. -/
noncomputable def supDistSeg (p w c : V) (t : ℝ) : ℝ :=
  max (max |((1 - t) • p + t • w) 0 - c 0| |((1 - t) • p + t • w) 1 - c 1|)
    |((1 - t) • p + t • w) 2 - c 2|

lemma supDistSeg_continuous (p w c : V) : Continuous (supDistSeg p w c) := by
  unfold supDistSeg
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

lemma le_supDistSeg (p w c : V) (t : ℝ) (m : Fin 3) :
    |((1 - t) • p + t • w) m - c m| ≤ supDistSeg p w c t := by
  unfold supDistSeg
  fin_cases m <;> simp

lemma supDistSeg_attained (p w c : V) (t : ℝ) :
    ∃ m, |((1 - t) • p + t • w) m - c m| = supDistSeg p w c t := by
  unfold supDistSeg
  rcases le_total |((1 - t) • p + t • w) 0 - c 0| |((1 - t) • p + t • w) 1 - c 1|
    with h01 | h01 <;>
  rcases le_total (max |((1 - t) • p + t • w) 0 - c 0| |((1 - t) • p + t • w) 1 - c 1|)
    |((1 - t) • p + t • w) 2 - c 2| with h2 | h2
  · exact ⟨2, (max_eq_right h2).symm⟩
  · exact ⟨1, by rw [max_eq_left h2, max_eq_right h01]⟩
  · exact ⟨2, (max_eq_right h2).symm⟩
  · exact ⟨0, by rw [max_eq_left h2, max_eq_left h01]⟩

/-- A segment from inside (or on) the fence to a point on or outside it
meets the fence surface. -/
lemma segment_cross {p w c : V} {h : ℝ}
    (hp : ∀ m, |p m - c m| ≤ h) (hw : ∃ m, h ≤ |w m - c m|) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (∀ m, |((1 - t) • p + t • w) m - c m| ≤ h) ∧
      ∃ m, |((1 - t) • p + t • w) m - c m| = h := by
  have g0 : supDistSeg p w c 0 ≤ h := by
    obtain ⟨m, hm⟩ := supDistSeg_attained p w c 0
    rw [← hm]; simpa using hp m
  have g1 : h ≤ supDistSeg p w c 1 := by
    obtain ⟨m, hm⟩ := hw
    calc h ≤ |w m - c m| := hm
      _ = |(((1 : ℝ) - 1) • p + (1 : ℝ) • w) m - c m| := by simp
      _ ≤ _ := le_supDistSeg p w c 1 m
  obtain ⟨t, ⟨ht0, ht1⟩, hth⟩ := intermediate_value_Icc (zero_le_one' ℝ)
    (supDistSeg_continuous p w c).continuousOn ⟨g0, g1⟩
  refine ⟨t, ht0, ht1, fun m => hth ▸ le_supDistSeg p w c t m, ?_⟩
  obtain ⟨m, hm⟩ := supDistSeg_attained p w c t
  exact ⟨m, hm.trans hth⟩

lemma sgn_mul_abs (d : ℝ) : sgn (decide (0 ≤ d)) * |d| = d := by
  unfold sgn
  by_cases h : 0 ≤ d
  · simp [h, abs_of_nonneg h]
  · push Not at h; simp [not_le.mpr h, abs_of_neg h]

lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

lemma sgn_mul_self_abs (d : ℝ) : sgn (decide (0 ≤ d)) * d = |d| := by
  have h := sgn_mul_abs d
  have h2 := sgn_sq (decide (0 ≤ d))
  calc sgn (decide (0 ≤ d)) * d
      = sgn (decide (0 ≤ d)) * (sgn (decide (0 ≤ d)) * |d|) := by rw [h]
    _ = |d| := by rw [← mul_assoc, h2, one_mul]

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

/-- An affine function positive
at the four corners of a patch is positive on the patch. -/
lemma patch_pos (P : Patch) {z c n q : V} {h : ℝ} (hh : 0 < h)
    (hz : ∀ m, |z m - c m| ≤ h) (hface : z P.1 - c P.1 = sgn (P.2 P.1) * h)
    (hquad : ∀ m, 0 ≤ sgn (P.2 m) * (z m - c m))
    (hcorner : ∀ κ, 0 < n ⬝ᵥ (c + h • cornerDir P κ - q)) : 0 < n ⬝ᵥ (z - q) := by
  obtain ⟨ax, s⟩ := P
  -- Normalised positions `a m ∈ [0,1]` along the two quadrant axes.
  --
  have ha : ∀ m, ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ h * a = sgn (s m) * (z m - c m) := by
    intro m
    refine ⟨sgn (s m) * (z m - c m) / h, div_nonneg (hquad m) hh.le, ?_, ?_⟩
    · rw [div_le_one hh]
      calc sgn (s m) * (z m - c m) ≤ |sgn (s m) * (z m - c m)| := le_abs_self _
        _ = |z m - c m| := by rw [abs_mul, abs_sgn, one_mul]
        _ ≤ h := hz m
    · field_simp
  obtain ⟨a0, a00, a01, ha0⟩ := ha 0
  obtain ⟨a1, a10, a11, ha1⟩ := ha 1
  obtain ⟨a2, a20, a21, ha2⟩ := ha 2
  have q0 := sgn_sq (s 0)
  have q1 := sgn_sq (s 1)
  have q2 := sgn_sq (s 2)
  have hzq : n ⬝ᵥ (z - q) = ∑ m, n m * (c m - q m) +
      (n 0 * (z 0 - c 0) + n 1 * (z 1 - c 1) + n 2 * (z 2 - c 2)) := by
    simp only [dotProduct, Pi.sub_apply, Fin.sum_univ_three]; ring
  have hcq : ∀ κ, n ⬝ᵥ (c + h • cornerDir (ax, s) κ - q) = ∑ m, n m * (c m - q m) +
      (n 0 * (h * cornerDir (ax, s) κ 0) + n 1 * (h * cornerDir (ax, s) κ 1) +
        n 2 * (h * cornerDir (ax, s) κ 2)) := by
    intro κ
    simp only [dotProduct, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Fin.sum_univ_three]
    ring
  rw [hzq]
  set g := ∑ m, n m * (c m - q m)
  have hc : ∀ κ, 0 < g + (n 0 * (h * cornerDir (ax, s) κ 0) +
      n 1 * (h * cornerDir (ax, s) κ 1) + n 2 * (h * cornerDir (ax, s) κ 2)) :=
    fun κ => (hcq κ) ▸ hcorner κ
  simp only at hface
  -- For each face axis, bilinear interpolation over the other two axes.
  --
  fin_cases ax
  · have c00 := hc ![false, false, false]
    have c10 := hc ![false, true, false]
    have c01 := hc ![false, false, true]
    have c11 := hc ![false, true, true]
    simp [cornerDir] at c00 c10 c01 c11 hface
    have key := affine_square_pos (g0 := g + n 0 * (h * sgn (s 0)))
      (α := n 1 * (h * sgn (s 1))) (β := n 2 * (h * sgn (s 2)))
      a10 a11 a20 a21 (by linarith) (by linarith) (by linarith) (by linarith)
    have e0 : n 0 * (z 0 - c 0) = n 0 * (h * sgn (s 0)) := by rw [hface]; ring
    have e1 : n 1 * (h * sgn (s 1)) * a1 = n 1 * (z 1 - c 1) := by
      linear_combination (n 1 * sgn (s 1)) * ha1 + (n 1 * (z 1 - c 1)) * q1
    have e2 : n 2 * (h * sgn (s 2)) * a2 = n 2 * (z 2 - c 2) := by
      linear_combination (n 2 * sgn (s 2)) * ha2 + (n 2 * (z 2 - c 2)) * q2
    linarith
  · have c00 := hc ![false, false, false]
    have c10 := hc ![true, false, false]
    have c01 := hc ![false, false, true]
    have c11 := hc ![true, false, true]
    simp [cornerDir] at c00 c10 c01 c11 hface
    have key := affine_square_pos (g0 := g + n 1 * (h * sgn (s 1)))
      (α := n 0 * (h * sgn (s 0))) (β := n 2 * (h * sgn (s 2)))
      a00 a01 a20 a21 (by linarith) (by linarith) (by linarith) (by linarith)
    have e0 : n 1 * (z 1 - c 1) = n 1 * (h * sgn (s 1)) := by rw [hface]; ring
    have e1 : n 0 * (h * sgn (s 0)) * a0 = n 0 * (z 0 - c 0) := by
      linear_combination (n 0 * sgn (s 0)) * ha0 + (n 0 * (z 0 - c 0)) * q0
    have e2 : n 2 * (h * sgn (s 2)) * a2 = n 2 * (z 2 - c 2) := by
      linear_combination (n 2 * sgn (s 2)) * ha2 + (n 2 * (z 2 - c 2)) * q2
    linarith
  · have c00 := hc ![false, false, false]
    have c10 := hc ![true, false, false]
    have c01 := hc ![false, true, false]
    have c11 := hc ![true, true, false]
    simp [cornerDir] at c00 c10 c01 c11 hface
    have key := affine_square_pos (g0 := g + n 2 * (h * sgn (s 2)))
      (α := n 0 * (h * sgn (s 0))) (β := n 1 * (h * sgn (s 1)))
      a00 a01 a10 a11 (by linarith) (by linarith) (by linarith) (by linarith)
    have e0 : n 2 * (z 2 - c 2) = n 2 * (h * sgn (s 2)) := by rw [hface]; ring
    have e1 : n 0 * (h * sgn (s 0)) * a0 = n 0 * (z 0 - c 0) := by
      linear_combination (n 0 * sgn (s 0)) * ha0 + (n 0 * (z 0 - c 0)) * q0
    have e2 : n 1 * (h * sgn (s 1)) * a1 = n 1 * (z 1 - c 1) := by
      linear_combination (n 1 * sgn (s 1)) * ha1 + (n 1 * (z 1 - c 1)) * q1
    linarith

/-- A point of the fence surface lies in a patch of the face it touches,
and an affine function positive at that patch's corners is positive at
the point. -/
lemma patch_of_surface {z c : V} {h : ℝ} (hh : 0 < h)
    (hz : ∀ m, |z m - c m| ≤ h) {ax : Fin 3} (hax : |z ax - c ax| = h) :
    ∃ P : Patch, P.1 = ax ∧ z ax - c ax = sgn (P.2 ax) * h ∧ ∀ n q : V,
      ((∀ κ, 0 < n ⬝ᵥ (c + h • cornerDir P κ - q)) → 0 < n ⬝ᵥ (z - q)) := by
  have hface : z ax - c ax = sgn (decide (0 ≤ z ax - c ax)) * h := by
    have := sgn_mul_abs (z ax - c ax)
    rw [hax] at this
    exact this.symm
  refine ⟨(ax, fun m => decide (0 ≤ z m - c m)), rfl, hface, fun n q hc => ?_⟩
  exact patch_pos _ hh hz hface (fun m => by
    simp only
    rw [sgn_mul_self_abs]; exact abs_nonneg _) hc

end Rng3d
