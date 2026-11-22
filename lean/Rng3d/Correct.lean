/-
Correctness of the SPoIF model: for points in `[0,1)^3`, the edges the
procedure reports at anchor `i` are exactly the RNG edges at `i`.
No general-position assumption is needed.
-/
import Rng3d.Fence

open Finset

namespace Rng3d

variable {N : ℕ}

lemma hR_pos (hN : 1 ≤ N) (r : ℕ) : 0 < hR N r := by
  unfold hR; have := ds_pos hN; positivity

lemma hR_mono (hN : 1 ≤ N) {r r' : ℕ} (h : r' ≤ r) : hR N r' ≤ hR N r := by
  unfold hR
  have := ds_pos hN
  have : (r' : ℝ) ≤ r := by exact_mod_cast h
  nlinarith

lemma half_ds_le_hR (r : ℕ) (hN : 1 ≤ N) : ds N / 2 ≤ hR N r := by
  unfold hR
  have := ds_pos hN
  have : (0 : ℝ) ≤ r := by positivity
  nlinarith

lemma convex_mem_cube {p w : V} {t : ℝ} (hp : p ∈ unitCube) (hw : w ∈ unitCube)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 - t) • p + t • w ∈ unitCube := by
  intro m
  obtain ⟨p0, p1⟩ := hp m
  obtain ⟨w0, w1⟩ := hw m
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) p0, mul_nonneg ht0 w0]
  · nlinarith [mul_le_mul_of_nonneg_left (le_max_left (p m) (w m)) (sub_nonneg.mpr ht1),
      mul_le_mul_of_nonneg_left (le_max_right (p m) (w m)) ht0, max_lt p1 w1]

/-- A patch secured by a point at radius `r' ≤ r` stays secured at `r`
(Theorem 2 of the paper). -/
lemma secures_grow (hN : 1 ≤ N) {x : Fin N → V} {i j : Fin N} {r' r : ℕ} {P : Patch}
    (hr : r' ≤ r) (hs : securesBy x i r' P j) (κ : Fin 3 → Bool) :
    0 < (x j - x i) ⬝ᵥ (center N (x i) + hR N r • cornerDir P κ - x j) := by
  obtain ⟨h0, h1⟩ := hs κ
  have hpos := hR_pos hN r'
  set L := hR N r / hR N r'
  have hL : 1 ≤ L := by
    rw [le_div_iff₀ hpos, one_mul]; exact hR_mono hN hr
  have hscale : hR N r • cornerDir P κ = L • (hR N r' • cornerDir P κ) := by
    rw [smul_smul]; congr 1; simp only [L]; rw [div_mul_cancel₀ _ hpos.ne']
  rw [hscale]
  exact scale_secure hL h0 h1

/-- An out-of-bounds patch at radius `r' ≤ r` has its whole face plane
outside the unit cube at radius `r`. -/
lemma oob_face (hN : 1 ≤ N) {x : Fin N → V} {i : Fin N} {r' r : ℕ} {P : Patch}
    (hxi : x i ∈ unitCube) (hr : r' ≤ r) (hO : OOB x i r' P) {z : V}
    (hface : z P.1 - center N (x i) P.1 = sgn (P.2 P.1) * hR N r) :
    z ∉ unitCube := by
  intro hz
  have hc := hO (fun _ => false)
  apply hc
  intro m
  have hcm := center_mem hN hxi m
  have hmono := hR_mono hN hr
  have hpos := hR_pos hN r'
  by_cases hm : m = P.1
  · subst hm
    obtain ⟨z0, z1⟩ := hz P.1
    simp only [corner, cornerDir, ite_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold sgn at hface ⊢
    cases hb : P.2 P.1 <;> simp only [hb] at hface ⊢ <;> norm_num at hface ⊢ <;>
      constructor <;> nlinarith
  · simp only [corner, cornerDir, hm, ite_false, Bool.false_eq_true, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_zero, add_zero]
    exact ⟨hcm.1.le, hcm.2⟩

/-- Every RNG neighbour of the anchor is collected by the main loop. -/
lemma rng_mem_cand (hN : 1 ≤ N) {x : Fin N → V} (hx : ∀ j, x j ∈ unitCube)
    {i k : Fin N} (hk : isRNGEdge x i k) : k ∈ cand x i := by
  obtain ⟨hik, hblk⟩ := hk
  unfold cand
  rw [mem_Q]
  refine ⟨Ne.symm hik, ?_⟩
  by_contra hfar
  push Not at hfar
  set R := Rstar x i
  have hspec : allSecured x i R ∨ gridN N - 1 ≤ R := Rstar_spec x i
  rcases hspec with hsec | hgrid
  swap
  · have := cheb_le_grid hN (hx k) (hx i); omega
  set c := center N (x i)
  set h := hR N R
  have hh := hR_pos hN R
  obtain ⟨m0, hm0⟩ := far_of_cheb hN hfar
  have hp : ∀ m, |x i m - c m| ≤ h := fun m =>
    (abs_center_sub hN (x i) m).trans (half_ds_le_hR R hN)
  obtain ⟨t, ht0, ht1, hzin, ax, hax⟩ := segment_cross hp ⟨m0, hm0⟩
  set z := (1 - t) • x i + t • x k
  have hzc : z ∈ unitCube := convex_mem_cube (hx i) (hx k) ht0 ht1
  obtain ⟨P, hP1, hface, hpos⟩ := patch_of_surface hh hzin hax
  obtain ⟨r', hr', hcase⟩ := hsec P
  rcases hcase with hO | ⟨j, hjQ, hj⟩
  · exact oob_face hN (hx i) hr' hO (hP1 ▸ hface) hzc
  · have hjQ' := hjQ
    rw [mem_Q] at hjQ'
    have hcor : ∀ κ, 0 < (x j - x i) ⬝ᵥ (c + h • cornerDir P κ - x j) :=
      fun κ => secures_grow hN hr' hj κ
    have hzpos := hpos (x j - x i) (x j) hcor
    have hji : x j ≠ x i := by
      intro he
      have := (hj (fun _ => false)).1
      rw [he, sub_self, zero_dotProduct] at this
      exact lt_irrefl 0 this
    have hwk := affine_pos_of_segment ht0 ht1 (self_side_neg hji) hzpos
    have hjk : j ≠ k := by
      intro he; subst he; simp at hwk
    exact hblk j hjQ'.1 hjk (plane_blocks hwk)

lemma ed_le_maxd {x : Fin N → V} {i k : Fin N} (hk : k ∈ cand x i) :
    ed (x i) (x k) ≤ maxd x i := by
  unfold maxd
  have h := Finset.le_sup (f := fun j => (ed (x i) (x j)).toNNReal) hk
  have h' : ((ed (x i) (x k)).toNNReal : ℝ) ≤
      (((cand x i).sup fun j => (ed (x i) (x j)).toNNReal : NNReal) : ℝ) := by
    exact_mod_cast h
  rw [Real.coe_toNNReal (ed (x i) (x k)) (Real.sqrt_nonneg _)] at h'
  exact h'

/-- Main correctness theorem: the procedure reports exactly the RNG
edges at the anchor. -/
theorem output_iff (hN : 1 ≤ N) {x : Fin N → V} (hx : ∀ j, x j ∈ unitCube)
    (i k : Fin N) : k ∈ output x i ↔ isRNGEdge x i k := by
  constructor
  · intro hk
    rw [mem_output] at hk
    obtain ⟨hkc, hnb⟩ := hk
    have hkc' := hkc
    unfold cand at hkc'
    rw [mem_Q] at hkc'
    refine ⟨Ne.symm hkc'.1, fun j hji hjk hb => ?_⟩
    -- A blocker is closer to the anchor than the candidate, hence within
    -- the saboteur extension.
    --
    have hlt := ed_lt_of_dd_lt hb.1
    have hmax := ed_le_maxd hkc
    have hclose : ∀ m, |x j m - x i m| ≤ maxd x i := fun m => by
      rw [abs_sub_comm]
      exact (abs_coord_le_ed _ _ m).trans (hlt.le.trans hmax)
    have hcheb := cheb_le_of_close hN hclose
    have hjb : j ∈ blk x i := by
      unfold blk Tx
      rw [mem_Q]
      exact ⟨hji, hcheb.trans (le_max_right _ _)⟩
    exact hnb j hjb hjk hb
  · intro hk
    have hkc := rng_mem_cand hN hx hk
    rw [mem_output]
    refine ⟨hkc, fun j hj hjk => ?_⟩
    unfold blk at hj
    rw [mem_Q] at hj
    exact hk.2 j hj.1 hjk

end Rng3d
