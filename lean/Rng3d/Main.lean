/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Rng3d.Expect

@[expose] public section

/-!
Main theorem: the expected operation count of SPoIF on `N` independent
uniform points in `[0,1)^3` is at most `C · N` for an absolute constant
`C`.
-/

open Finset MeasureTheory ProbabilityTheory

namespace Rng3d

open Classical

variable {N : ℕ}

abbrev Face := Fin 3 × Bool

/-- Box containing all points within cell distance `2r + 3` of cell `κ`. -/
noncomputable def Bset (N : ℕ) (κ : Fin 3 → Fin (gridN N)) (r : ℕ) : Set V :=
  nearBox (cellCenter κ) (hR N (2 * r + 3))

/-- Securing region of face `F` at fence radius `r - 1` around cell `κ`. -/
noncomputable def Sset (N : ℕ) (κ : Fin 3 → Fin (gridN N)) (r : ℕ) (F : Face) : Set V :=
  secRegion (cellCenter κ) (hR N (r - 1)) F.1 F.2

def faceOK (N : ℕ) (κ : Fin 3 → Fin (gridN N)) (r : ℕ) (F : Face) : Prop :=
  faceIn (cellCenter κ) (hR N (r - 1)) F.1 F.2

noncomputable def gF (N : ℕ) (κ : Fin 3 → Fin (gridN N)) (r : ℕ) (F : Face) (y : V) :
    ENNReal :=
  eFac (Bset N κ r) y * (Sset N κ r F)ᶜ.indicator 1 y

/-- Product of one-coordinate factors: the anchor is in cell `κ`, every
other point contributes `g`. -/
noncomputable def termF (i : Fin N) (κ : Fin 3 → Fin (gridN N)) (g : V → ENNReal)
    (x : Fin N → V) : ENNReal :=
  ∏ j, (if j = i then (cellBox κ).indicator 1 else g) (x j)

noncomputable def inner (i : Fin N) (r : ℕ) (κ : Fin 3 → Fin (gridN N)) (x : Fin N → V) :
    ENNReal :=
  if r < 17 then termF i κ (eFac (Bset N κ r)) x
  else ∑ F : Face, if faceOK N κ r F then termF i κ (gF N κ r F) x else 0

/-- The dominating function for anchor `i`. -/
noncomputable def domG (i : Fin N) (x : Fin N → V) : ENNReal :=
  ∑ r ∈ range (gridN N), ENNReal.ofReal (((r : ℝ) + 2) ^ 4) *
    ∑ κ : Fin 3 → Fin (gridN N), inner i r κ x

lemma Bset_measurable (κ : Fin 3 → Fin (gridN N)) (r : ℕ) : MeasurableSet (Bset N κ r) :=
  nearBox_measurable _ _

lemma Sset_measurable (κ : Fin 3 → Fin (gridN N)) (r : ℕ) (F : Face) :
    MeasurableSet (Sset N κ r F) :=
  secRegion_measurable _ _ _ _

lemma gF_measurable (κ : Fin 3 → Fin (gridN N)) (r : ℕ) (F : Face) :
    Measurable (gF N κ r F) :=
  (eFac_measurable (Bset_measurable κ r)).mul
    (measurable_one.indicator (Sset_measurable κ r F).compl)

lemma factor_measurable (i j : Fin N) (κ : Fin 3 → Fin (gridN N)) {g : V → ENNReal}
    (hg : Measurable g) :
    Measurable (if j = i then (cellBox κ).indicator 1 else g) := by
  split_ifs
  · exact measurable_one.indicator (cellBox_measurable κ)
  · exact hg

lemma termF_measurable (i : Fin N) (κ : Fin 3 → Fin (gridN N)) {g : V → ENNReal}
    (hg : Measurable g) : Measurable (termF i κ g) := by
  unfold termF
  exact Finset.measurable_prod _ fun j _ =>
    (factor_measurable i j κ hg).comp (measurable_pi_apply j)

lemma inner_measurable (i : Fin N) (r : ℕ) (κ : Fin 3 → Fin (gridN N)) :
    Measurable (inner i r κ) := by
  unfold inner
  split_ifs
  · exact termF_measurable i κ (eFac_measurable (Bset_measurable κ r))
  · refine Finset.measurable_sum _ fun F _ => ?_
    split_ifs
    · exact termF_measurable i κ (gF_measurable κ r F)
    · exact measurable_const

lemma domG_measurable (i : Fin N) : Measurable (domG i) := by
  unfold domG
  exact Finset.measurable_sum _ fun r _ => measurable_const.mul
    (Finset.measurable_sum _ fun κ _ => inner_measurable i r κ)

lemma termF_eq (i : Fin N) (κ : Fin 3 → Fin (gridN N)) (g : V → ENNReal) (x : Fin N → V) :
    termF i κ g x = (cellBox κ).indicator 1 (x i) * ∏ j ∈ {i}ᶜ, g (x j) := by
  unfold termF
  rw [Fintype.prod_eq_mul_prod_compl i]
  simp only [↓reduceIte]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_compl, Finset.mem_singleton] at hj
  simp [hj]

lemma card_compl_single (i : Fin N) : ({i}ᶜ : Finset (Fin N)).card = N - 1 := by
  rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]

lemma lintegral_termF (i : Fin N) (κ : Fin 3 → Fin (gridN N)) {g : V → ENNReal}
    (hg : Measurable g) :
    ∫⁻ x, termF i κ g x ∂(PN N) = μc (cellBox κ) * (∫⁻ y, g y ∂μc) ^ (N - 1) := by
  unfold termF
  rw [lintegral_pi_prod _ fun j => factor_measurable i j κ hg,
    Fintype.prod_eq_mul_prod_compl i]
  simp only [↓reduceIte]
  rw [lintegral_indicator_one (cellBox_measurable κ)]
  congr 1
  rw [Finset.prod_congr rfl (g := fun _ => ∫⁻ y, g y ∂μc) fun j hj => by
    rw [Finset.mem_compl, Finset.mem_singleton] at hj; simp [hj]]
  rw [Finset.prod_const, card_compl_single]

/-! ### Pointwise domination -/

theorem cost_le_domG (hN : 1 ≤ N) {x : Fin N → V} (hx : ∀ j, x j ∈ unitCube) (i : Fin N) :
    (cost x i : ENNReal) ≤ ENNReal.ofReal (1000 * Clam) * domG i x := by
  set R := Rstar x i
  set X := nearCount x i (2 * R + 3)
  obtain ⟨κ0, hκ0, hcen⟩ := exists_cell hN (hx i)
  set B := Bset N κ0 R
  -- The count of near points is at most the number of other points in `B`.
  --
  set K : ℝ := ∑ j ∈ ({i}ᶜ : Finset (Fin N)), B.indicator 1 (x j)
  have hXK : (X : ℝ) ≤ K := by
    have hsub : Q x i (2 * R + 3) ⊆ {i}ᶜ := fun j hj => by
      rw [mem_Q] at hj; simp [hj.1]
    have hX : (X : ℝ) = ∑ j ∈ Q x i (2 * R + 3), B.indicator 1 (x j) := by
      rw [show (X : ℝ) = ∑ _j ∈ Q x i (2 * R + 3), (1 : ℝ) by simp [X, nearCount]]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [mem_Q] at hj
      have : x j ∈ B := by
        have := mem_nearBox_of_cheb hN hj.2
        rw [hcen] at this; exact this
      simp [Set.indicator_of_mem this]
    rw [hX]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hprod : ∏ j ∈ ({i}ᶜ : Finset (Fin N)), eFac B (x j) =
      ENNReal.ofReal (Real.exp (lam * K)) := by
    unfold eFac
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le), ← Real.exp_sum,
      Finset.mul_sum]
  have hsq : ((X + 1 : ℕ) : ENNReal) ^ 2 ≤
      ENNReal.ofReal Clam * ∏ j ∈ ({i}ᶜ : Finset (Fin N)), eFac B (x j) := by
    rw [hprod, ← ENNReal.ofReal_mul Clam_pos.le, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_pow (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    exact sq_le_Clam_exp (by positivity) hXK
  -- The inner term at the actual radius and cell dominates the product.
  --
  have hinner : ∏ j ∈ ({i}ᶜ : Finset (Fin N)), eFac B (x j) ≤ inner i R κ0 x := by
    unfold inner
    split_ifs with hR17
    · rw [termF_eq, Set.indicator_of_mem hκ0, Pi.one_apply, one_mul]
    · push Not at hR17
      have hlt : R - 1 < R := by omega
      have hns := Rstar_min x i hlt
      push Not at hns
      obtain ⟨m, σ, hfin, hout⟩ := unsecured_face hN (by omega : 16 ≤ R - 1) hns.1
      rw [hcen] at hfin hout
      have hok : faceOK N κ0 R (m, σ) := hfin
      refine le_trans ?_ (Finset.single_le_sum (f := fun F : Face =>
        if faceOK N κ0 R F then termF i κ0 (gF N κ0 R F) x else 0)
        (fun _ _ => bot_le) (Finset.mem_univ (m, σ)))
      simp only [hok, ↓reduceIte]
      rw [termF_eq, Set.indicator_of_mem hκ0, Pi.one_apply, one_mul]
      refine Finset.prod_le_prod fun j hj => ?_
      rw [Finset.mem_compl, Finset.mem_singleton] at hj
      unfold gF
      have : x j ∈ (Sset N κ0 R (m, σ))ᶜ := hout j hj
      rw [Set.indicator_of_mem this, Pi.one_apply, mul_one]
  have hRn : R ∈ range (gridN N) := by
    rw [mem_range]; have := Rstar_le x i; have := gridN_pos hN; omega
  have hdom : ENNReal.ofReal (((R : ℝ) + 2) ^ 4) * inner i R κ0 x ≤ domG i x := by
    unfold domG
    refine le_trans ?_ (Finset.single_le_sum (f := fun r : ℕ => ENNReal.ofReal (((r : ℝ) + 2) ^ 4) *
      ∑ κ : Fin 3 → Fin (gridN N), inner i r κ x) (fun _ _ => bot_le) hRn)
    gcongr
    exact Finset.single_le_sum (f := fun κ => inner i R κ x)
      (fun _ _ => bot_le) (Finset.mem_univ κ0)
  have hcost : (cost x i : ENNReal) ≤ 1000 * ((R + 2 : ℕ) : ENNReal) ^ 4 *
      ((X + 1 : ℕ) : ENNReal) ^ 2 := by
    exact_mod_cast cost_le hN x i
  have hR4 : ((R + 2 : ℕ) : ENNReal) ^ 4 = ENNReal.ofReal (((R : ℝ) + 2) ^ 4) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity)]; push_cast; rfl
  calc (cost x i : ENNReal)
      ≤ 1000 * ((R + 2 : ℕ) : ENNReal) ^ 4 * ((X + 1 : ℕ) : ENNReal) ^ 2 := hcost
    _ ≤ 1000 * ENNReal.ofReal (((R : ℝ) + 2) ^ 4) *
          (ENNReal.ofReal Clam * inner i R κ0 x) := by
        rw [hR4]; gcongr; exact hsq.trans (by gcongr)
    _ = ENNReal.ofReal (1000 * Clam) *
          (ENNReal.ofReal (((R : ℝ) + 2) ^ 4) * inner i R κ0 x) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        simp only [ENNReal.ofReal_ofNat]
        ring
    _ ≤ ENNReal.ofReal (1000 * Clam) * domG i x := by gcongr

/-! ### Integrating the dominating function -/

lemma hR_lt_one (hN : 1 ≤ N) {r : ℕ} (hr : r < gridN N) : hR N (r - 1) < 1 := by
  have hd := ds_mul hN
  have hdp := ds_pos hN
  have : ((r - 1 : ℕ) : ℝ) + 1 / 2 < gridN N := by
    have : (r - 1 : ℕ) + 1 ≤ gridN N := by omega
    have : ((r - 1 : ℕ) : ℝ) + 1 ≤ gridN N := by exact_mod_cast this
    linarith
  unfold hR
  nlinarith

lemma pow_le_exp_mul {z e : ℝ} (hz : 0 ≤ z) (hze : z ≤ 1 + e) (k : ℕ) :
    z ^ k ≤ Real.exp (k * e) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hz (hze.trans (by linarith [Real.add_one_le_exp e])) k

lemma lintegral_inner_le (hN : 1 ≤ N) (i : Fin N) {r : ℕ} (hr : r < gridN N)
    (κ : Fin 3 → Fin (gridN N)) :
    ∫⁻ x, inner i r κ x ∂(PN N) ≤ μc (cellBox κ) * ENNReal.ofReal (tailB r) := by
  set b := (2 * hR N (2 * r + 3)) ^ 3
  have hb0 : 0 ≤ b := by have := hR_pos hN (2 * r + 3); positivity
  have ha0 := alpha_nonneg
  have hB : μc (Bset N κ r) ≤ ENNReal.ofReal b :=
    μc_nearBox_le _ (hR_pos hN _).le
  have hk : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hN]; simp
  have hαB : ENNReal.ofReal alpha * μc (Bset N κ r) ≤ ENNReal.ofReal (alpha * b) := by
    rw [ENNReal.ofReal_mul ha0]; gcongr
  unfold inner
  split_ifs with h17
  · rw [lintegral_termF i κ (eFac_measurable (Bset_measurable κ r)),
      lintegral_eFac (Bset_measurable κ r)]
    gcongr
    have h1 : 1 + ENNReal.ofReal alpha * μc (Bset N κ r) ≤ ENNReal.ofReal (1 + alpha * b) := by
      rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]; gcongr
    calc (1 + ENNReal.ofReal alpha * μc (Bset N κ r)) ^ (N - 1)
        ≤ ENNReal.ofReal (1 + alpha * b) ^ (N - 1) := by gcongr
      _ = ENNReal.ofReal ((1 + alpha * b) ^ (N - 1)) :=
          (ENNReal.ofReal_pow (by positivity) _).symm
      _ ≤ ENNReal.ofReal (tailB r) := by
          apply ENNReal.ofReal_le_ofReal
          have := pow_le_exp_mul (z := 1 + alpha * b) (e := alpha * b) (by positivity) le_rfl
            (N - 1)
          rw [hk] at this
          have hh := head_exponent hN h17
          unfold tailB; simp only [h17, ↓reduceIte]
          calc (1 + alpha * b) ^ (N - 1) ≤ Real.exp (((N : ℝ) - 1) * (alpha * b)) := this
            _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hh
            _ ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  · push Not at h17
    rw [lintegral_finsetSum _ fun F _ => by
      split_ifs
      · exact termF_measurable i κ (gF_measurable κ r F)
      · exact measurable_const]
    set e := Real.exp (-(cdec * r))
    have hterm : ∀ F : Face, ∫⁻ x, (if faceOK N κ r F then termF i κ (gF N κ r F) x else 0)
        ∂(PN N) ≤ μc (cellBox κ) * ENNReal.ofReal e := by
      intro F
      split_ifs with hok
      swap
      · simp
      rw [lintegral_termF i κ (gF_measurable κ r F)]
      gcongr
      set h := hR N (r - 1)
      have hh := hR_pos hN (r - 1)
      have h1 := hR_lt_one hN hr
      set s := h / 10 * (h / 20) * (h / 20)
      have hs0 : 0 ≤ s := by positivity
      have hs1 : s ≤ 1 := by
        have : h ^ 3 ≤ 1 := pow_le_one₀ hh.le h1.le
        simp only [s]; nlinarith
      have hS : μc (Sset N κ r F) = ENNReal.ofReal s :=
        μc_secRegion (cellCenter_mem hN κ) hh h1 hok
      have hint := lintegral_eFac_compl (Bset_measurable κ r) (Sset_measurable κ r F)
      have hz : (1 - μc (Sset N κ r F)) + ENNReal.ofReal alpha * μc (Bset N κ r) ≤
          ENNReal.ofReal (1 - s + alpha * b) := by
        rw [hS, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hs0,
          ENNReal.ofReal_add (by linarith) (by positivity)]
        gcongr
      have hgF : ∫⁻ y, gF N κ r F y ∂μc ≤ ENNReal.ofReal (1 - s + alpha * b) :=
        (hint.trans hz)
      calc (∫⁻ y, gF N κ r F y ∂μc) ^ (N - 1)
          ≤ ENNReal.ofReal (1 - s + alpha * b) ^ (N - 1) := by gcongr
        _ = ENNReal.ofReal ((1 - s + alpha * b) ^ (N - 1)) :=
            (ENNReal.ofReal_pow (by nlinarith) _).symm
        _ ≤ ENNReal.ofReal e := by
            apply ENNReal.ofReal_le_ofReal
            have := pow_le_exp_mul (z := 1 - s + alpha * b) (e := alpha * b - s)
              (by nlinarith) (by linarith) (N - 1)
            rw [hk] at this
            have ht := tail_exponent hN h17 hr
            exact this.trans (Real.exp_le_exp.mpr ht)
    calc ∑ F : Face, ∫⁻ x, (if faceOK N κ r F then termF i κ (gF N κ r F) x else 0) ∂(PN N)
        ≤ ∑ _F : Face, μc (cellBox κ) * ENNReal.ofReal e := Finset.sum_le_sum fun F _ => hterm F
      _ = μc (cellBox κ) * ENNReal.ofReal (tailB r) := by
          rw [Finset.sum_const, Finset.card_univ]
          have : Fintype.card Face = 6 := by simp [Face]
          rw [this]
          unfold tailB
          simp only [show ¬ r < 17 by omega, ↓reduceIte]
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp only [nsmul_eq_mul, ENNReal.ofReal_ofNat]
          ring

/-- Constant of the per-anchor bound. -/
noncomputable def C0 : ℝ := ∑' r : ℕ, ((r : ℝ) + 2) ^ 4 * tailB r

lemma C0_nonneg : 0 ≤ C0 :=
  tsum_nonneg fun r => mul_nonneg (by positivity) (tailB_nonneg r)

lemma lintegral_domG_le (hN : 1 ≤ N) (i : Fin N) :
    ∫⁻ x, domG i x ∂(PN N) ≤ ENNReal.ofReal C0 := by
  unfold domG
  rw [lintegral_finsetSum (f := fun (r : ℕ) x => ENNReal.ofReal (((r : ℝ) + 2) ^ 4) *
      ∑ κ : Fin 3 → Fin (gridN N), inner i r κ x) _
    (fun r _ => Measurable.const_mul
      (Finset.measurable_sum _ fun κ _ => inner_measurable i r κ) _)]
  have hr : ∀ r ∈ range (gridN N), ∫⁻ x, ENNReal.ofReal (((r : ℝ) + 2) ^ 4) *
      ∑ κ : Fin 3 → Fin (gridN N), inner i r κ x ∂(PN N) ≤
      ENNReal.ofReal (((r : ℝ) + 2) ^ 4 * tailB r) := by
    intro r hr
    rw [mem_range] at hr
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun κ _ => inner_measurable i r κ),
      lintegral_finsetSum _ fun κ _ => inner_measurable i r κ,
      ENNReal.ofReal_mul (by positivity)]
    gcongr
    calc ∑ κ : Fin 3 → Fin (gridN N), ∫⁻ x, inner i r κ x ∂(PN N)
        ≤ ∑ κ : Fin 3 → Fin (gridN N), μc (cellBox κ) * ENNReal.ofReal (tailB r) :=
          Finset.sum_le_sum fun κ _ => lintegral_inner_le hN i hr κ
      _ = (∑ κ : Fin 3 → Fin (gridN N), μc (cellBox κ)) * ENNReal.ofReal (tailB r) := by
          rw [Finset.sum_mul]
      _ ≤ 1 * ENNReal.ofReal (tailB r) := by gcongr; exact sum_cellBox_le hN
      _ = ENNReal.ofReal (tailB r) := one_mul _
  calc ∑ r ∈ range (gridN N), ∫⁻ x, ENNReal.ofReal (((r : ℝ) + 2) ^ 4) *
        ∑ κ : Fin 3 → Fin (gridN N), inner i r κ x ∂(PN N)
      ≤ ∑ r ∈ range (gridN N), ENNReal.ofReal (((r : ℝ) + 2) ^ 4 * tailB r) :=
        Finset.sum_le_sum hr
    _ ≤ ∑' r : ℕ, ENNReal.ofReal (((r : ℝ) + 2) ^ 4 * tailB r) := ENNReal.sum_le_tsum _
    _ = ENNReal.ofReal C0 := by
        rw [C0, ENNReal.ofReal_tsum_of_nonneg
          (fun r => mul_nonneg (by positivity) (tailB_nonneg r)) summable_tail]

/-! ### Main theorem -/

instance (N : ℕ) : IsProbabilityMeasure (PN N) := by unfold PN; infer_instance

/-- **Expected linear time.** For `N` independent uniform points in the
unit cube, the expected operation count of the whole algorithm (grid
allocation, binning, and the SPoIF procedure at every anchor) is at most
`C · N`, for a constant `C` independent of `N`. -/
theorem expected_linear :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫⁻ x, (totalCost x : ENNReal) ∂(PN N) ≤ ENNReal.ofReal (C * N) := by
  set K := 1000 * Clam
  have hK : 0 ≤ K := by have := Clam_pos; positivity
  refine ⟨9 + K * C0, by have := C0_nonneg; positivity, fun N hN => ?_⟩
  have hpt : ∀ᵐ x ∂(PN N), (totalCost x : ENNReal) ≤
      (9 * N : ENNReal) + ∑ i, ENNReal.ofReal K * domG i x := by
    filter_upwards [ae_mem_cube] with x hx
    have h8 := gridN_cube_le hN
    unfold totalCost
    push_cast
    have hsum : ∑ i, (cost x i : ENNReal) ≤ ∑ i, ENNReal.ofReal K * domG i x :=
      Finset.sum_le_sum fun i _ => cost_le_domG hN hx i
    have hg : (N : ENNReal) + (gridN N : ENNReal) ^ 3 ≤ 9 * N := by
      have : N + gridN N ^ 3 ≤ 9 * N := by omega
      exact_mod_cast this
    exact add_le_add hg hsum
  calc ∫⁻ x, (totalCost x : ENNReal) ∂(PN N)
      ≤ ∫⁻ x, ((9 * N : ENNReal) + ∑ i, ENNReal.ofReal K * domG i x) ∂(PN N) :=
        lintegral_mono_ae hpt
    _ = (9 * N : ENNReal) + ∑ i, ENNReal.ofReal K * ∫⁻ x, domG i x ∂(PN N) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_finsetSum (f := fun i x => ENNReal.ofReal K * domG i x) _
            (fun i _ => (domG_measurable i).const_mul _)]
        simp only [lintegral_const_mul _ (domG_measurable _)]
    _ ≤ (9 * N : ENNReal) + ∑ _i : Fin N, ENNReal.ofReal K * ENNReal.ofReal C0 := by
        gcongr with i; exact lintegral_domG_le hN i
    _ = ENNReal.ofReal ((9 + K * C0) * N) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          show (9 : ENNReal) = ENNReal.ofReal 9 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by have := C0_nonneg; positivity)]
        congr 1; ring

end Rng3d
