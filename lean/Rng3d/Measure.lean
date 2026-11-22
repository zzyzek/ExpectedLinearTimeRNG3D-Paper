/-
Measure-theoretic setting: `N` independent uniform points in `[0,1)^3`,
the factorisation of the integral of a product of one-coordinate
functions, grid cells, and the integrals of the dominating factors.
-/
import Rng3d.CostBound

open Finset MeasureTheory ProbabilityTheory

namespace Rng3d

variable {N : ℕ}

lemma unitCube_eq : unitCube = Set.univ.pi fun _ : Fin 3 => Set.Ico (0 : ℝ) 1 := by
  ext y; simp [unitCube, Set.mem_pi]

lemma unitCube_measurable : MeasurableSet unitCube := by
  rw [unitCube_eq]; exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- Uniform distribution on the unit cube. -/
noncomputable def μc : Measure V := volume.restrict unitCube

instance : IsProbabilityMeasure μc := by
  constructor
  rw [μc, Measure.restrict_apply_univ, unitCube_eq, volume_pi_pi]
  simp

/-- `N` independent uniform points. -/
noncomputable def PN (N : ℕ) : Measure (Fin N → V) := Measure.pi fun _ => μc

lemma lintegral_pi_prod (f : Fin N → V → ENNReal) (hf : ∀ j, Measurable (f j)) :
    ∫⁻ x, ∏ j, f j (x j) ∂(PN N) = ∏ j, ∫⁻ y, f j y ∂μc := by
  have hX : iIndepFun (fun j (ω : Fin N → V) => f j (ω j)) (PN N) :=
    iIndepFun_pi (μ := fun _ => μc) (X := f) fun j => (hf j).aemeasurable
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun univ _ hX
    (fun j => (hf j).comp (measurable_pi_apply j))]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact (measurePreserving_eval (fun _ : Fin N => μc) j).lintegral_comp (hf j)

lemma ae_mem_cube : ∀ᵐ x ∂(PN N), ∀ j, x j ∈ unitCube := by
  rw [ae_all_iff]
  intro j
  have h0 : μc unitCubeᶜ = 0 := by
    rw [μc, Measure.restrict_apply unitCube_measurable.compl]; simp
  have := Measure.pi_eval_preimage_null (fun _ : Fin N => μc) (i := j) h0
  rw [ae_iff]
  simpa [PN, Set.preimage, Function.eval] using this

/-! ### Grid size -/

lemma gridN_le (N : ℕ) : gridN N ≤ N := by
  apply gridN_min
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ 3 := Nat.pow_le_pow_right h (by norm_num)

lemma gridN_cube_le (hN : 1 ≤ N) : gridN N ^ 3 ≤ 8 * N := by
  have hn := gridN_pos hN
  rcases Nat.lt_or_ge (gridN N) 2 with h | h
  · have : gridN N = 1 := by omega
    rw [this]; omega
  · have hmin : ¬ N ≤ (gridN N - 1) ^ 3 := Nat.find_min (exists_grid N) (by
      show gridN N - 1 < Nat.find (exists_grid N); unfold gridN at h ⊢; omega)
    push Not at hmin
    have h2 : gridN N ≤ 2 * (gridN N - 1) := by omega
    calc gridN N ^ 3 ≤ (2 * (gridN N - 1)) ^ 3 := Nat.pow_le_pow_left h2 3
      _ = 8 * (gridN N - 1) ^ 3 := by ring
      _ ≤ 8 * N := by omega

lemma ds_cube (hN : 1 ≤ N) : (gridN N : ℝ) ^ 3 * ds N ^ 3 = 1 := by
  rw [← mul_pow, ds_mul hN, one_pow]

/-! ### Cells -/

noncomputable def cellBox (κ : Fin 3 → Fin (gridN N)) : Set V :=
  Set.univ.pi fun a => Set.Ico (((κ a : ℕ) : ℝ) * ds N) ((((κ a : ℕ) : ℝ) + 1) * ds N)

noncomputable def cellCenter (κ : Fin 3 → Fin (gridN N)) : V :=
  fun a => (((κ a : ℕ) : ℝ) + 1 / 2) * ds N

lemma cellBox_measurable (κ : Fin 3 → Fin (gridN N)) : MeasurableSet (cellBox κ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma exists_cell (hN : 1 ≤ N) {y : V} (hy : y ∈ unitCube) :
    ∃ κ : Fin 3 → Fin (gridN N), y ∈ cellBox κ ∧ center N y = cellCenter κ := by
  have hr := fun a => cell_range hN hy a
  refine ⟨fun a => ⟨(cellOf N y a).toNat, by have := hr a; omega⟩, ?_, ?_⟩
  · intro a _
    have hc : (((cellOf N y a).toNat : ℕ) : ℝ) = (cellOf N y a : ℝ) := by
      have : (((cellOf N y a).toNat : ℕ) : ℤ) = cellOf N y a := Int.toNat_of_nonneg (hr a).1
      exact_mod_cast this
    simp only [Set.mem_Ico, hc]
    exact cell_bounds hN y a
  · funext a
    have : (((cellOf N y a).toNat : ℕ) : ℤ) = cellOf N y a := Int.toNat_of_nonneg (hr a).1
    simp only [center, cellCenter]
    congr 2
    exact_mod_cast this.symm

lemma sum_cellBox_le (hN : 1 ≤ N) :
    ∑ κ : Fin 3 → Fin (gridN N), μc (cellBox κ) ≤ 1 := by
  have hdp := ds_pos hN
  have hv : ∀ κ : Fin 3 → Fin (gridN N), μc (cellBox κ) ≤ ENNReal.ofReal (ds N) ^ 3 := by
    intro κ
    calc μc (cellBox κ) ≤ volume (cellBox κ) := Measure.restrict_apply_le _ _
      _ = ENNReal.ofReal (ds N) ^ 3 := by
        rw [cellBox, volume_pi_pi]
        simp only [Real.volume_Ico, Fin.prod_univ_three]
        ring_nf
  calc ∑ κ : Fin 3 → Fin (gridN N), μc (cellBox κ)
      ≤ ∑ _κ : Fin 3 → Fin (gridN N), ENNReal.ofReal (ds N) ^ 3 := sum_le_sum fun κ _ => hv κ
    _ = (gridN N : ENNReal) ^ 3 * ENNReal.ofReal (ds N) ^ 3 := by
        simp [Finset.card_univ, Fintype.card_fin]
    _ = 1 := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_pow hdp.le, ← ENNReal.ofReal_mul (by positivity), ds_cube hN,
          ENNReal.ofReal_one]

/-! ### Boxes around the anchor cell -/

noncomputable def nearBox (c : V) (H : ℝ) : Set V :=
  Set.univ.pi fun a => Set.Icc (c a - H) (c a + H)

lemma nearBox_measurable (c : V) (H : ℝ) : MeasurableSet (nearBox c H) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma mem_nearBox_of_cheb (hN : 1 ≤ N) {y z : V} {t : ℕ} (h : cheb N y z ≤ t) :
    y ∈ nearBox (center N z) (hR N t) := by
  intro a _
  have := abs_le.mp (center_close_of_cheb hN h a)
  simp only [Set.mem_Icc]; constructor <;> linarith

lemma μc_nearBox_le (c : V) {H : ℝ} (hH : 0 ≤ H) :
    μc (nearBox c H) ≤ ENNReal.ofReal ((2 * H) ^ 3) := by
  calc μc (nearBox c H) ≤ volume (nearBox c H) := Measure.restrict_apply_le _ _
    _ = ENNReal.ofReal ((2 * H) ^ 3) := by
        rw [nearBox, volume_pi_pi]
        have e : ∀ a, (c a + H) - (c a - H) = 2 * H := fun a => by ring
        simp only [Real.volume_Icc, Fin.prod_univ_three, e]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

lemma μc_secRegion {c : V} (hc : ∀ a, 0 < c a ∧ c a < 1) {h : ℝ} (hh : 0 < h)
    (h1 : h < 1) {m : Fin 3} {σ : Bool} (hf : faceIn c h m σ) :
    μc (secRegion c h m σ) = ENNReal.ofReal (h / 10 * (h / 20) * (h / 20)) := by
  rw [μc, Measure.restrict_apply (secRegion_measurable _ _ _ _),
    Set.inter_eq_left.mpr (secRegion_sub hc hh h1 hf), volume_secRegion _ hh]

lemma cellCenter_mem (hN : 1 ≤ N) (κ : Fin 3 → Fin (gridN N)) (a : Fin 3) :
    0 < cellCenter κ a ∧ cellCenter κ a < 1 := by
  have hdp := ds_pos hN
  have hd := ds_mul hN
  have hk : (((κ a : ℕ) : ℝ)) + 1 ≤ gridN N := by exact_mod_cast (κ a).isLt
  unfold cellCenter
  constructor
  · positivity
  · nlinarith

/-! ### Dominating one-coordinate factors -/

/-- Rate of the exponential moment. -/
noncomputable def lam : ℝ := 1 / 10 ^ 8

noncomputable def alpha : ℝ := Real.exp lam - 1

lemma lam_pos : 0 < lam := by unfold lam; positivity

lemma alpha_nonneg : 0 ≤ alpha := by
  unfold alpha; linarith [Real.add_one_le_exp lam, lam_pos]

lemma alpha_le : alpha ≤ 2 / 10 ^ 8 := by
  have h := Real.abs_exp_sub_one_le (x := lam) (by unfold lam; rw [abs_le]; constructor <;> norm_num)
  unfold alpha
  have := (abs_le.mp h).2
  rw [abs_of_pos lam_pos] at this
  unfold lam at this ⊢
  linarith

/-- `exp(λ · 1_B)`, the factor whose product dominates `(1 + count)^2`. -/
noncomputable def eFac (B : Set V) (y : V) : ENNReal :=
  ENNReal.ofReal (Real.exp (lam * B.indicator 1 y))

lemma eFac_eq (B : Set V) (y : V) :
    eFac B y = 1 + B.indicator (fun _ => ENNReal.ofReal alpha) y := by
  unfold eFac
  by_cases hy : y ∈ B
  · simp only [Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one alpha_nonneg]
    congr 1; unfold alpha; ring
  · simp [Set.indicator_of_notMem hy]

lemma eFac_measurable {B : Set V} (hB : MeasurableSet B) : Measurable (eFac B) := by
  unfold eFac
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (measurable_one.indicator hB)))

lemma lintegral_eFac {B : Set V} (hB : MeasurableSet B) :
    ∫⁻ y, eFac B y ∂μc = 1 + ENNReal.ofReal alpha * μc B := by
  simp_rw [eFac_eq]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ,
    one_mul, lintegral_indicator_const hB]

lemma lintegral_eFac_compl {B S : Set V} (hB : MeasurableSet B) (hS : MeasurableSet S) :
    ∫⁻ y, eFac B y * Sᶜ.indicator 1 y ∂μc ≤ (1 - μc S) + ENNReal.ofReal alpha * μc B := by
  have hle : ∀ y, eFac B y * Sᶜ.indicator 1 y ≤
      Sᶜ.indicator 1 y + B.indicator (fun _ => ENNReal.ofReal alpha) y := by
    intro y
    by_cases hy : y ∈ S
    · simp [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hy)]
    · rw [Set.indicator_of_mem (Set.mem_compl hy), Pi.one_apply, mul_one, eFac_eq]
  calc ∫⁻ y, eFac B y * Sᶜ.indicator 1 y ∂μc
      ≤ ∫⁻ y, (Sᶜ.indicator 1 y + B.indicator (fun _ => ENNReal.ofReal alpha) y) ∂μc :=
        lintegral_mono hle
    _ = μc Sᶜ + ENNReal.ofReal alpha * μc B := by
        rw [lintegral_add_left (measurable_one.indicator hS.compl),
          lintegral_indicator_one hS.compl, lintegral_indicator_const hB]
    _ = (1 - μc S) + ENNReal.ofReal alpha * μc B := by rw [prob_compl_eq_one_sub hS]

end Rng3d
