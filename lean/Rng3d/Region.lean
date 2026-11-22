/-
Securing regions.  For a fence of radius `ρ ≥ 16` and a face that is not
outside the unit cube, an explicit box of volume `h^3/4000`
(`h` the fence half-width) inside the unit cube has the property that
any point in it secures all four patches of that face.  So if the fence
is not secured at radius `ρ`, some face has no other point in its box.
-/
import Rng3d.Correct

open Finset

namespace Rng3d

variable {N : ℕ}

/-- Interval for the face axis: between `9h/20` and `11h/20` beyond the
cell centre, on the side of the face. -/
def faceI (c0 h : ℝ) (σ : Bool) : Set ℝ :=
  if σ then Set.Ico (c0 + 9 / 20 * h) (c0 + 11 / 20 * h)
  else Set.Ioc (c0 - 11 / 20 * h) (c0 - 9 / 20 * h)

/-- Interval for a side axis: width `h/20` next to the cell centre, on a
side that stays inside `[0,1)`. -/
def sideI (c0 h : ℝ) : Set ℝ :=
  if c0 + h / 20 ≤ 1 then Set.Ico c0 (c0 + h / 20) else Set.Ico (c0 - h / 20) c0

def secRegion (c : V) (h : ℝ) (m : Fin 3) (σ : Bool) : Set V :=
  Set.univ.pi fun a => if a = m then faceI (c a) h σ else sideI (c a) h

/-- The face plane of axis `m`, side `σ`, is inside `[0,1)`. -/
def faceIn (c : V) (h : ℝ) (m : Fin 3) (σ : Bool) : Prop :=
  0 ≤ c m + sgn σ * h ∧ c m + sgn σ * h < 1

lemma faceI_bound {c0 h y : ℝ} {σ : Bool} (hy : y ∈ faceI c0 h σ) :
    9 / 20 * h ≤ sgn σ * (y - c0) ∧ sgn σ * (y - c0) ≤ 11 / 20 * h := by
  unfold faceI at hy
  unfold sgn
  cases σ
  · simp only [Bool.false_eq_true, ite_false, Set.mem_Ioc] at hy ⊢
    constructor <;> linarith [hy.1, hy.2]
  · simp only [ite_true, Set.mem_Ico] at hy ⊢
    constructor <;> linarith [hy.1, hy.2]

lemma sideI_bound {c0 h y : ℝ} (hh : 0 < h) (hy : y ∈ sideI c0 h) :
    |y - c0| ≤ h / 20 := by
  unfold sideI at hy
  split_ifs at hy with hc
  · obtain ⟨h1, h2⟩ := hy; rw [abs_le]; constructor <;> linarith
  · obtain ⟨h1, h2⟩ := hy; rw [abs_le]; constructor <;> linarith

/-- The arithmetic core of the securing argument, in coordinates where
the face axis comes first.  `w` is the candidate point and `δ` the
anchor, both relative to the cell centre; `u` is a corner direction. -/
lemma key_ineq {h s w0 w1 w2 δ0 δ1 δ2 u1 u2 : ℝ} (hh : 0 < h) (hs : s * s = 1)
    (hw0 : 9 / 20 * h ≤ s * w0 ∧ s * w0 ≤ 11 / 20 * h)
    (hw1 : |w1| ≤ h / 20) (hw2 : |w2| ≤ h / 20)
    (hδ0 : |δ0| ≤ h / 33) (hδ1 : |δ1| ≤ h / 33) (hδ2 : |δ2| ≤ h / 33)
    (hu1 : |u1| ≤ 1) (hu2 : |u2| ≤ 1) :
    0 < (w0 - δ0) * (h * s - w0) + (w1 - δ1) * (h * u1 - w1) +
        (w2 - δ2) * (h * u2 - w2) ∧
    0 < (w0 - δ0) * (h * s) + (w1 - δ1) * (h * u1) + (w2 - δ2) * (h * u2) := by
  have habs : |s| = 1 := by
    have : |s| * |s| = 1 := by rw [← abs_mul, hs, abs_one]
    nlinarith [abs_nonneg s]
  have hsd : |s * δ0| ≤ h / 33 := by rw [abs_mul, habs, one_mul]; exact hδ0
  have hsd' := abs_le.mp hsd
  have e0 : (w0 - δ0) * (h * s - w0) = (s * w0 - s * δ0) * (h - s * w0) := by
    linear_combination ((w0 - δ0) * w0) * hs
  have e0' : (w0 - δ0) * (h * s) = h * (s * w0 - s * δ0) := by ring
  -- Side terms are bounded below by minus the product of absolute bounds.
  --
  have side : ∀ {w δ u : ℝ}, |w| ≤ h / 20 → |δ| ≤ h / 33 → |u| ≤ 1 →
      -((h / 20 + h / 33) * (h + h / 20)) ≤ (w - δ) * (h * u - w) ∧
      -((h / 20 + h / 33) * h) ≤ (w - δ) * (h * u) := by
    intro w δ u hw hδ hu
    have a1 : |w - δ| ≤ h / 20 + h / 33 := (abs_sub _ _).trans (add_le_add hw hδ)
    have a2 : |h * u - w| ≤ h + h / 20 := by
      refine (abs_sub _ _).trans (add_le_add ?_ hw)
      rw [abs_mul, abs_of_pos hh]; nlinarith
    have a3 : |h * u| ≤ h := by rw [abs_mul, abs_of_pos hh]; nlinarith
    constructor
    · have := neg_abs_le ((w - δ) * (h * u - w))
      rw [abs_mul] at this
      have := mul_le_mul a1 a2 (abs_nonneg _) (by positivity)
      linarith
    · have := neg_abs_le ((w - δ) * (h * u))
      rw [abs_mul] at this
      have := mul_le_mul a1 a3 (abs_nonneg _) (by positivity)
      linarith
  obtain ⟨s1, t1⟩ := side hw1 hδ1 hu1
  obtain ⟨s2, t2⟩ := side hw2 hδ2 hu2
  have f1 : 0 ≤ s * w0 - s * δ0 - (9 / 20 * h - h / 33) := by linarith
  have f2 : 0 ≤ h - s * w0 - 9 / 20 * h := by linarith
  have fp : (9 / 20 * h - h / 33) * (9 / 20 * h) ≤ (s * w0 - s * δ0) * (h - s * w0) := by
    apply mul_le_mul <;> nlinarith
  constructor
  · rw [e0]; nlinarith
  · rw [e0']; nlinarith

lemma abs_cornerDir_le (P : Patch) (κ : Fin 3 → Bool) (a : Fin 3) :
    |cornerDir P κ a| ≤ 1 := by
  unfold cornerDir
  split_ifs <;> simp [abs_sgn]

lemma cornerDir_face (P : Patch) (κ : Fin 3 → Bool) : cornerDir P κ P.1 = sgn (P.2 P.1) := by
  simp [cornerDir]

/-- Any point of the securing region of a face secures every patch of
that face, for fence radius `ρ ≥ 16`. -/
lemma secRegion_secures (hN : 1 ≤ N) {p y : V} {ρ : ℕ} (hρ : 16 ≤ ρ) (P : Patch)
    (hy : y ∈ secRegion (center N p) (hR N ρ) P.1 (P.2 P.1)) (κ : Fin 3 → Bool) :
    0 < (y - p) ⬝ᵥ (center N p + hR N ρ • cornerDir P κ - y) ∧
    0 < (y - p) ⬝ᵥ (hR N ρ • cornerDir P κ) := by
  set c := center N p
  set h := hR N ρ
  have hh : 0 < h := hR_pos hN ρ
  have hdp := ds_pos hN
  have hδ : ∀ a, |p a - c a| ≤ h / 33 := by
    intro a
    refine (abs_center_sub hN p a).trans ?_
    have : (16 : ℝ) ≤ ρ := by exact_mod_cast hρ
    simp only [h, hR]
    nlinarith
  have hs := sgn_sq (P.2 P.1)
  have hya : ∀ a, y a ∈ (if a = P.1 then faceI (c a) h (P.2 P.1) else sideI (c a) h) :=
    fun a => hy a (Set.mem_univ a)
  have hface : 9 / 20 * h ≤ sgn (P.2 P.1) * (y P.1 - c P.1) ∧
      sgn (P.2 P.1) * (y P.1 - c P.1) ≤ 11 / 20 * h := by
    have := hya P.1; simp only [ite_true] at this; exact faceI_bound this
  have hside : ∀ a, a ≠ P.1 → |y a - c a| ≤ h / 20 := by
    intro a ha
    have := hya a; simp only [ha, ite_false] at this; exact sideI_bound hh this
  have hu := abs_cornerDir_le P κ
  have huf := cornerDir_face P κ
  -- Rewrite both dot products in coordinates relative to the cell centre.
  --
  have e1 : (y - p) ⬝ᵥ (c + h • cornerDir P κ - y) =
      ∑ a, ((y a - c a) - (p a - c a)) * (h * cornerDir P κ a - (y a - c a)) := by
    simp only [dotProduct, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => ?_; ring
  have e2 : (y - p) ⬝ᵥ (h • cornerDir P κ) =
      ∑ a, ((y a - c a) - (p a - c a)) * (h * cornerDir P κ a) := by
    simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => ?_; ring
  rw [e1, e2, Fin.sum_univ_three, Fin.sum_univ_three]
  obtain ⟨ax, sv⟩ := P
  generalize cornerDir (ax, sv) κ = u at hu huf ⊢
  simp only at hface hside huf hs
  fin_cases ax
  · simp only [Fin.zero_eta] at hface hside huf hs
    rw [huf]
    exact key_ineq hh hs hface (hside 1 (by decide)) (hside 2 (by decide)) (hδ 0) (hδ 1)
      (hδ 2) (hu 1) (hu 2)
  · simp only [Fin.mk_one] at hface hside huf hs
    rw [huf]
    have := key_ineq hh hs hface (hside 0 (by decide)) (hside 2 (by decide)) (hδ 1) (hδ 0)
      (hδ 2) (hu 0) (hu 2)
    constructor <;> linarith [this.1, this.2]
  · simp only [Fin.reduceFinMk] at hface hside huf hs
    rw [huf]
    have := key_ineq hh hs hface (hside 0 (by decide)) (hside 1 (by decide)) (hδ 2) (hδ 0)
      (hδ 1) (hu 0) (hu 1)
    constructor <;> linarith [this.1, this.2]

lemma secRegion_close (hN : 1 ≤ N) {p y : V} {ρ : ℕ} {m : Fin 3} {σ : Bool}
    (hy : y ∈ secRegion (center N p) (hR N ρ) m σ) (a : Fin 3) :
    |y a - center N p a| < hR N ρ := by
  have hh := hR_pos hN ρ
  have hya := hy a (Set.mem_univ a)
  simp only at hya
  split_ifs at hya with ha
  · have := faceI_bound hya
    have habs : |sgn σ| = 1 := abs_sgn σ
    have : |y a - center N p a| = |sgn σ * (y a - center N p a)| := by
      rw [abs_mul, habs, one_mul]
    rw [this, abs_lt]; constructor <;> linarith
  · have := sideI_bound hh hya; linarith

/-- A point within half-width `hR r` of the anchor's cell centre in every
coordinate is within cell distance `r`. -/
lemma cheb_le_of_center_close (hN : 1 ≤ N) {y z : V} {r : ℕ}
    (h : ∀ a, |y a - center N z a| < hR N r) : cheb N y z ≤ r := by
  rw [cheb_le_iff]
  intro a
  have hdp := ds_pos hN
  obtain ⟨y1, y2⟩ := cell_bounds hN y a
  have ha := abs_lt.mp (h a)
  unfold center hR at ha
  have u : ((cellOf N y a : ℝ) - cellOf N z a) < (r : ℝ) + 1 := by
    by_contra hc; push Not at hc; nlinarith
  have l : -((r : ℝ) + 1) < ((cellOf N y a : ℝ) - cellOf N z a) := by
    by_contra hc; push Not at hc; nlinarith
  have u' : cellOf N y a - cellOf N z a < (r : ℤ) + 1 := by exact_mod_cast u
  have l' : -((r : ℤ) + 1) < cellOf N y a - cellOf N z a := by exact_mod_cast l
  omega

/-- Cell distance `≤ t` places a point in the closed box of half-width
`hR t` around the anchor's cell centre. -/
lemma center_close_of_cheb (hN : 1 ≤ N) {y z : V} {t : ℕ} (h : cheb N y z ≤ t)
    (a : Fin 3) : |y a - center N z a| ≤ hR N t := by
  rw [cheb_le_iff] at h
  have hm := h a
  have hdp := ds_pos hN
  obtain ⟨y1, y2⟩ := cell_bounds hN y a
  have hab : |((cellOf N y a : ℝ) - cellOf N z a)| ≤ t := by
    have : ((cellOf N y a - cellOf N z a).natAbs : ℝ) ≤ t := by exact_mod_cast hm
    rw [Nat.cast_natAbs, Int.cast_abs] at this; push_cast at this; exact this
  rw [abs_le] at hab
  unfold center hR
  rw [abs_le]; constructor <;> nlinarith

/-- If the fence is not secured at radius `ρ ≥ 16`, some face inside the
unit cube has no other point in its securing region. -/
lemma unsecured_face (hN : 1 ≤ N) {x : Fin N → V} {i : Fin N} {ρ : ℕ} (hρ : 16 ≤ ρ)
    (hns : ¬ allSecured x i ρ) :
    ∃ m σ, faceIn (center N (x i)) (hR N ρ) m σ ∧
      ∀ j, j ≠ i → x j ∉ secRegion (center N (x i)) (hR N ρ) m σ := by
  unfold allSecured at hns
  push Not at hns
  obtain ⟨P, hP⟩ := hns
  refine ⟨P.1, P.2 P.1, ?_, ?_⟩
  · by_contra hout
    apply hP
    refine ⟨ρ, le_rfl, Or.inl fun κ hc => hout ?_⟩
    have := hc P.1
    simp only [corner, Pi.add_apply, Pi.smul_apply, smul_eq_mul, cornerDir_face] at this
    unfold faceIn
    rw [mul_comm] at this
    exact this
  · intro j hji hj
    apply hP
    refine ⟨ρ, le_rfl, Or.inr ⟨j, ?_, fun κ => secRegion_secures hN hρ P hj κ⟩⟩
    rw [mem_Q]
    exact ⟨hji, cheb_le_of_center_close hN (secRegion_close hN hj)⟩

/-- The securing region lies in the unit cube when its face does and the
fence half-width is below 1. -/
lemma secRegion_sub {c : V} (hc : ∀ a, 0 < c a ∧ c a < 1) {h : ℝ} (hh : 0 < h)
    (h1 : h < 1) {m : Fin 3} {σ : Bool} (hf : faceIn c h m σ) :
    secRegion c h m σ ⊆ unitCube := by
  intro y hy a
  have hca := hc a
  have hya := hy a (Set.mem_univ a)
  simp only at hya
  split_ifs at hya with ha
  · subst ha
    unfold faceIn sgn at hf
    unfold faceI at hya
    cases σ
    · simp only [Bool.false_eq_true, ite_false, Set.mem_Ioc] at hf hya
      constructor <;> linarith [hya.1, hya.2]
    · simp only [ite_true, Set.mem_Ico] at hf hya
      constructor <;> linarith [hya.1, hya.2]
  · unfold sideI at hya
    split_ifs at hya with hc
    · obtain ⟨y1, y2⟩ := hya; constructor <;> linarith
    · obtain ⟨y1, y2⟩ := hya; constructor <;> linarith

lemma faceI_measurable (c0 h : ℝ) (σ : Bool) : MeasurableSet (faceI c0 h σ) := by
  unfold faceI; split_ifs <;> measurability

lemma sideI_measurable (c0 h : ℝ) : MeasurableSet (sideI c0 h) := by
  unfold sideI; split_ifs <;> measurability

lemma secRegion_measurable (c : V) (h : ℝ) (m : Fin 3) (σ : Bool) :
    MeasurableSet (secRegion c h m σ) := by
  unfold secRegion
  refine MeasurableSet.univ_pi fun a => ?_
  split_ifs
  · exact faceI_measurable _ _ _
  · exact sideI_measurable _ _

open MeasureTheory in
lemma volume_secRegion (c : V) {h : ℝ} (hh : 0 < h) (m : Fin 3) (σ : Bool) :
    volume (secRegion c h m σ) = ENNReal.ofReal (h / 10 * (h / 20) * (h / 20)) := by
  have hf : ∀ a, volume (faceI (c a) h σ) = ENNReal.ofReal (h / 10) := by
    intro a; unfold faceI; split_ifs
    · rw [Real.volume_Ico]; congr 1; ring
    · rw [Real.volume_Ioc]; congr 1; ring
  have hs : ∀ a, volume (sideI (c a) h) = ENNReal.ofReal (h / 20) := by
    intro a; unfold sideI; split_ifs
    · rw [Real.volume_Ico]; congr 1; ring
    · rw [Real.volume_Ico]; congr 1; ring
  have hv : ∀ a, volume (if a = m then faceI (c a) h σ else sideI (c a) h) =
      if a = m then ENNReal.ofReal (h / 10) else ENNReal.ofReal (h / 20) := by
    intro a; split_ifs
    · exact hf a
    · exact hs a
  unfold secRegion
  rw [volume_pi_pi]
  simp_rw [hv]
  rw [Fin.prod_univ_three, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]
  fin_cases m <;> simp <;> ring

end Rng3d
