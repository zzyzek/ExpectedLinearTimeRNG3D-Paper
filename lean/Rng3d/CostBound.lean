/-
Deterministic bound on the per-anchor operation count in terms of the
final fence radius `R*` and the number of points within cell distance
`2R* + 3` of the anchor.
-/
import Rng3d.Region

open Finset

namespace Rng3d

variable {N : ℕ}

lemma Q_mono {x : Fin N → V} {i : Fin N} {r r' : ℕ} (h : r ≤ r') : Q x i r ⊆ Q x i r' := by
  intro j hj
  rw [mem_Q] at hj ⊢
  exact ⟨hj.1, hj.2.trans h⟩

lemma maxd_le (hN : 1 ≤ N) (x : Fin N → V) (i : Fin N) :
    maxd x i ≤ 2 * ((Rstar x i : ℝ) + 1) * ds N := by
  have hdp := ds_pos hN
  set b := 2 * ((Rstar x i : ℝ) + 1) * ds N
  have hb : 0 ≤ b := by positivity
  have hed : ∀ j ∈ cand x i, ed (x i) (x j) ≤ b := by
    intro j hj
    unfold cand at hj
    rw [mem_Q] at hj
    have hc := fun m => close_of_cheb hN hj.2 m
    have hsq : dd (x i) (x j) ≤ b ^ 2 := by
      rw [dd_eq, Fin.sum_univ_three]
      have h0 := abs_lt.mp (hc 0)
      have h1 := abs_lt.mp (hc 1)
      have h2 := abs_lt.mp (hc 2)
      have e : ∀ m, (x i m - x j m) ^ 2 ≤ (((Rstar x i : ℝ) + 1) * ds N) ^ 2 := by
        intro m
        have := abs_lt.mp (hc m)
        rw [← sq_abs, abs_sub_comm]
        have ha : |x j m - x i m| ≤ ((Rstar x i : ℝ) + 1) * ds N := (hc m).le
        exact pow_le_pow_left₀ (abs_nonneg _) ha 2
      have := e 0; have := e 1; have := e 2
      simp only [b]
      nlinarith
    unfold ed
    calc Real.sqrt (dd (x i) (x j)) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hsq
      _ = b := Real.sqrt_sq hb
  unfold maxd
  have : ((cand x i).sup fun j => (ed (x i) (x j)).toNNReal) ≤ b.toNNReal :=
    Finset.sup_le fun j hj => Real.toNNReal_le_toNNReal (hed j hj)
  calc (((cand x i).sup fun j => (ed (x i) (x j)).toNNReal : NNReal) : ℝ)
      ≤ (b.toNNReal : ℝ) := by exact_mod_cast this
    _ = b := Real.coe_toNNReal b hb

lemma Tx_le (hN : 1 ≤ N) (x : Fin N → V) (i : Fin N) : Tx x i ≤ 2 * Rstar x i + 3 := by
  unfold Tx
  refine max_le (by omega) ?_
  unfold Mx
  rw [Nat.ceil_le]
  have hdp := ds_pos hN
  have := maxd_le hN x i
  have : maxd x i / ds N ≤ 2 * ((Rstar x i : ℝ) + 1) := by
    rw [div_le_iff₀ hdp]; linarith
  push_cast
  linarith

/-- Number of other points within cell distance `t` of the anchor. -/
noncomputable def nearCount (x : Fin N → V) (i : Fin N) (t : ℕ) : ℕ := (Q x i t).card

theorem cost_le (hN : 1 ≤ N) (x : Fin N → V) (i : Fin N) :
    cost x i ≤ 1000 * (Rstar x i + 2) ^ 4 * (nearCount x i (2 * Rstar x i + 3) + 1) ^ 2 := by
  set R := Rstar x i
  set T := Tx x i
  set X := nearCount x i (2 * R + 3)
  have hT : T ≤ 2 * R + 3 := Tx_le hN x i
  have hRT : R ≤ T := le_max_left _ _
  have hQ : ∀ r ≤ T, (Q x i r).card ≤ X := fun r hr =>
    card_le_card (Q_mono (hr.trans hT))
  have hcube : ∀ r ≤ T, (2 * r + 1) ^ 3 ≤ (4 * (R + 2)) ^ 3 := fun r hr =>
    Nat.pow_le_pow_left (by omega) 3
  have s1 : (∑ r ∈ range (R + 1), ((2 * r + 1) ^ 3 + 100 * ((Q x i r).card + 1))) ≤
      (R + 1) * ((4 * (R + 2)) ^ 3 + 100 * (X + 1)) := by
    have := Finset.sum_le_card_nsmul (range (R + 1))
      (fun r => (2 * r + 1) ^ 3 + 100 * ((Q x i r).card + 1))
      ((4 * (R + 2)) ^ 3 + 100 * (X + 1)) (fun r hr => by
        rw [mem_range] at hr
        have h1 := hcube r (by omega)
        have h2 := hQ r (by omega)
        omega)
    simpa using this
  have s2 : (∑ r ∈ Ioc R T, ((2 * r + 1) ^ 3 + (Q x i r).card)) ≤
      (T - R) * ((4 * (R + 2)) ^ 3 + 100 * (X + 1)) := by
    have := Finset.sum_le_card_nsmul (Ioc R T)
      (fun r => (2 * r + 1) ^ 3 + (Q x i r).card)
      ((4 * (R + 2)) ^ 3 + 100 * (X + 1)) (fun r hr => by
        rw [mem_Ioc] at hr
        have h1 := hcube r hr.2
        have h2 := hQ r hr.2
        omega)
    simpa using this
  have s3 : (cand x i).card * ((blk x i).card + 1) ≤ (X + 1) * (X + 1) := by
    have hc : (cand x i).card ≤ X := hQ R hRT
    have hb : (blk x i).card ≤ X := hQ T le_rfl
    exact Nat.mul_le_mul (by omega) (by omega)
  have hsum : cost x i ≤ (R + 1) * ((4 * (R + 2)) ^ 3 + 100 * (X + 1)) +
      (T - R) * ((4 * (R + 2)) ^ 3 + 100 * (X + 1)) + (X + 1) * (X + 1) := by
    have hdef : cost x i = (∑ r ∈ range (R + 1), ((2 * r + 1) ^ 3 + 100 * ((Q x i r).card + 1))) +
        (∑ r ∈ Ioc R T, ((2 * r + 1) ^ 3 + (Q x i r).card)) +
        (cand x i).card * ((blk x i).card + 1) := rfl
    rw [hdef]
    omega
  have hw : (R + 1) + (T - R) ≤ 2 * (R + 2) := by omega
  have hA : 1 ≤ R + 2 := by omega
  have hB : 1 ≤ X + 1 := by omega
  set A := R + 2
  set B := X + 1
  have e1 : (R + 1) * ((4 * A) ^ 3 + 100 * B) + (T - R) * ((4 * A) ^ 3 + 100 * B) ≤
      2 * A * ((4 * A) ^ 3 + 100 * B) := by
    rw [← add_mul]; exact Nat.mul_le_mul_right _ hw
  have hA4 : A ≤ A ^ 4 := by
    calc A = A ^ 1 := (pow_one A).symm
      _ ≤ A ^ 4 := Nat.pow_le_pow_right hA (by norm_num)
  have hB2 : B ≤ B ^ 2 := by nlinarith
  have hA4' : 1 ≤ A ^ 4 := Nat.one_le_pow _ _ hA
  have : 2 * A * ((4 * A) ^ 3 + 100 * B) + B * B ≤ 1000 * A ^ 4 * B ^ 2 := by
    have : 2 * A * ((4 * A) ^ 3 + 100 * B) + B * B = 128 * A ^ 4 + 200 * (A * B) + B ^ 2 := by
      ring
    rw [this]
    have t1 : A ^ 4 ≤ A ^ 4 * B ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    have t2 : A * B ≤ A ^ 4 * B ^ 2 := Nat.mul_le_mul hA4 hB2
    have t3 : B ^ 2 ≤ A ^ 4 * B ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  omega

end Rng3d
