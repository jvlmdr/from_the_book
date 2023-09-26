-- Proof of Bertrand's postulate (also exists in mathlib).

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.LocallyFinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import FromTheBook.Ch02.Bertrand.CentralBinom
import FromTheBook.Ch02.Bertrand.LandauTrick
import FromTheBook.Ch02.Bertrand.ProdPrimes
import FromTheBook.Ch02.Bertrand.Util

open BigOperators


lemma natRealCoeLtCoe (a b : ℕ) : (a : ℝ) < (b : ℝ) ↔ a < b := by simp

lemma natRealCoeLeCoe (a b : ℕ) : (a : ℝ) ≤ (b : ℝ) ↔ a ≤ b := by simp

lemma rpowDivThreeLe {n : ℕ} (hn : 0 < n) (h : 4^n ≤ (2*n) ^ (1 + Nat.sqrt (2*n)) * 4^(2*n/3).pred)
    : 4^(↑n/3) ≤ (2*↑n) ^ (1 + Real.sqrt (2*n)) := by
  rw [← natRealCoeLeCoe] at h
  have : 4^(↑n/3 : ℝ) = 4^(↑n : ℝ) / 4^(2*↑n/3 : ℝ)
  . rw [eq_div_iff]
    swap; {apply ne_of_gt; apply Real.rpow_pos_of_pos (by norm_num)}
    rw [← Real.rpow_add (by norm_num)]
    simp [Real.rpow_def_of_pos]  -- Real.rpow_eq_rpow? strict mono?
    norm_num
    push_cast
    simp [div_add_div_same]
    norm_cast
    rw [(by linarith : n + 2*n = n*3)]
    simp
  rw [this]; clear this
  rw [div_le_iff]
  swap; {apply Real.rpow_pos_of_pos; norm_num}
  rw [Real.rpow_nat_cast]
  norm_cast
  apply le_trans h; clear h
  push_cast
  apply mul_le_mul
  . rw [← Real.rpow_nat_cast]
    rw [Real.rpow_le_rpow_left_iff (by norm_cast; linarith)]
    simp [-Real.sqrt_mul']
    norm_cast
    apply Real.nat_sqrt_le_real_sqrt
  . rw [← Real.rpow_nat_cast]
    rw [Real.rpow_le_rpow_left_iff (by norm_cast)]
    rw [le_div_iff (by norm_num)]
    norm_cast
    apply Nat.le_trans (Nat.mul_le_mul_right 3 (Nat.pred_le _))
    apply Nat.div_mul_le_self
  . apply pow_nonneg (by norm_num)
  . apply Real.rpow_nonneg_of_nonneg (by norm_cast; linarith)

lemma succLtTwoPow {a : ℕ} (h2 : 2 ≤ a) : a.succ < 2^a := by
  replace h2 := Nat.exists_eq_add_of_le h2
  cases h2 with | intro u hu =>
  rw [hu]
  clear a hu
  induction u with
  | zero => simp
  | succ u h =>
    rw [Nat.add_succ, Nat.pow_succ, Nat.mul_two]
    rw [← Nat.add_one]
    apply Nat.add_lt_add h
    apply Nat.one_lt_pow <;> linarith

lemma twoMulLtTwoPow {n : ℝ} (hn : 32 ≤ n) : 2*n < 2 ^ (6 * (2*n)^6⁻¹) :=
  calc 2*n
    _ = (2*n) ^ (6⁻¹ * 6) := by simp
    _ = ((2*n) ^ 6⁻¹) ^ 6 := by apply Real.rpow_mul (by linarith)
    _ < (↑⌊(2*n) ^ 6⁻¹⌋₊ + 1) ^ 6 := by
      apply Real.rpow_lt_rpow _ _ (by norm_num)
      . apply Real.rpow_nonneg_of_nonneg; linarith
      . apply Nat.lt_floor_add_one
    _ < 2 ^ (6 * ↑⌊(2*n)^6⁻¹⌋₊) := by
      norm_cast  -- ℕ on both sides.
      conv => rhs; rhs; rw [mul_comm]
      rw [Nat.pow_mul]
      apply Nat.pow_lt_pow_of_lt_left _ (by norm_num)
      apply succLtTwoPow
      have h0 : 0 ≤ (2 * n) ^ 6⁻¹
      . apply le_of_lt; apply Real.rpow_pos_of_pos; linarith
      rw [Nat.le_floor_iff h0]
      norm_cast
      rw [← Real.rpow_le_rpow_iff (by norm_num) h0 (by norm_num : (0:ℝ) < 6)]
      rw [← Real.rpow_mul (by linarith)]
      simp
      rw [mul_comm]
      rw [← div_le_iff (by norm_num)]
      norm_cast
      norm_num
      assumption
    _ ≤ 2 ^ (6 * (2*n)^6⁻¹) := by
      rw [Real.rpow_le_rpow_left_iff (by norm_num)]
      rw [mul_le_mul_left (by norm_num)]
      have h0 : 0 ≤ (2 * n) ^ 6⁻¹
      . apply le_of_lt; apply Real.rpow_pos_of_pos; linarith
      exact Nat.floor_le h0

lemma ltTwoMulSqrtTwoMul {n : ℝ} (h : 81/2 < n) : 18 < 2 * Real.sqrt (2*n) := by
  rw [← div_lt_iff' (by norm_num)]
  rw [Real.lt_sqrt (by norm_num)]
  norm_num
  rw [← div_lt_iff' (by norm_num)]
  linarith

lemma fourPowLtOf {n : ℝ} (hn : 81/2 < n) (h : 4^(n/3) ≤ (2*n)^(1 + Real.sqrt (2*n)))
    : 4^n < 2^(20 * (2*n)^(2/3)) :=
  calc
  _ ≤ (4^(n/3))^3 := by rw [← Real.rpow_mul (by norm_num)]; simp
  _ ≤ ((2*n)^((1 + Real.sqrt (2*n))))^3 := by
    apply Real.rpow_le_rpow _ h (by linarith)
    apply Real.rpow_nonneg_of_nonneg (by norm_num)
  _ = (2*n)^((1 + Real.sqrt (2*n)) * 3) := by rw [Real.rpow_mul (by linarith)]
  _ < (2 ^ (6 * (2*n)^6⁻¹)) ^ ((1 + Real.sqrt (2*n)) * 3) := by
    apply Real.rpow_lt_rpow (by linarith) (twoMulLtTwoPow (by linarith))
    simp
    exact lt_add_of_pos_of_le (by norm_num) (Real.sqrt_nonneg _)
  _ < _ := by
    rw [← Real.rpow_mul (by linarith)]
    rw [Real.rpow_lt_rpow_left_iff (by linarith)]
    calc
    _ = (18 * (1 + Real.sqrt (2*n))) * ((2*n)^6⁻¹) := by linarith
    _ < (2 + 18) * Real.sqrt (2*n) * (2*n)^6⁻¹ := by
      rw [mul_lt_mul_right]
      . simp [mul_add, add_mul]
        apply ltTwoMulSqrtTwoMul
        linarith
      . apply Real.rpow_pos_of_pos
        linarith
    _ = 20 * (Real.sqrt (2*n) * (2*n)^6⁻¹) := by linarith
    _ = _ := by
      simp [Real.sqrt_eq_rpow]
      rw [← Real.rpow_add (by linarith)]
      norm_num

lemma lt4kIff {n : ℝ} (hn : 0 < n) : 4^n < 2^(20 * (2*n)^(2/3)) ↔ n < 4000 := by
  rw [(by norm_num : (4 : ℝ) = 2 ^ 2)]
  rw [← Real.rpow_mul (by norm_num)]
  rw [Real.rpow_lt_rpow_left_iff (by linarith)]
  -- TODO: Use NNReal instead?
  have h_nonneg : 0 < (2 * n) ^ (2 / 3) := by apply Real.rpow_pos_of_pos; linarith
  rw [← @Real.rpow_lt_rpow_iff _ _ 3 (by linarith) (by linarith) (by norm_num)]
  rw [@Real.mul_rpow 20 _ _ (by norm_num) (by linarith)]
  rw [← Real.rpow_mul (by linarith)]
  simp
  rw [(by norm_num : (3:ℝ) = 1 + 2)]
  rw [@Real.rpow_add (2*n) (by linarith)]
  rw [@Real.rpow_add 20 (by norm_num)]
  norm_num
  rw [mul_lt_mul_right (by apply sq_pos_of_pos; linarith)]
  rw [mul_comm]
  rw [← lt_div_iff (by norm_num)]
  norm_num

lemma bertrand (n : ℕ) : 0 < n → ∃ p, p ∈ Set.Ioc n (2*n) ∧ Nat.Prime p := by
  intro hn
  cases lt_or_le n 4000 with
  | inl hn' => exact landauTrick (by linarith) (by linarith)
  | inr hn' =>
    by_contra h
    simp at h
    replace h : ∏ p in primes (Finset.Ioc n (2*n)), p = 1
    . apply Finset.prod_eq_one
      intro i hi
      specialize h i
      simp [primes] at *
      specialize h hi.left.left hi.left.right hi.right
      contradiction
    have h' := fourPowLeMulProdPrimes (by linarith : 2 < n)
    simp [h] at h'; clear h
    replace h' := rpowDivThreeLe (by linarith : 0 < n) h'
    have : (81 / 2 : ℝ) < ↑n
    . rw [div_lt_iff (by norm_num)]; norm_cast; linarith
    replace h' := fourPowLtOf this h'; clear this
    rw [lt4kIff (by norm_cast)] at h'
    norm_cast at h'
    linarith
