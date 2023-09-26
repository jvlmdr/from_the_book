-- Product of primes bounded above by power of four.

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith

import FromTheBook.Ch02.Bertrand.Util

open BigOperators

example (n : ℕ) : primes (Finset.range n) = {p : ℕ | p < n ∧ Nat.Prime p} := by
  simp [primes]

lemma chooseHalfLePowFour {m : ℕ} : Nat.choose (2*m+1) m ≤ 4^m :=
  calc Nat.choose (2*m+1) m
    _ = ∑ k in {m}, Nat.choose (2*m+1) k := Finset.sum_singleton
    _ = ∑ k in Finset.Ico m (m+1), Nat.choose (2*m+1) k := by rw [Nat.Ico_succ_singleton]
    _ ≤ ∑ k in Finset.Ico 0 (m+1), Nat.choose (2*m+1) k :=
      Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_left (Nat.zero_le m))
    _ = ∑ k in Finset.range (m+1), Nat.choose (2*m+1) k := by rw [Finset.range_eq_Ico]
    _ = 4^m := Nat.sum_range_choose_halfway _

lemma prodPrimesIocLeChoose {m : ℕ}
    : ∏ p in primes (Finset.Ioc (m+1) (2*m+1)), p ≤ Nat.choose (2*m+1) m := by
  -- Uses divisibility of `Nat.choose`.
  rw [primes]
  apply Nat.le_of_dvd
  . apply Nat.choose_pos; linarith
  apply Finset.prod_primes_dvd <;> simp [← Nat.prime_iff]
  intro p ha hb hp
  rw [two_mul, add_assoc]
  apply Nat.Prime.dvd_choose_add hp <;> linarith

lemma primesSuccEqPrimesSelf {n : ℕ} (hn : ¬Nat.Prime n.succ)
    : primes (Finset.range n.succ.succ) = primes (Finset.range n.succ) := by
  simp [primes]
  rw [Finset.range_succ]
  simp [Finset.filter_insert]
  assumption

theorem caseStrongRecOnOddPrimes {p : ℕ → Prop} (zero : p 0) (two : p 2)
    (not_prime : ∀ n, ¬Nat.Prime n.succ → (∀ x, x ≤ n → p x) → p n.succ)  -- Includes `p 1`.
    (odd_prime : ∀ n, Nat.Prime (2*n).succ → (∀ x, x ≤ 2*n → p x) → p (2*n).succ)
    : ∀ n, p n := by
  intro n
  induction n using Nat.caseStrongInductionOn with
  | zero => exact zero
  | ind k h_ind =>
    cases dec_em (Nat.Prime k.succ) with
    | inr hk_prime =>
      -- Not prime, positive.
      apply not_prime _ hk_prime
      exact h_ind
    | inl hk_prime =>
      -- Prime; split into 2 and odd primes.
      cases Nat.Prime.eq_two_or_odd' hk_prime with
      | inl hk_two => rw [hk_two]; exact two
      | inr hk_two =>
        cases hk_two with
        | intro m hm =>
          simp [Nat.add_one] at hm
          simp [hm] at *
          apply odd_prime _ hk_prime h_ind

-- We can use `Nat.prime n.succ` to obtain `prodPrimes n.succ ≤ 4^n`
-- from `prodPrimes n ≤ 4^n.pred`.
-- Therefore shift the inductive hypothesis to `prodPrimes n ≤ 4^n.pred`
-- rather than `prodPrimes n.succ ≤ 4^n`.

theorem prodPrimesLePowFour {n : ℕ} : prodPrimes n ≤ 4^n.pred := by
  induction n using caseStrongRecOnOddPrimes with
  | zero => simp
  | two => simp
  | not_prime n hp hi =>
    specialize hi n
    simp at hi
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.pred_succ] at *
      simp [prodPrimes]
      rw [primesSuccEqPrimesSelf hp, Nat.add_one]
      rw [← prodPrimes, Nat.add_one]
      apply le_trans hi
      simp [pow_succ]
  | odd_prime n hp hi =>
    simp
    conv => rhs; rw [two_mul, pow_add]
    specialize hi n.succ _
    . cases n with
      | zero => contradiction  -- No need to handle (2n+1) = 1; not prime.
      | succ n => linarith
    simp at hi
    rw [prodPrimesSplit (by linarith : n.succ ≤ (2*n).succ)]
    apply Nat.mul_le_mul hi
    apply le_trans _ chooseHalfLePowFour
    exact prodPrimesIocLeChoose

theorem prodPrimesRealLePowFour {x : ℝ} (hx : 1 ≤ x) : ↑(prodPrimes ⌊x⌋₊) ≤ 4^(x-1) :=
  calc (prodPrimes ⌊x⌋₊ : ℝ)
    _ ≤ ↑(4 ^ (⌊x⌋₊ - 1)) := by
      norm_cast
      apply prodPrimesLePowFour
    _ = 4 ^ ↑(⌊x⌋₊ - 1) := by norm_cast
    _ ≤ 4 ^ (x - 1) := by
      rw [Real.rpow_le_rpow_left_iff (by norm_num)]
      rw [← Nat.floor_sub_one]
      apply Nat.floor_le
      linarith
