-- Uses several results in mathlib.

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import FromTheBook.Ch02.Bertrand.ProdPrimes  -- prodPrimesLePowFour
import FromTheBook.Ch02.Bertrand.Util

open BigOperators


-- Probably exists in some form in mathlib?
lemma powNeOneIff' {x i : ℕ} : x^i ≠ 1 ↔ i ≠ 0 ∧ x ≠ 1 := by
  cases i with
  | zero => simp
  | succ i =>
    simp [not_iff_not]
    simp [pow_succ]  -- Can't combine these simps?
    intro hx
    simp [hx]

-- Only primes can have non-zero multiplicity in factorization.
-- Might be better to use (Nat.factorization n).support somehow?
lemma primeOfPowFactorizationNeOne {n p : ℕ} : p ^ (Nat.factorization n x) ≠ 1 → Nat.Prime x := by
  intro hx
  rw [powNeOneIff'] at hx
  by_contra hp  -- Nat.decidablePrime
  cases hx with | intro h hx =>
  apply h
  simp
  exact Nat.factorization_eq_zero_of_non_prime _ hp


namespace FactorizationCentralBinom

-- Multiplicity of primes sqrt(2n) < p ≤ 2n is at most one.
lemma leOne {n p : ℕ} (hp : p.Prime)
    : 2*n < p^2 → Nat.factorization (Nat.centralBinom n) p ≤ 1 := by
  intro hnp
  apply le_trans (Nat.factorization_choose_le_log)
  have hnp := Nat.le_pred_of_lt hnp
  apply le_trans (Nat.log_mono_right hnp)
  rw [← Nat.lt_succ_iff]
  have hp := Nat.Prime.one_lt hp
  apply Nat.log_lt_of_lt_pow
  . simp [hp]
  . apply Nat.pred_lt
    simp [hp]
    linarith

-- Requires 0 < n to handle product over empty set.
lemma prodIcoPowLePow {n : ℕ} {s : Finset ℕ} (hn : 0 < n)
    : ∏ p in s, p^(Nat.factorization (Nat.centralBinom n) p) ≤ (2*n)^(Finset.card s) := by
  apply Finset.prod_le_pow_card
  intro x _
  apply Nat.pow_factorization_choose_le
  linarith

-- Supports n = 0 by requiring empty set in this case.
lemma prodIcoPowLePow' {n : ℕ} {s : Finset ℕ} (hs : n = 0 → s = ∅)
    : ∏ p in s, p^(Nat.factorization (Nat.centralBinom n) p) ≤ (2*n)^(Finset.card s) := by
  apply Finset.prod_le_pow_card
  intro x hx
  cases n with
  | zero => simp at hs; rw [hs] at hx; contradiction
  | succ n => apply Nat.pow_factorization_choose_le; simp

-- Can eliminate terms 0 and 1 from product.
lemma prodRangePowEqProdIcoPowOfLeTwo {n a b : ℕ} (ha : a ≤ 2)
    : ∏ p in Finset.range b, p^(Nat.factorization (Nat.centralBinom n) p) =
      ∏ p in Finset.Ico a b, p^(Nat.factorization (Nat.centralBinom n) p) := by
  rw [Finset.range_eq_Ico]
  rw [← Finset.prod_subset (Finset.Ico_subset_Ico_left (Nat.zero_le a)) _]
  simp
  intro x hxb hbx
  rw [Nat.factorization_eq_zero_of_non_prime]; simp
  intro hp
  have hp := Nat.Prime.two_le hp
  specialize hbx (le_trans ha hp)
  linarith

-- Primes greater than sqrt(2n) have multiplicity at most 1.
lemma prodIocSqrtLePowLeProdPrimes {n a b : ℕ} (ha : Nat.sqrt (2*n) ≤ a)
    : ∏ p in (Finset.Ioc a b), p^(Nat.factorization (Nat.centralBinom n) p) ≤
      ∏ p in primes (Finset.Ioc a b), p := by
  rw [primes]
  rw [← @Finset.prod_filter_of_ne _ _ _ _ _ Nat.Prime]
  . apply Finset.prod_le_prod'
    simp
    intro p hbp _ hp
    replace hbp := lt_of_le_of_lt ha hbp
    conv => rhs; rw [← Nat.pow_one p]
    rw [pow_le_pow_iff (Nat.Prime.one_lt hp)]
    rw [Nat.sqrt_lt'] at hbp
    exact leOne hp hbp
  . intro p _
    apply primeOfPowFactorizationNeOne

lemma prodIocSqrtPowLeProdPrimes {n b : ℕ}
    : ∏ p in (Finset.Ioc (Nat.sqrt (2*n)) b), p^(Nat.factorization (Nat.centralBinom n) p) ≤
      ∏ p in primes (Finset.Ioc (Nat.sqrt (2*n)) b), p :=
  prodIocSqrtLePowLeProdPrimes (le_refl _)

end FactorizationCentralBinom


lemma sqrtTwoMulLeSelf {n : ℕ} (hn : 2 ≤ n) : Nat.sqrt (2*n) ≤ n := by
  conv => rhs; rw [← Nat.sqrt_eq n]
  apply Nat.sqrt_le_sqrt
  exact Nat.mul_le_mul_right _ hn

lemma prodRangePowFactorization {n : ℕ}
    : ∏ p in Finset.range b, p ^ Nat.factorization n p =
      ∏ p in Finset.Ico 1 b, p ^ Nat.factorization n p := by
  cases b with
  | zero => simp
  | succ b =>
    rw [← Finset.prod_range_mul_prod_Ico _ (Nat.zero_lt_succ _)]
    simp

lemma powFactorizationPos (n p : ℕ) : 0 < p ^ Nat.factorization n p := by
  cases p with
  | zero => simp
  | succ p => exact Nat.one_le_pow _ _ (Nat.zero_lt_succ _)

lemma prodLeProdMulProdOfUnionOfOneLe {s t₁ t₂ : Finset ℕ} {f : ℕ → ℕ}
    (hs : s ⊆ t₁ ∪ t₂) (hf : ∀ y, 1 ≤ f y)
    : ∏ x in s, f x ≤ (∏ x in t₁, f x) * ∏ x in t₂, f x := by
  rw [← Finset.prod_union_inter]
  apply le_trans _ (Nat.le_mul_of_pos_right _)
  . exact Finset.prod_mono_set_of_one_le' hf hs
  . apply Finset.prod_pos
    intro x _
    apply hf

lemma mulDivLeSelf {n a b : ℕ} (hab : a ≤ b) : a*n/b ≤ n := by
  cases b with
  | zero => simp
  | succ b =>
    conv => rhs; rw [← Nat.mul_div_right n (Nat.zero_lt_succ b)]
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul_right _ hab

lemma mulRightLeOfLeOne {x y z : ℕ} (h1 : x ≤ 1) (h : y ≤ z) : x * y ≤ z := by
  rw [← Nat.one_mul z]
  apply Nat.mul_le_mul h1 h

lemma mulLeftLeOfLeOne {x y z : ℕ} (h1 : y ≤ 1) (h : x ≤ z) : x * y ≤ z := by
  rw [← Nat.mul_one z]
  apply Nat.mul_le_mul h h1

theorem fourPowLeMulProdPrimes {n : ℕ} (hn : 2 < n)
    : 4^n ≤ (2*n) ^ (1 + Nat.sqrt (2*n)) * 4^(2*n/3).pred
      * (∏ p in primes (Finset.Ioc n (2*n)), p) := by
  apply le_trans (Nat.four_pow_le_two_mul_self_mul_centralBinom _ (by linarith))
  -- Cancel the (2n) factor.
  rw [Nat.one_add, Nat.pow_succ]
  have : ∀ {x y z : ℕ}, x * (2*n) * y * z = (2*n) * (x * y * z) := by intro x y z; linarith
  rw [this]; clear this
  apply Nat.mul_le_mul_left
  rw [← Nat.prod_pow_factorization_centralBinom]
  -- Split product at sqrt(2n).
  rw [Finset.range_eq_Ico]
  conv => lhs; rw [← Finset.prod_Ico_consecutive _ (Nat.zero_le _) (Nat.succ_le_succ (Nat.sqrt_le_self _))]
  simp [Nat.Ico_succ_succ]
  conv => rhs; rw [mul_assoc]
  apply Nat.mul_le_mul
  . -- Use loose bound (2n)^sqrt(2n) for primes up to sqrt(2n).
    rw [FactorizationCentralBinom.prodRangePowEqProdIcoPowOfLeTwo (Nat.le_succ _ : 1 ≤ 2)]
    apply le_of_le_of_eq (FactorizationCentralBinom.prodIcoPowLePow' _)
    . norm_num
    . intro hn; rw [hn]; norm_num
  . -- Use union of (sqrt(2n), 2n/3] and (2n/3, n]; may overlap.
    have hs : Finset.Ioc (Nat.sqrt (2*n)) (2*n) ⊆ Finset.Ioc (Nat.sqrt (2*n)) (2*n/3) ∪ Finset.Ioc (2*n/3) (2*n)
    . repeat rw [← Nat.Ico_succ_succ]
      apply Finset.Ico_subset_Ico_union_Ico
    apply le_trans (prodLeProdMulProdOfUnionOfOneLe hs (powFactorizationPos _))
    clear hs
    apply Nat.mul_le_mul
    . -- Bound product of factors in (sqrt(2n), 2n/3] by product of primes in (1, 2n/3].
      apply le_trans FactorizationCentralBinom.prodIocSqrtPowLeProdPrimes
      apply le_trans _ (@prodPrimesLePowFour (2*n/3))
      rw [prodPrimes, Finset.range_eq_Ico, Nat.Ico_succ_right]
      apply Finset.prod_le_prod_of_subset_of_one_le' <;> rw [primes]
      . apply Finset.monotone_filter_left
        exact Finset.Ioc_subset_Iic_self
      . intro p hp _
        simp at hp
        replace hp := Nat.Prime.one_lt hp.right
        linarith
    . -- Split factors at n.
      conv => lhs; rw [← Finset.prod_Ioc_consecutive _ (mulDivLeSelf (by norm_num)) (by linarith : n ≤ 2*n)]
      apply mulRightLeOfLeOne
      . -- No factors in (2n/3, n].
        apply le_of_eq
        apply Finset.prod_eq_one
        intro x hx
        simp at hx
        rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hx.right]
        . simp
        . apply @Nat.lt_of_div_lt_div _ _ 3
          simp
          exact hx.left
      . -- Bound product of factors by product of primes.
        apply FactorizationCentralBinom.prodIocSqrtLePowLeProdPrimes
        exact sqrtTwoMulLeSelf (le_of_lt hn)
