import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Prime

open BigOperators

def primes : Finset ℕ → Finset ℕ := Finset.filter Nat.Prime

def prodPrimes (n : ℕ) : ℕ := ∏ p in primes (Finset.range n.succ), p

lemma prodPrimesSplit {b a : ℕ} (ha : a ≤ b)
    : prodPrimes b = prodPrimes a * ∏ p in primes (Finset.Ioc a b), p := by
  rw [← Nat.Ico_succ_succ]
  simp [prodPrimes, primes]
  rw [Finset.range_eq_Ico]
  rw [← Finset.prod_union]
  . rw [← Finset.filter_union]
    rw [Finset.Ico_union_Ico_eq_Ico (Nat.zero_le a.succ) (Nat.succ_le_succ ha)]
  . apply Finset.disjoint_filter_filter
    apply Finset.Ico_disjoint_Ico_consecutive
