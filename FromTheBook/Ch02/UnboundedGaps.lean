import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Linarith

def PrimeRange : ℕ → List ℕ := List.filter Nat.Prime ∘ List.range

namespace PrimeRange

def prod : ℕ → ℕ := List.prod ∘ PrimeRange

lemma prodNeZero {k : ℕ} : prod k ≠ 0 := by
  simp [prod, PrimeRange, List.mem_filter]

lemma prodPos {k : ℕ} : 0 < prod k :=
  Nat.pos_of_ne_zero prodNeZero

lemma prodDvdOfLt {k p : ℕ} (hp : Nat.Prime p) :
    p < k → p ∣ prod k := by
  intro hk
  apply List.dvd_prod
  simp [PrimeRange, List.mem_filter]
  exact ⟨hk, hp⟩

end PrimeRange


lemma gapAfterProdPrimeRange {k u : ℕ} :
    2 ≤ u ∧ u ≤ k.succ → ¬Nat.Prime (PrimeRange.prod k.succ.succ + u) := by
  intros
  rw [Nat.prime_def_lt']
  simp
  intros
  have : u ≠ 1
  . linarith
  cases Nat.exists_prime_and_dvd this with
  | intro p hp =>
    exists p
    have hu_pos : 0 < u
    . linarith
    have hpu : p ≤ u := Nat.le_of_dvd hu_pos hp.right
    apply And.intro
    . apply lt_of_le_of_lt hpu
      apply Nat.lt_add_of_pos_left
      apply PrimeRange.prodPos
    . apply And.intro
      . exact Nat.Prime.two_le hp.left
      . apply Nat.dvd_add _ hp.right
        apply PrimeRange.prodDvdOfLt hp.left
        linarith

theorem existsGap (k : ℕ) : ∃ m, ∀ x, x < k → ¬Nat.Prime (m + x) := by
  exists PrimeRange.prod k.succ.succ + 2
  intros x hx
  rw [add_assoc]
  apply gapAfterProdPrimeRange
  simp
  linarith
