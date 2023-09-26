import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

def nums := [2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631, 1259, 2503, 4001]

lemma allPrimeNums : List.All₂ Nat.Prime nums := by
  -- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Prove.20decidable.20statement.20by.20evaluation
  -- Tactic simp will try to reduce (Nat.Prime n) using decide for n up to about 300.
  -- Core of norm_num is more efficient for these larger n.
  -- Therefore, use norm_num1 to avoid simp trying to reduce with decide.
  simp (config := {decide := false}) [nums]
  norm_num1
  simp

lemma existsOfSlowMono {a b : ℕ} {l : List ℕ}
    (hl_mono : List.Chain (fun u v => u < v) a l)
    (hl_slow : List.Chain (fun u v => v ≤ 2 * u) a l)
    (hl_cons : l ≠ [])
    (hb : b < List.getLast l hl_cons)
    : ∀ n, n ∈ Set.Icc a b → ∃ lᵢ, lᵢ ∈ l ∧ lᵢ ∈ Set.Ioc n (2*n) := by
  cases l with
  | nil => contradiction
  | cons x l =>
    induction l generalizing a x with
    | nil =>
      intro n hn
      simp at *
      apply And.intro <;> linarith
    | cons y l h =>
      rw [List.chain_cons] at hl_mono
      rw [List.chain_cons] at hl_slow
      simp at hb
      specialize @h x y hl_mono.right hl_slow.right (List.cons_ne_nil y l) hb
      intro n hn
      specialize h n
      have : ∀ lᵢ, lᵢ ∈ x :: y :: l ↔ lᵢ = x ∨ lᵢ ∈ y :: l := by simp
      simp_rw [this]
      simp only [or_and_right]
      rw [exists_or]
      cases le_or_lt x n with
      | inl hx =>
        apply Or.inr
        simp only [Set.mem_Ico] at *
        specialize h (And.intro hx hn.right)
        exact h
      | inr hx =>
        apply Or.inl
        simp at *
        apply And.intro <;> linarith

theorem landauTrick {n : ℕ} (hn_pos : 0 < n) (hn_lt : n ≤ 4000)
    : ∃ p, p ∈ Set.Ioc n (2*n) ∧ Nat.Prime p := by
  intros
  have hp : n ∈ Set.Icc 1 4000 → ∃ p, p ∈ nums ∧ p ∈ Set.Ioc n (2*n)
  . apply existsOfSlowMono <;> simp [nums]
  have hp : ∃ p, p ∈ nums ∧ p ∈ Set.Ioc n (2*n)
  . apply hp
    apply And.intro <;> linarith
  cases hp with
  | intro p hp =>
    exists p
    apply And.intro hp.right
    refine List.all₂_iff_forall.mp ?_ p hp.left
    exact allPrimeNums
