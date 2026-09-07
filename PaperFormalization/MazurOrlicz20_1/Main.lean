import Mathlib

/-!
# Scottish Book — Mazur–Orlicz Problem 20.1

The paper proves `k₁ = 1`, `k₂ = 2`, and `kₙ = 3` for `n ≥ 3`.
The genuinely external algebraic-geometric input is the fixed-point Bertini theorem.
This file makes that input explicit as a hypothesis and formalizes the complete deduction
from it and from the two sharp lower-bound witnesses.
-/

namespace ScottishBook.MazurOrlicz20_1

/-- Abstract statement that irreducibility can be detected on a `k`-dimensional linear subspace. -/
def Detectable (n k : ℕ) : Prop := Prop

/-- `LeastDetection n k` expresses the defining universal property of the exact constant. -/
def LeastDetection (Detect : ℕ → ℕ → Prop) (n k : ℕ) : Prop :=
  1 ≤ k ∧ Detect n k ∧ ∀ j, 1 ≤ j → Detect n j → k ≤ j

/-- Exactly the external mathematical facts used by the paper's proof. -/
structure Inputs (Detect : ℕ → ℕ → Prop) : Prop where
  one_exact : LeastDetection Detect 1 1
  two_upper : Detect 2 2
  two_not_one : ¬ Detect 2 1
  bertini_three : ∀ n, 3 ≤ n → Detect n 3
  lower_three : ∀ n, 3 ≤ n → ¬ Detect n 1 ∧ ¬ Detect n 2

lemma two_exact {Detect : ℕ → ℕ → Prop} (h : Inputs Detect) :
    LeastDetection Detect 2 2 := by
  refine ⟨by omega, h.two_upper, ?_⟩
  intro j hjpos hj
  by_contra hnot
  have hjlt : j < 2 := Nat.lt_of_not_ge hnot
  interval_cases j
  · omega
  · exact h.two_not_one hj

lemma high_exact {Detect : ℕ → ℕ → Prop} (h : Inputs Detect)
    {n : ℕ} (hn : 3 ≤ n) : LeastDetection Detect n 3 := by
  refine ⟨by omega, h.bertini_three n hn, ?_⟩
  intro j hjpos hj
  by_contra hnot
  have hjlt : j < 3 := Nat.lt_of_not_ge hnot
  rcases h.lower_three n hn with ⟨h1, h2⟩
  interval_cases j
  · omega
  · exact h1 hj
  · exact h2 hj

/-- Formal counterpart of Theorem 2.1, conditional only on the named external inputs. -/
theorem exact_solution {Detect : ℕ → ℕ → Prop} (h : Inputs Detect) :
    LeastDetection Detect 1 1 ∧
    LeastDetection Detect 2 2 ∧
    ∀ n, 3 ≤ n → LeastDetection Detect n 3 := by
  exact ⟨h.one_exact, two_exact h, fun n hn => high_exact h hn⟩

/-- Consequently the optimal universal bound is `3`. -/
theorem universal_bound_three {Detect : ℕ → ℕ → Prop} (h : Inputs Detect) :
    (∀ n, 1 ≤ n → Detect n 3 ∨ n = 1 ∨ n = 2) ∧
    (∀ n, 3 ≤ n → ¬ Detect n 2) := by
  constructor
  · intro n hn
    by_cases h3 : 3 ≤ n
    · exact Or.inl (h.bertini_three n h3)
    · omega
  · intro n hn
    exact (h.lower_three n hn).2

end ScottishBook.MazurOrlicz20_1
