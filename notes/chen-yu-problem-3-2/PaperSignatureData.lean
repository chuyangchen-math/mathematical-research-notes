import PaperOrientationLocal
import PaperSpinLocal

namespace Problem32.PaperSignatureData
open Problem32.PaperOrientationLocal

def ramificationIndex : ChartKind → ℤ
  | .unramified _ => 1
  | .ramified _ => 2
  | .simplePole => 2

/-- Lemma 3.1: the explicitly integral coefficient -coverOrder is half
the coefficient of the pulled-back divisor. This includes simple poles. -/
theorem lemma_3_1 (c : ChartKind) :
    2 * (-coverOrder c) = ramificationIndex c * baseOrder c := by
  cases c <;> simp [coverOrder, ramificationIndex, baseOrder] <;> ring

theorem integral_half_pullback (c : ChartKind) :
    ∃ e : ℤ, 0 ≤ e ∧ 2*e = ramificationIndex c * baseOrder c := by
  refine ⟨-coverOrder c, ?_, lemma_3_1 c⟩
  cases c <;> simp [coverOrder] <;> omega

open Problem32.PaperSpinLocal
theorem classify_spin_order (m : ℤ) (hm : -1 ≤ m) (hmod : m % 4 ≠ 2) :
    ∃ c : SpinKind, order c = m := by
  by_cases h : m = -1
  · exact ⟨.simplePole, h.symm⟩
  have hnonneg : 0 ≤ m := by omega
  have hq : 0 ≤ m/4 := Int.ediv_nonneg hnonneg (by omega)
  have hcast : ((m/4).toNat : ℤ) = m/4 := Int.toNat_of_nonneg hq
  have hrem := Int.emod_nonneg m (by norm_num : (4 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 4)
  by_cases hzero : m % 4 = 0
  · refine ⟨.even (m/4).toNat, ?_⟩
    dsimp [order]; rw [hcast]; omega
  by_cases hone : m % 4 = 1
  · refine ⟨.oddOne (m/4).toNat, ?_⟩
    dsimp [order]; rw [hcast]; omega
  · refine ⟨.oddThree (m/4).toNat, ?_⟩
    dsimp [order]; rw [hcast]; omega

/-- The elementary divisor decomposition div(q)=2A+B used in Section 2. -/
theorem floor_branch_decomposition (m : ℤ) : m = 2*(m/2) + m%2 := by omega

theorem half_omega_order (c : SpinKind) :
    (match c with
      | .even r => 2*(r : ℤ)
      | .oddOne r => 4*(r : ℤ)+2
      | .oddThree r => 4*(r : ℤ)+4
      | .simplePole => 0) = 2 * (-lowerBound c) := by
  cases c <;> simp [lowerBound] <;> ring

theorem spin_degree_formula {J : Type*} (s : Finset J) (c : J → SpinKind) :
    ∑ j ∈ s, contribution (c j) = ∑ j ∈ s, (order (c j)+1)/4 := by
  apply Finset.sum_congr rfl
  intro j hj
  exact contribution_floor (c j)

inductive ExceptionalSignature where
  | g3_9 | g3_6_3 | g3_3_3_3
  | g4_12 | g4_9_3 | g4_6_6 | g4_6_3_3 | g4_3_3_3_3
  deriving DecidableEq

def genus : ExceptionalSignature → ℤ
  | .g3_9 | .g3_6_3 | .g3_3_3_3 => 3
  | _ => 4

def zeroMultiplicities : ExceptionalSignature → List ℤ
  | .g3_9 => [9]
  | .g3_6_3 => [6,3]
  | .g3_3_3_3 => [3,3,3]
  | .g4_12 => [12]
  | .g4_9_3 => [9,3]
  | .g4_6_6 => [6,6]
  | .g4_6_3_3 => [6,3,3]
  | .g4_3_3_3_3 => [3,3,3,3]

def divisorDegree (s : ExceptionalSignature) : ℤ :=
  ((zeroMultiplicities s).map (fun m => m/3)).sum

theorem degree_equals_genus (s : ExceptionalSignature) : divisorDegree s = genus s := by
  cases s <;> norm_num [divisorDegree, zeroMultiplicities, genus]

/-- The genus-four theorem is only used on its non-hyperelliptic locus. -/
def Eligible (s : ExceptionalSignature) (nonhyperelliptic : Prop) : Prop :=
  genus s = 3 ∨ (genus s = 4 ∧ nonhyperelliptic)

#print axioms lemma_3_1
#print axioms classify_spin_order
#print axioms half_omega_order
#print axioms spin_degree_formula
#print axioms degree_equals_genus
end Problem32.PaperSignatureData
