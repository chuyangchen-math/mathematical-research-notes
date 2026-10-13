
import Mathlib

namespace McMullen313

/-!
# Finite Sector Automaton

This module develops the abstract finite permutation
underlying the sector cycles of an unfolding.

The geometric construction and verification of the
sector transition will be handled separately.
-/

/-! ## 1. Finite sector states -/

structure SectorState (n m k : Nat) where
  copy   : Fin n
  vertex : Fin m
  side   : Fin k
deriving DecidableEq, Fintype

/-! ## 2. Sector transition system -/

structure SectorSystem (n m k : Nat) where
  next :
    SectorState n m k →
    SectorState n m k

  next_bijective :
    Function.Bijective next

/-! ## 3. Associated permutation -/

noncomputable def sectorEquiv
    {n m k : Nat}
    (S : SectorSystem n m k) :
    SectorState n m k ≃ SectorState n m k :=
  Equiv.ofBijective S.next S.next_bijective

theorem sectorEquiv_apply
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k) :
    sectorEquiv S s = S.next s := by
  rfl

/-! ## 4. Iteration -/

def iterate
    {n m k : Nat}
    (S : SectorSystem n m k) :
    Nat → SectorState n m k → SectorState n m k
  | 0, s =>
      s
  | t + 1, s =>
      S.next (iterate S t s)

theorem iterate_zero
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k) :
    iterate S 0 s = s := by
  rfl

theorem iterate_succ
    {n m k : Nat}
    (S : SectorSystem n m k)
    (t : Nat)
    (s : SectorState n m k) :
    iterate S (t + 1) s =
      S.next (iterate S t s) := by
  rfl

theorem iterate_add
    {n m k : Nat}
    (S : SectorSystem n m k)
    (a b : Nat)
    (s : SectorState n m k) :
    iterate S (a + b) s =
      iterate S a (iterate S b s) := by
  induction a with
  | zero =>
      simp [iterate]
  | succ a ih =>
      simp [Nat.succ_add, iterate, ih]

/-! ## 5. Injectivity and surjectivity -/

theorem next_injective
    {n m k : Nat}
    (S : SectorSystem n m k) :
    Function.Injective S.next :=
  S.next_bijective.1

theorem next_surjective
    {n m k : Nat}
    (S : SectorSystem n m k) :
    Function.Surjective S.next :=
  S.next_bijective.2

theorem iterate_injective
    {n m k : Nat}
    (S : SectorSystem n m k)
    (t : Nat) :
    Function.Injective (iterate S t) := by
  induction t with
  | zero =>
      intro x y h
      exact h
  | succ t ih =>
      intro x y h
      apply ih
      apply next_injective S
      exact h

/-! ## 6. Commutation with the successor -/

theorem iterate_next
    {n m k : Nat}
    (S : SectorSystem n m k)
    (r : Nat)
    (s : SectorState n m k) :
    iterate S r (S.next s) =
      S.next (iterate S r s) := by
  induction r with
  | zero =>
      rfl
  | succ r ih =>
      change
        S.next (iterate S r (S.next s)) =
          S.next (S.next (iterate S r s))
      rw [ih]

/-! ## 7. Return times -/

def IsReturn
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k)
    (r : Nat) : Prop :=
  r > 0 ∧ iterate S r s = s

private theorem return_of_repeat
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k)
    (i j : Nat)
    (hij : i < j)
    (heq : iterate S i s = iterate S j s) :
    ∃ r : Nat, IsReturn S s r := by

  let r := j - i

  have hrpos : 0 < r := by
    dsimp [r]
    omega

  have hij_add : i + r = j := by
    dsimp [r]
    omega

  have hcancel :
      iterate S i (iterate S r s) =
        iterate S i s := by
    calc
      iterate S i (iterate S r s) =
          iterate S (i + r) s :=
        (iterate_add S i r s).symm
      _ = iterate S j s := by
        rw [hij_add]
      _ = iterate S i s :=
        heq.symm

  have hreturn : iterate S r s = s :=
    (iterate_injective S i) hcancel

  exact ⟨r, hrpos, hreturn⟩

/-! ## 8. Existence of a return time -/

theorem exists_return
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k) :
    ∃ r : Nat, IsReturn S s r := by

  classical

  let N := Fintype.card (SectorState n m k)

  have hcard :
      Fintype.card (SectorState n m k) <
        Fintype.card (Fin (N + 1)) := by
    simp [N]

  obtain ⟨i, j, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun x : Fin (N + 1) =>
        iterate S x.val s)
      hcard

  have hval : i.val ≠ j.val := by
    intro h
    apply hne
    exact Fin.ext h

  rcases lt_or_gt_of_ne hval with hij | hji

  · exact
      return_of_repeat S s
        i.val j.val hij heq

  · exact
      return_of_repeat S s
        j.val i.val hji heq.symm

/-! ## 9. Minimal positive period -/

noncomputable def sectorPeriod
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k) : Nat := by
  classical
  exact Nat.find (exists_return S s)

theorem sectorPeriod_spec
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k) :
    IsReturn S s (sectorPeriod S s) := by
  classical
  exact Nat.find_spec (exists_return S s)

theorem sectorPeriod_positive
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k) :
    0 < sectorPeriod S s :=
  (sectorPeriod_spec S s).1

theorem iterate_sectorPeriod
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k) :
    iterate S (sectorPeriod S s) s = s :=
  (sectorPeriod_spec S s).2

/-! ## 10. Minimality -/

theorem sectorPeriod_minimal
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k)
    (r : Nat)
    (hr : IsReturn S s r) :
    sectorPeriod S s ≤ r := by
  classical
  exact Nat.find_min' (exists_return S s) hr

theorem sectorPeriod_no_earlier_return
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k)
    (r : Nat)
    (hr : r < sectorPeriod S s) :
    ¬ IsReturn S s r := by
  intro hreturn
  have hle := sectorPeriod_minimal S s r hreturn
  omega

/-! ## 11. Return times along the orbit -/

theorem isReturn_next_iff
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k)
    (r : Nat) :
    IsReturn S (S.next s) r ↔
      IsReturn S s r := by

  constructor

  · intro h
    rcases h with ⟨hpos, heq⟩
    refine ⟨hpos, ?_⟩

    apply next_injective S

    calc
      S.next (iterate S r s) =
          iterate S r (S.next s) :=
        (iterate_next S r s).symm
      _ = S.next s := heq

  · intro h
    rcases h with ⟨hpos, heq⟩
    refine ⟨hpos, ?_⟩

    calc
      iterate S r (S.next s) =
          S.next (iterate S r s) :=
        iterate_next S r s
      _ = S.next s := by
        rw [heq]

/-! ## 12. Invariance of the minimal period -/

theorem sectorPeriod_invariant
    {n m k : Nat}
    (S : SectorSystem n m k)
    (s : SectorState n m k) :
    sectorPeriod S (S.next s) =
      sectorPeriod S s := by

  apply Nat.le_antisymm

  · apply sectorPeriod_minimal
      S (S.next s) (sectorPeriod S s)

    exact
      (isReturn_next_iff
        S s (sectorPeriod S s)).2
        (sectorPeriod_spec S s)

  · apply sectorPeriod_minimal
      S s (sectorPeriod S (S.next s))

    exact
      (isReturn_next_iff
        S s (sectorPeriod S (S.next s))).1
        (sectorPeriod_spec S (S.next s))

/-! ## 13. Global permutation order -/

noncomputable def sectorOrder
    {n m k : Nat}
    (S : SectorSystem n m k) : Nat :=
  orderOf (sectorEquiv S)

theorem sectorOrder_positive
    {n m k : Nat}
    (S : SectorSystem n m k) :
    sectorOrder S > 0 := by
  classical
  unfold sectorOrder
  exact orderOf_pos (sectorEquiv S)

end McMullen313
