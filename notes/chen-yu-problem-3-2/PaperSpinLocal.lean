import LocalLaurent

/-! The five local cases of Theorem 2.1, with the m=0 case included in even 0.
The plus and minus pole-bound equivalences are proved coefficientwise via
the previously constructed descent and parity lemmas. -/
noncomputable section
namespace Problem32.PaperSpinLocal
open Problem32.LocalLaurent

inductive SpinKind where
  | even (r : ℕ)
  | oddOne (r : ℕ)
  | oddThree (r : ℕ)
  | simplePole

def order : SpinKind → ℤ
  | .even r => 4*(r : ℤ)
  | .oddOne r => 4*(r : ℤ)+1
  | .oddThree r => 4*(r : ℤ)+3
  | .simplePole => -1

def contribution : SpinKind → ℤ
  | .even r => r
  | .oddOne r => r
  | .oddThree r => r+1
  | .simplePole => 0

def lowerBound : SpinKind → ℤ
  | .even r => -(r : ℤ)
  | .oddOne r => -(2*(r : ℤ)+1)
  | .oddThree r => -(2*(r : ℤ)+2)
  | .simplePole => 0

def plusMap : SpinKind → Series →ₗ[ℂ] Series
  | .even _ => LinearMap.id
  | _ => doubleShift 0

def minusMap : SpinKind → Series →ₗ[ℂ] Series
  | .even r => shift (-2*(r : ℤ))
  | .oddOne r => doubleShift (-(4*(r : ℤ)+1))
  | .oddThree r => doubleShift (-(4*(r : ℤ)+3))
  | .simplePole => doubleShift 1

theorem contribution_floor (c : SpinKind) : contribution c = (order c+1)/4 := by
  cases c <;> simp only [contribution, order] <;> omega

theorem doubleShift_bound_rounded (k b l : ℤ)
    (hround : ∀ n : ℤ, (n-b)%2=0 → (n < 2*k+b ↔ n < l)) (f : Series) :
    doubleShift b f ∈ bounded l ↔ f ∈ bounded k := by
  constructor
  · intro h
    have hp : doubleShift b f ∈ paritySpace b ⊓ bounded l := ⟨doubleShift_parity b f, h⟩
    rw [← parity_bounded_congr b (2*k+b) l hround] at hp
    have hd := descend_bounded k b (doubleShift b f) hp.2
    simpa only [descend_doubleShift] using hd
  · intro h
    have hp : doubleShift b f ∈ paritySpace b ⊓ bounded (2*k+b) :=
      ⟨doubleShift_parity b f, doubleShift_bounded k b f h⟩
    rw [parity_bounded_congr b (2*k+b) l hround] at hp
    exact hp.2

theorem plus_bound_iff (c : SpinKind) (f : Series) :
    plusMap c f ∈ bounded (lowerBound c) ↔ f ∈ bounded (-contribution c) := by
  cases c with
  | even r => rfl
  | oddOne r =>
    exact doubleShift_bound_rounded (-(r : ℤ)) 0 (-(2*(r : ℤ)+1)) (by
      intro n hn; omega) f
  | oddThree r =>
    exact doubleShift_bound_rounded (-((r : ℤ)+1)) 0 (-(2*(r : ℤ)+2)) (by
      intro n hn; omega) f
  | simplePole =>
    exact doubleShift_bound_rounded 0 0 0 (by intro n hn; omega) f

theorem minus_bound_iff (c : SpinKind) (f : Series) :
    minusMap c f ∈ bounded (lowerBound c) ↔ f ∈ bounded (contribution c) := by
  cases c with
  | even r =>
    constructor
    · intro h
      have hb := shift_bounded (-(r : ℤ)) (2*(r : ℤ)) _ h
      change shift (2*(r : ℤ)) (shift (-2*(r : ℤ)) f) ∈ bounded (-(r : ℤ)+2*(r : ℤ)) at hb
      have hi : shift (2*(r : ℤ)) (shift (-2*(r : ℤ)) f) = f := by
        convert shift_shift_neg (2*(r : ℤ)) f using 1 <;> congr 2 <;> ring
      rw [hi] at hb
      convert hb using 1 <;> dsimp [contribution] <;> congr 1 <;> ring
    · intro h
      have hb := shift_bounded (r : ℤ) (-2*(r : ℤ)) f h
      convert hb using 1 <;> dsimp [lowerBound, minusMap] <;> congr 1 <;> ring
  | oddOne r =>
    exact doubleShift_bound_rounded (r : ℤ) (-(4*(r : ℤ)+1)) (-(2*(r : ℤ)+1)) (by
      intro n hn; omega) f
  | oddThree r =>
    exact doubleShift_bound_rounded ((r : ℤ)+1) (-(4*(r : ℤ)+3)) (-(2*(r : ℤ)+2)) (by
      intro n hn; omega) f
  | simplePole =>
    exact doubleShift_bound_rounded 0 1 0 (by intro n hn; omega) f

def pullback : SpinKind → Series → Series
  | .even _ => id
  | _ => pullbackDifferential

def omegaLocal : SpinKind → Series
  | .even r => HahnSeries.single (2*(r : ℤ)) 1
  | .oddOne r => HahnSeries.single (4*(r : ℤ)+2) 2
  | .oddThree r => HahnSeries.single (4*(r : ℤ)+4) 2
  | .simplePole => HahnSeries.single 0 2

theorem omegaLocal_ne_zero (c : SpinKind) : omegaLocal c ≠ 0 := by
  cases c <;> exact HahnSeries.single_ne_zero (by norm_num)

theorem reflected_quotient_mul (m : ℤ) (f : Series) :
    doubleShift (-m) f * HahnSeries.single (m+1) 2 = pullbackDifferential f := by
  ext n
  rw [HahnSeries.coeff_mul_single, doubleShift_coeff]
  change (if (n-(m+1)- -m)%2=0 then f.coeff ((n-(m+1)- -m)/2) else 0) * 2 =
    2 * (if (n-1)%2=0 then f.coeff ((n-1)/2) else 0)
  have h : n-(m+1)- -m = n-1 := by ring
  rw [h]
  ring

theorem minus_mul_omega (c : SpinKind) (f : Series) :
    minusMap c f * omegaLocal c = pullback c f := by
  cases c with
  | even r =>
    have h := shift_shift_neg (2*(r : ℤ)) f
    change HahnSeries.single (2*(r : ℤ)) 1 * (HahnSeries.single (-(2*(r : ℤ))) 1 * f) = f at h
    change (HahnSeries.single (-2*(r : ℤ)) 1 * f) * HahnSeries.single (2*(r : ℤ)) 1 = f
    convert (mul_comm _ _).trans h using 1 <;> congr 2 <;> ring
  | oddOne r =>
    have h : 4*(r : ℤ)+1+1 = 4*(r : ℤ)+2 := by ring
    simpa only [minusMap, omegaLocal, pullback, h] using reflected_quotient_mul (4*(r : ℤ)+1) f
  | oddThree r =>
    have h : 4*(r : ℤ)+3+1 = 4*(r : ℤ)+4 := by ring
    simpa only [minusMap, omegaLocal, pullback, h] using reflected_quotient_mul (4*(r : ℤ)+3) f
  | simplePole => simpa only [minusMap, omegaLocal, pullback, neg_neg, neg_add_cancel] using reflected_quotient_mul (-1) f

theorem germ_minus {F : Type*} [Field F] (eval : F →+* Series)
    (c : SpinKind) (x w : F) (v f : Series) (hv : v ≠ 0)
    (hx : pullback c f = eval x * v) (hw : omegaLocal c = eval w * v) :
    eval (x/w) = minusMap c f := by
  have hq := (eq_div_iff (omegaLocal_ne_zero c)).mpr (minus_mul_omega c f)
  rw [map_div₀, hq, hx, hw]
  exact (mul_div_mul_right (eval x) (eval w) hv).symm

#print axioms contribution_floor
#print axioms plus_bound_iff
#print axioms minus_bound_iff
#print axioms germ_minus
end Problem32.PaperSpinLocal


