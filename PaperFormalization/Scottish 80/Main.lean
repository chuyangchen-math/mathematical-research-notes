import Mathlib

namespace Scottish80

open Set Topology

/-- `F_σ`: by De Morgan, this is exactly a countable union of closed sets. -/
def IsFSigma {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  IsGδ sᶜ

/-- `F_{σδ}`: a countable intersection of `F_σ` sets. -/
def IsFSigmaDelta {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ (ι : Type) (f : ι → Set X),
    Countable ι ∧ (∀ i, IsFSigma (f i)) ∧ s = ⋂ i, f i

/-- `F_{σδσ}`: a countable union of `F_{σδ}` sets.  This is included only so that
    the literal conclusion asked for in Problem 80 can be stated verbatim. -/
def IsFSigmaDeltaSigma {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ (ι : Type) (f : ι → Set X),
    Countable ι ∧ (∀ i, IsFSigmaDelta (f i)) ∧ s = ⋃ i, f i

namespace IsFSigma

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Continuous preimages preserve `F_σ`. -/
theorem preimage {f : X → Y} {s : Set Y} (hs : IsFSigma s) (hf : Continuous f) :
    IsFSigma (f ⁻¹' s) := by
  rw [IsFSigma] at hs ⊢
  simpa only [Set.preimage_compl] using hs.preimage hf

end IsFSigma

namespace IsFSigmaDelta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every `F_σ` set is `F_{σδ}`. -/
theorem of_isFSigma {s : Set X} (hs : IsFSigma s) : IsFSigmaDelta s := by
  refine ⟨Unit, fun _ => s, inferInstance, ?_, ?_⟩
  · intro i
    exact hs
  · ext x
    simp

/-- Continuous preimages preserve `F_{σδ}`. -/
theorem preimage {f : X → Y} {s : Set Y} (hs : IsFSigmaDelta s) (hf : Continuous f) :
    IsFSigmaDelta (f ⁻¹' s) := by
  rcases hs with ⟨ι, g, hι, hg, hs⟩
  refine ⟨ι, fun i => f ⁻¹' g i, hι, ?_, ?_⟩
  · intro i
    exact (hg i).preimage hf
  · rw [hs]
    ext x
    simp

/-- Finite intersections preserve `F_{σδ}`. -/
theorem inter {s t : Set X} (hs : IsFSigmaDelta s) (ht : IsFSigmaDelta t) :
    IsFSigmaDelta (s ∩ t) := by
  rcases hs with ⟨ι, f, hι, hf, hs⟩
  rcases ht with ⟨κ, g, hκ, hg, ht⟩
  refine ⟨Sum ι κ, Sum.elim f g, @instCountableSum ι κ hι hκ, ?_, ?_⟩
  · intro z
    cases z with
    | inl i => exact hf i
    | inr j => exact hg j
  · rw [hs, ht]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hsi, hti⟩ z
      cases z with
      | inl i => exact hsi i
      | inr j => exact hti j
    · intro h
      exact ⟨fun i => h (Sum.inl i), fun j => h (Sum.inr j)⟩

end IsFSigmaDelta

section SigmaOperation

variable {E : Type*} [TopologicalSpace E]

/-- All coordinates lie in `R`. -/
def AllCoords (R : Set E) : Set (ℕ → E) :=
  {x | ∀ n, x n ∈ R}

/-- The sequence is eventually equal to the fixed point `r₀`. -/
def EventuallyEq (r₀ : E) : Set (ℕ → E) :=
  {x | ∃ N, ∀ n, N ≤ n → x n = r₀}

/-- The literal `R^σ` occurring in Scottish Book Problem 80. -/
def SigmaSet (R : Set E) (r₀ : E) : Set (ℕ → E) :=
  AllCoords R ∩ EventuallyEq r₀

/-- If `R` is `F_{σδ}`, then the condition that every coordinate lies in `R`
    is again `F_{σδ}` in the product. -/
theorem allCoords_isFSigmaDelta {R : Set E} (hR : IsFSigmaDelta R) :
    IsFSigmaDelta (AllCoords R) := by
  rcases hR with ⟨ι, g, hι, hg, hR⟩
  refine ⟨ℕ × ι,
    fun p => (fun x : ℕ → E => x p.1) ⁻¹' g p.2,
    @instCountableProd ℕ ι inferInstance hι, ?_, ?_⟩
  · intro p
    exact (hg p.2).preimage (continuous_apply p.1)
  · rw [hR]
    ext x
    simp only [AllCoords, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h p
      exact h p.1 p.2
    · intro h n i
      exact h (n, i)

/-- Put a variable in the first coordinate and freeze all later coordinates at `r₀`. -/
def headEmbed (r₀ : E) (t : E) : ℕ → E
  | 0 => t
  | _ + 1 => r₀

/-- The head embedding is continuous for the product topology. -/
theorem continuous_headEmbed (r₀ : E) : Continuous (headEmbed r₀) := by
  apply continuous_pi
  intro n
  cases n with
  | zero =>
      change Continuous (fun t : E => t)
      fun_prop
  | succ n =>
      change Continuous (fun _ : E => r₀)
      fun_prop

/- If `r₀ ∈ R`, the preimage of the literal `R^σ` under the head embedding is exactly `R`. -/
omit [TopologicalSpace E] in
theorem preimage_sigmaSet_headEmbed {R : Set E} {r₀ : E} (hr₀ : r₀ ∈ R) :
    headEmbed r₀ ⁻¹' SigmaSet R r₀ = R := by
  ext t
  constructor
  · intro ht
    change (∀ n, headEmbed r₀ t n ∈ R) ∧
      (∃ N, ∀ n, N ≤ n → headEmbed r₀ t n = r₀) at ht
    simpa [headEmbed] using ht.1 0
  · intro ht
    change (∀ n, headEmbed r₀ t n ∈ R) ∧
      (∃ N, ∀ n, N ≤ n → headEmbed r₀ t n = r₀)
    constructor
    · intro n
      cases n with
      | zero => simpa [headEmbed] using ht
      | succ n => simpa [headEmbed] using hr₀
    · refine ⟨1, ?_⟩
      intro n hn
      cases n with
      | zero => omega
      | succ n => simp [headEmbed]


/-- Consequently, if `R` is not `F_σ`, then neither is the literal `R^σ`. -/
theorem sigmaSet_not_isFSigma {R : Set E} {r₀ : E}
    (hR : ¬ IsFSigma R) (hr₀ : r₀ ∈ R) :
    ¬ IsFSigma (SigmaSet R r₀) := by
  intro hσ
  have hp := hσ.preimage (continuous_headEmbed r₀)
  rw [preimage_sigmaSet_headEmbed hr₀] at hp
  exact hR hp


variable [T2Space E]

/-- The eventual-equality condition is `F_σ`. -/
theorem eventuallyEq_isFSigma (r₀ : E) : IsFSigma (EventuallyEq r₀) := by
  rw [IsFSigma]
  have hcompl :
      (EventuallyEq r₀)ᶜ =
        ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_h : N ≤ n), {x : ℕ → E | x n ≠ r₀} := by
    ext x
    simp only [EventuallyEq, Set.mem_compl_iff, Set.mem_ofPred_eq,
      Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h N
      by_contra hN
      apply h
      refine ⟨N, ?_⟩
      intro n hn
      by_contra hne
      exact hN ⟨n, hn, hne⟩
    · intro h hex
      rcases hex with ⟨N, hN⟩
      rcases h N with ⟨n, hn, hne⟩
      exact hne (hN n hn)
  rw [hcompl]
  apply IsGδ.iInter_of_isOpen
  intro N
  apply isOpen_iUnion
  intro n
  apply isOpen_iUnion
  intro hn
  exact (isClosed_eq (continuous_apply n) continuous_const).isOpen_compl

/-- The key upper-bound theorem: the literal `R^σ` does not leave `F_{σδ}`. -/
theorem sigmaSet_isFSigmaDelta {R : Set E} {r₀ : E} (hR : IsFSigmaDelta R) :
    IsFSigmaDelta (SigmaSet R r₀) := by
  exact (allCoords_isFSigmaDelta hR).inter
    (IsFSigmaDelta.of_isFSigma (eventuallyEq_isFSigma r₀))

end SigmaOperation

section ConcreteCounterexample

/-- The embedded rational numbers. -/
def RatSet : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))

/-- The irrational reals. -/
def IrrSet : Set ℝ := RatSetᶜ

/-- `ℝ` satisfies the completeness hypothesis of the original problem. -/
theorem real_complete : CompleteSpace ℝ := inferInstance

/-- The irrationals are `F_{σδ}`: intersect the complements of all rational singletons. -/
theorem irrSet_isFSigmaDelta : IsFSigmaDelta IrrSet := by
  refine ⟨ℚ, fun q => ({(q : ℝ)}ᶜ : Set ℝ), inferInstance, ?_, ?_⟩
  · intro q
    rw [IsFSigma]
    simpa using (IsGδ.singleton (q : ℝ))
  · ext x
    simp only [IrrSet, RatSet, Set.mem_compl_iff, Set.mem_range,
      Set.mem_iInter, Set.mem_singleton_iff, not_exists]
    constructor
    · intro h q hxq
      exact h q hxq.symm
    · intro h q hqx
      exact h q hqx.symm

/-- The rational numbers form a meagre subset of `ℝ`. -/
theorem ratSet_isMeagre : IsMeagre RatSet := by
  rw [show RatSet = ⋃ q : ℚ, ({(q : ℝ)} : Set ℝ) by
    ext x
    simp [RatSet]]
  apply isMeagre_iUnion
  intro q
  exact ((isClosed_singleton : IsClosed ({(q : ℝ)} : Set ℝ)).isNowhereDense_iff.mpr
    (interior_singleton (q : ℝ))).isMeagre

/-- The irrationals are not `F_σ`, by Baire category and density of `ℚ` in `ℝ`. -/
theorem irrSet_not_isFSigma : ¬ IsFSigma IrrSet := by
  intro hR
  have hQG : IsGδ RatSet := by
    rw [IsFSigma] at hR
    simpa [IrrSet] using hR
  have hQdense : Dense RatSet := by
    change DenseRange ((↑) : ℚ → ℝ)
    exact Rat.denseRange_cast
  exact (not_isMeagre_of_isGδ_of_dense hQG hQdense) ratSet_isMeagre

/-- `√2` is an admissible fixed point in the irrational set. -/
theorem sqrtTwo_mem_irrSet : Real.sqrt 2 ∈ IrrSet := by
  change Irrational (Real.sqrt 2)
  exact irrational_sqrt_two

/-- The literal `R^σ` for the concrete Scottish-80 counterexample is still `F_{σδ}`. -/
theorem concrete_sigma_isFSigmaDelta :
    IsFSigmaDelta (SigmaSet IrrSet (Real.sqrt 2)) :=
  sigmaSet_isFSigmaDelta irrSet_isFSigmaDelta

/-- In fact it remains outside `F_σ` as well. -/
theorem concrete_sigma_not_isFSigma :
    ¬ IsFSigma (SigmaSet IrrSet (Real.sqrt 2)) :=
  sigmaSet_not_isFSigma irrSet_not_isFSigma sqrtTwo_mem_irrSet

/-- The universal `σ`-assertion asked for in the literal statement of Problem 80:
    every complete metric-space input in `F_{σδ} \ F_σ` should be sent by the printed
    `σ`-operation into `F_{σδσ} \ F_{σδ}`. -/
def Problem80SigmaAssertion : Prop :=
  ∀ (E : Type) [MetricSpace E] [CompleteSpace E] (R : Set E) (r₀ : E),
    IsFSigmaDelta R → ¬ IsFSigma R → r₀ ∈ R →
      IsFSigmaDeltaSigma (SigmaSet R r₀) ∧ ¬ IsFSigmaDelta (SigmaSet R r₀)

/-- Fully formal counterexample data for the literal `σ`-assertion. -/
theorem scottishBook80_negative :
    IsFSigmaDelta IrrSet ∧
    ¬ IsFSigma IrrSet ∧
    Real.sqrt 2 ∈ IrrSet ∧
    IsFSigmaDelta (SigmaSet IrrSet (Real.sqrt 2)) ∧
    ¬ IsFSigma (SigmaSet IrrSet (Real.sqrt 2)) := by
  exact ⟨irrSet_isFSigmaDelta,
    irrSet_not_isFSigma,
    sqrtTwo_mem_irrSet,
    concrete_sigma_isFSigmaDelta,
    concrete_sigma_not_isFSigma⟩


/-- Hence the literal universal `σ`-assertion in Scottish Book Problem 80 is false. -/
theorem problem80SigmaAssertion_false : ¬ Problem80SigmaAssertion := by
  intro h
  have hbad := h ℝ IrrSet (Real.sqrt 2)
    irrSet_isFSigmaDelta irrSet_not_isFSigma sqrtTwo_mem_irrSet
  exact hbad.2 concrete_sigma_isFSigmaDelta

end ConcreteCounterexample

#print axioms Scottish80.problem80SigmaAssertion_false

end Scottish80
