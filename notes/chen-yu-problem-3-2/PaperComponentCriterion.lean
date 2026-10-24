import PaperResidualGlobal
import PaperSignatureData

noncomputable section
namespace Problem32.PaperComponentCriterion
open Problem32.PaperResidualGlobal Problem32.PaperSignatureData
variable {F X : Type*} [Field F] [Algebra ℂ F]

/-- S is H^0(K-D) in meromorphic coefficients. The membership law is the
definition of a divisor-bounded section (with the zero section separated). -/
theorem positive_sections_iff (A : DivisorTheory F X) (K D : Divisor X)
    (S : Submodule ℂ F) [FiniteDimensional ℂ S]
    (section_definition : ∀ f : F, f ∈ S ↔ f = 0 ∨ ∀ x, D x ≤ tensorDivisor A K 1 f x) :
    0 < Module.finrank ℂ S ↔ ∃ f : F, f ≠ 0 ∧ ∀ x, D x ≤ tensorDivisor A K 1 f x := by
  rw [Module.finrank_pos_iff_exists_ne_zero]
  constructor
  · rintro ⟨f, hf⟩
    have hn : f.val ≠ 0 := by intro h; apply hf; exact Subtype.ext h
    exact ⟨f.val, hn, ((section_definition f.val).mp f.property).resolve_left hn⟩
  · rintro ⟨f, hf, hb⟩
    refine ⟨⟨f, (section_definition f).mpr (Or.inr hb)⟩, ?_⟩
    intro h
    exact hf (congrArg (fun z : S => z.val) h)

theorem positive_iff_residual (A : DivisorTheory F X) (K D P : Divisor X)
    (degree : Divisor X →+ ℤ) (g : ℤ) (q : F) (hq : q ≠ 0)
    (hD : Effective D) (hP : Effective P)
    (hqdiv : tensorDivisor A K 2 q = 3 • D-P) (hdegD : degree D = g)
    (canonical_degree : ∀ f : F, f ≠ 0 → degree (tensorDivisor A K 1 f) = 2*g-2)
    (S : Submodule ℂ F) [FiniteDimensional ℂ S]
    (section_definition : ∀ f : F, f ∈ S ↔ f = 0 ∨ ∀ x, D x ≤ tensorDivisor A K 1 f x) :
    0 < Module.finrank ℂ S ↔ ResidualCubic A K D P degree g q :=
  (positive_sections_iff A K D S section_definition).trans
    (lemma_5_2 A K D P degree g q hq hD hP hqdiv hdegD canonical_degree)

/-- The Riemann--Roch arithmetic used in Theorem 5.3. -/
theorem riemann_roch_threshold (h0O h0K : ℕ)
    (riemann_roch : (h0O : ℤ) - (h0K : ℤ) = 1) :
    0 < h0K ↔ 2 ≤ h0O := by omega

inductive Component where | regular | irregular
  deriving DecidableEq

/-- External Chen--Möller input is used only in its allowed range and only
for its stated section counts. The threshold equivalence is then proved. -/
theorem component_threshold (signature : ExceptionalSignature)
    (nonhyperelliptic : Prop) (eligible : Eligible signature nonhyperelliptic)
    (component : Component) (h0O h0K : ℕ)
    (riemann_roch : (h0O : ℤ) - (h0K : ℤ) = 1)
    (chen_moeller : Eligible signature nonhyperelliptic →
      h0O = match component with | .regular => 1 | .irregular => 2) :
    (0 < h0K ↔ component = .irregular) ∧
      (h0K = 0 ↔ component = .regular) := by
  have hc := chen_moeller eligible
  cases component <;> simp_all <;> omega

theorem theorem_5_3 (A : DivisorTheory F X) (K D P : Divisor X)
    (degree : Divisor X →+ ℤ) (signature : ExceptionalSignature)
    (q : F) (hq : q ≠ 0) (hD : Effective D) (hP : Effective P)
    (hqdiv : tensorDivisor A K 2 q = 3 • D-P)
    (signature_degree : degree D = divisorDegree signature)
    (canonical_degree : ∀ f : F, f ≠ 0 →
      degree (tensorDivisor A K 1 f) = 2*genus signature-2)
    (S : Submodule ℂ F) [FiniteDimensional ℂ S]
    (section_definition : ∀ f : F, f ∈ S ↔ f = 0 ∨ ∀ x, D x ≤ tensorDivisor A K 1 f x)
    (h0O : ℕ) (riemann_roch : (h0O : ℤ) - (Module.finrank ℂ S : ℤ) = 1)
    (nonhyperelliptic : Prop) (eligible : Eligible signature nonhyperelliptic)
    (component : Component)
    (chen_moeller : Eligible signature nonhyperelliptic →
      h0O = match component with | .regular => 1 | .irregular => 2) :
    (ResidualCubic A K D P degree (genus signature) q ↔ 0 < Module.finrank ℂ S) ∧
    (0 < Module.finrank ℂ S ↔ 2 ≤ h0O) ∧
    (0 < Module.finrank ℂ S ↔ component = .irregular) ∧
    (Module.finrank ℂ S = 0 ↔ component = .regular) := by
  have hd : degree D = genus signature := signature_degree.trans (degree_equals_genus signature)
  exact ⟨(positive_iff_residual A K D P degree (genus signature) q hq hD hP
    hqdiv hd canonical_degree S section_definition).symm,
    riemann_roch_threshold h0O (Module.finrank ℂ S) riemann_roch,
    component_threshold signature nonhyperelliptic eligible component h0O
      (Module.finrank ℂ S) riemann_roch chen_moeller⟩

#print axioms positive_iff_residual
#print axioms theorem_5_3
end Problem32.PaperComponentCriterion
