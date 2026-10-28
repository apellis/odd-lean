import OddMath.SKM.FiniteColourClassDetection
import OddMath.SKM.SerrePolynomialExamples

/-! The finite-colour detection theorem applied to concrete class relations
over a two-colour datum, restricted to one colour. -/
noncomputable section
namespace OddMath.SKM.FiniteColourClassDetectionExamples
open CategoryTheory StringDiagrams FiniteColour SerrePolynomialExamples

/-- The singleton colour set `{true}`. -/
abbrev J₀ : Finset Bool := {true}

/-- The colour `true` as an element of the restricted colour set. -/
def t₀ : J₀ := ⟨true, Finset.mem_singleton_self _⟩

/-- A relation between two literally different layer lists: a single dot
layer on the upward strand, written once as a cancelling pair. -/
def dotLayer : LayerData Bool := ([], .dot true, [])

def dotLayer₀ : LayerData J₀ := ([], .dot t₀, [])

theorem dotLayer_map : layerData J₀ dotLayer₀ = dotLayer := rfl

theorem dot_relation :
    ∑ m ∈ ({0, 1} : Finset ℕ), (if m = 0 then (1 : ℚ) else -1) •
      cl datum scalars 0 [(true, true)] [(true, true)] [dotLayer] = 0 := by
  simp

/-- The restricted relation holds for every finite colour set past the witness. -/
theorem dot_relation_restrict :
    ∃ J₁ : Finset Bool, ∀ J : Finset Bool, J₁ ⊆ J →
      ∀ (s' t' : List (Letter J)) (ls' : ℕ → List (LayerData J)),
        s'.map (letter J) = [(true, true)] → t'.map (letter J) = [(true, true)] →
        (∀ m ∈ ({0, 1} : Finset ℕ), (ls' m).map (layerData J) = [dotLayer]) →
        ∑ m ∈ ({0, 1} : Finset ℕ), (if m = 0 then (1 : ℚ) else -1) •
          cl (datum.restrictColours J) (scalars.restrictColours datum J) 0 s' t' (ls' m) = 0 :=
  sum_cl_eq_zero_restrict datum scalars 0 _ _ _ _ _ dot_relation

/-- A non-chaining layer list has zero class, detected in one colour. -/
theorem nonchain_relation :
    ∑ _m ∈ ({0} : Finset ℕ), (1 : ℚ) • cl datum scalars 0 [] [(true, true)] [] = 0 := by
  rw [Finset.sum_singleton, cl_of_not (by simp [SChain]), smul_zero]

example : ∃ J₁ : Finset Bool, ∀ J : Finset Bool, J₁ ⊆ J →
    ∀ (s' t' : List (Letter J)) (ls' : ℕ → List (LayerData J)),
      s'.map (letter J) = [] → t'.map (letter J) = [(true, true)] →
      (∀ m ∈ ({0} : Finset ℕ), (ls' m).map (layerData J) = []) →
      ∑ m ∈ ({0} : Finset ℕ), (1 : ℚ) •
        cl (datum.restrictColours J) (scalars.restrictColours datum J) 0 s' t' (ls' m) = 0 :=
  sum_cl_eq_zero_restrict datum scalars 0 _ _ _ _ _ nonchain_relation

/-- The restricted words and layers in the hypotheses exist for `J₀`. -/
example : ([(true, t₀)] : List (Letter J₀)).map (letter J₀) = [(true, true)] ∧
    [dotLayer₀].map (layerData J₀) = [dotLayer] := ⟨rfl, rfl⟩

#print axioms sum_cl_eq_zero_restrict
#print axioms linear_injective
#print axioms chain_of_map

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.FiniteColourClassDetection then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"

end OddMath.SKM.FiniteColourClassDetectionExamples
