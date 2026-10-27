import OddMath.SKM.ScalarChangeBubbleFamily
import OddMath.SKM.MixedCrossingLocalExamples

/-!
Brundan–Ellis (1.21)–(1.22) and Definition 2.3: full polynomial/exterior
bubble evaluation under a noninjective coefficient map on two odd colours.
No nonzero Hom class or universal basis is assumed.
-/

noncomputable section
namespace OddMath.SKM.ScalarChangeBubbleFamilyExamples
open CategoryTheory StringDiagrams Presentation ScalarChange MixedCrossingLocalExamples
open scoped TensorProduct

private def source : Scalars oddDatum (ZMod 9) where
  t _ _ := 1
  t_self _ := rfl
  t_symm_of_d_eq_zero _ _ _ := rfl
  s _ _ _ _ := 0
  s_symm _ _ _ _ := rfl
  s_eq_zero _ _ _ _ _ := rfl
  two_isUnit _ := (ZMod.isUnit_iff_coprime 2 9).2 (by decide)

private def bubble : CScalars source where
  c _ _ := -1
  shift _ _ _ := by simp [source]

private def specialize : ZMod 9 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 9) _

example : (3 : ZMod 9) ≠ 0 ∧ specialize (3 : ZMod 9) = 0 := by
  constructor <;> decide

example (i : {i : Bool // oddDatum.parity i = 1}) :
    symMap (D := oddDatum) specialize (SYM.delta oddDatum (ZMod 9) i) =
      SYM.delta oddDatum (ZMod 3) i := symMap_delta specialize i

example (μ : Bool → ℤ) (i : Bool) (n : ℤ) :
    homMap specialize oddDatum source _ _ (bubL bubble i μ n) =
      bubL (cScalars oddDatum specialize bubble) i μ n :=
  homMap_bubL specialize bubble i μ n

example (μ : Bool → ℤ) (i : Bool) (n : ℤ) :
    homMap specialize oddDatum source _ _ (bubR bubble i μ n) =
      bubR (cScalars oddDatum specialize bubble) i μ n :=
  homMap_bubR specialize bubble i μ n

example (μ : Bool → ℤ) (i : Bool) :
    homMap specialize oddDatum source _ _ (oddBubble bubble i μ) =
      oddBubble (cScalars oddDatum specialize bubble) i μ :=
  homMap_oddBubble specialize bubble i μ

example (μ : Bool → ℤ) (i : {i : Bool // oddDatum.parity i = 1})
    (j : Bool) (n : ℕ) :
    homMap specialize oddDatum source _ _
      (betaSYM bubble μ (SYM.delta oddDatum (ZMod 9) i *
        SYM.e oddDatum (ZMod 9) j n)) =
      betaSYM (cScalars oddDatum specialize bubble) μ
        (SYM.delta oddDatum (ZMod 3) i * SYM.e oddDatum (ZMod 3) j n) := by
  rw [homMap_betaSYM]
  simp

example (μ : Bool → ℤ) (p : SYM oddDatum (ZMod 9)) :
    letI := specialize.toAlgebra
    homBaseChange specialize oddDatum source (ob oddDatum μ []) (ob oddDatum μ [])
      ((2 : ZMod 3) ⊗ₜ[ZMod 9] betaSYM bubble μ p) =
      (2 : ZMod 3) • betaSYM (cScalars oddDatum specialize bubble) μ
        (symMap (D := oddDatum) specialize p) :=
  homBaseChange_betaSYM specialize bubble μ 2 p

#print axioms OddMath.SKM.ScalarChange.homBaseChange_betaSYM
#print axioms OddMath.SKM.ScalarChange.symMap
#print axioms OddMath.SKM.ScalarChange.symMap_delta
#print axioms OddMath.SKM.ScalarChange.homMap_bubL
#print axioms OddMath.SKM.ScalarChange.homMap_bubR
#print axioms OddMath.SKM.ScalarChange.homMap_oddBubble
#print axioms OddMath.SKM.ScalarChange.homMap_betaSYM

end OddMath.SKM.ScalarChangeBubbleFamilyExamples
