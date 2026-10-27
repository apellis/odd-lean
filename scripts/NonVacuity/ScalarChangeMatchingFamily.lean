import OddMath.SKM.ScalarChangeMatchingFamily
import OddMath.SKM.CupCompletedChoiceExamples
import OddMath.SKM.MixedCrossingLocalExamples

/-!
Brundan–Ellis §8 and (1.21)–(1.22): a complete cup-adapted decorated
matching choice with positive dots and a genuine odd bubble coefficient under
noninjective specialization. Also check both oriented normalized bends.
-/
noncomputable section
namespace OddMath.SKM.ScalarChangeMatchingFamilyExamples
open OddMath.SKM CategoryTheory StringDiagrams StringDiagrams.Chord ScalarChange
open MixedCrossingLocalExamples
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
private abbrev P : List (Letter Bool) := [up false]
private abbrev Q : List (Letter Bool) := [dn true]
private abbrev a : List (Letter Bool) := P ++ Q
private abbrev b : List (Letter Bool) := P ++ up false :: dn false :: Q

/-- This index belongs to a complete choice whose literal middle cup carries
two dots; the full exterior coefficient remains attached on specialization. -/
example (μ : Bool → ℤ) :
    ∃ (G : MatchingBasisChoice a a) (F : MatchingBasisChoice a b)
      (p : ℕ × G.Labels ↪ F.Labels),
      ∀ (j : G.members) (n : MatchingStrand a j.val → ℕ),
        F.layers (p (2, ⟨j, n⟩)) =
          (PointedMatching.ofStrict (G.matching j j.property).1
            (G.matching j j.property).2).layers n ++
          (xCupL (up false)).map (xwhL P Q) ++
          dLay b (List.replicate 2 (.dt P.length)) ∧
        homMap specialize oddDatum source _ _
          (F.expansion bubble μ (Finsupp.single (p (2, ⟨j, n⟩))
            (SYM.delta oddDatum (ZMod 9) ⟨false, rfl⟩ *
             SYM.e oddDatum (ZMod 9) true 1))) =
          F.expansion (cScalars oddDatum specialize bubble) μ
            (Finsupp.single (p (2, ⟨j, n⟩))
              (SYM.delta oddDatum (ZMod 3) ⟨false, rfl⟩ *
               SYM.e oddDatum (ZMod 3) true 1)) := by
  obtain ⟨G, F, p, h⟩ := CupCompletedChoiceExamples.complete_paired_sector true
  refine ⟨G, F, p, fun j n => ⟨h 2 j n, ?_⟩⟩
  rw [homMap_expansion_single]
  simp

/-- The cup-and-two-dots label actually exists; it is not merely an
implication from a possibly empty set of matching labels. -/
example : ∃ (G : MatchingBasisChoice a a) (F : MatchingBasisChoice a b)
    (p : ℕ × G.Labels ↪ F.Labels) (j : G.members),
    F.layers (p (2, ⟨j, fun _ => 0⟩)) =
      (PointedMatching.ofStrict (G.matching j j.property).1
        (G.matching j j.property).2).layers (fun _ => 0) ++
      (xCupL (up false)).map (xwhL P Q) ++
      dLay b (List.replicate 2 (.dt P.length)) := by
  obtain ⟨G, F, p, h⟩ := CupCompletedChoiceExamples.complete_paired_sector true
  have hm : IsMatching₂ a a [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ a [] := by
    exact ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  obtain ⟨R, hR, _⟩ := G.complete [] hm hr
  exact ⟨G, F, p, ⟨R, hR⟩, h 2 ⟨R, hR⟩ (fun _ => 0)⟩

/-- The same oriented decorated generator goes through the tensor comparison. -/
example (F : MatchingBasisChoice a b) (μ : Bool → ℤ) (t : F.Labels) :
    letI := specialize.toAlgebra
    homBaseChange specialize oddDatum source (ob oddDatum μ a) (ob oddDatum μ b)
      ((2 : ZMod 3) ⊗ₜ[ZMod 9] F.expansion bubble μ
        (Finsupp.single t (SYM.delta oddDatum (ZMod 9) ⟨false, rfl⟩))) =
      (2 : ZMod 3) • F.expansion (cScalars oddDatum specialize bubble) μ
        (Finsupp.single t (SYM.delta oddDatum (ZMod 3) ⟨false, rfl⟩)) := by
  rw [homBaseChange_expansion_single]
  simp

/-- A normalized left cup followed by an odd dot and a cap, plus the
opposite left-cap orientation as an actual placed layer. -/
example (μ : Bool → ℤ) :
    homMap specialize oddDatum source _ _
      (xev bubble μ [] []
        [([], .lcup false, []), ([], .gen (.dot false), [dn false]),
         ([], .gen (.cap false), [])]) =
    xev (cScalars oddDatum specialize bubble) μ [] []
        [([], .lcup false, []), ([], .gen (.dot false), [dn false]),
         ([], .gen (.cap false), [])] :=
  homMap_xev specialize bubble μ [] [] _

example (μ : Bool → ℤ) :
    homMap specialize oddDatum source _ _
      (xlay bubble μ ([], .lcap false, [])) =
      xlay (cScalars oddDatum specialize bubble) μ ([], .lcap false, []) :=
  homMap_xlay specialize bubble μ _

#print axioms OddMath.SKM.ScalarChange.homMap_plcL
#print axioms OddMath.SKM.ScalarChange.homMap_bubAt
#print axioms OddMath.SKM.ScalarChange.homMap_xlay
#print axioms OddMath.SKM.ScalarChange.homMap_xev
#print axioms OddMath.SKM.ScalarChange.homMap_expansion_single
#print axioms OddMath.SKM.ScalarChange.homMap_expansion
#print axioms OddMath.SKM.ScalarChange.homBaseChange_expansion_single

end OddMath.SKM.ScalarChangeMatchingFamilyExamples
