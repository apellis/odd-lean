import OddMath.SKM.WeakMateChoice
import OddMath.SKM.TopMatchingChoice

/-! Complete cup/cap inverse-mate choices, with both boundary words nonempty. -/
noncomputable section
namespace NonVacuity.WeakMateChoice
open StringDiagrams StringDiagrams.Chord OddMath.SKM
private def colour : Fin 2 → Unit := fun _ => ()
private def u : Letter Unit := (true, ())
private def U₀ : MatchingBasisChoice (List.ofFn fun r => (true, colour r))
    (List.ofFn fun r => (true, colour r)) := Classical.choice (MatchingBasisChoice.nonempty _ _)
private def U : MatchingBasisChoice (ups [()] ++ [u]) ([u] ++ [u]) := U₀.atTop colour colour
private def F : MatchingBasisChoice ([u] ++ dualW [u]) (dns [()] ++ [u]) :=
  Classical.choice (MatchingBasisChoice.nonempty _ _)
private theorem bounded (R : U.members) (j : ℕ) : (U.points R j).1 ≤ R.val.length := le_rfl
private def W := WeakMate.weakChoice U F (fun R j _ => bounded R j)

theorem all_target_classes_covered : Function.Surjective (WeakMate.target U F) :=
  WeakMate.target_surjective U F

theorem literal_weak_matching (R : F.members) :
    IsMatching₂ ([u] ++ dualW [u]) (dns [()] ++ [u]) (W.representative R) ∧
      Reduced₂ ([u] ++ dualW [u]) (W.representative R) := ⟨W.matching R, W.reduced R⟩

theorem all_upstairs_decorations (t : U.Labels) :
    ∃ s, WeakMate.sourceLabelsEquiv U F (fun R j _ => bounded R j) s = t :=
  (WeakMate.sourceLabelsEquiv U F (fun R j _ => bounded R j)).surjective t

theorem literal_serializer (t : F.Labels) :
    W.layers t = dLay ([u] ++ dualW [u]) (WeakMate.moves [()] [u] [u]
      (U.serialize (WeakMate.sourceLabelsEquiv U F (fun R j _ => bounded R j) t).1
        (WeakMate.sourceLabelsEquiv U F (fun R j _ => bounded R j) t).2)) :=
  WeakMate.weakChoice_layers U F (fun R j _ => bounded R j) t

#print axioms all_target_classes_covered
#print axioms literal_weak_matching
#print axioms all_upstairs_decorations
#print axioms literal_serializer
end NonVacuity.WeakMateChoice
