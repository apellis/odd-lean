import OddMath.SKM.ContextualBoundaryInduction
import OddMath.SKM.Nondegeneracy

/-! Assembly of contextual exchange descent and sorted independence.
The local exchange statements are explicit hypotheses; this module does not
assert that their diagrammatic coefficient comparisons are already constructed. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- Independence at a fixed global external weight, for every choice, on
exactly the equal-weight boundaries appearing in the conjecture. -/
def BoundaryIndependence (cs : CScalars Sc) (μ : X) (a b : List (Letter I)) : Prop :=
  wt D 0 a = wt D 0 b → ∀ F : MatchingBasisChoice a b, Function.Injective (F.expansion cs μ)

/-- The local source exchange needed by the global induction. Every term uses
the same global `μ`; only equal-color deletions require residual independence. -/
def SourceExchangeDescent (cs : CScalars Sc) : Prop :=
  ∀ μ L Q i j b,
    BoundaryIndependence cs μ (L ++ up j :: dn i :: Q) b →
    (i = j → BoundaryIndependence cs μ (L ++ Q) b) →
    BoundaryIndependence cs μ (L ++ dn i :: up j :: Q) b

/-- The corresponding target exchange, retaining arbitrary contexts. -/
def TargetExchangeDescent (cs : CScalars Sc) : Prop :=
  ∀ μ a L Q i j,
    BoundaryIndependence cs μ a (L ++ dn j :: up i :: Q) →
    (i = j → BoundaryIndependence cs μ a (L ++ Q)) →
    BoundaryIndependence cs μ a (L ++ up i :: dn j :: Q)

/-- Sorting opposite directions preserves weight for arbitrary colors. -/
theorem wt_context_opposite_swap (μ : X) (L Q : List (Letter I)) (i j : I) :
    wt D μ (L ++ dn i :: up j :: Q) = wt D μ (L ++ up j :: dn i :: Q) := by
  rw [wt_append, wt_append]
  congr 1
  simp only [wt_cons]
  abel

/-- The residual deletion is weight preserving precisely in the equal-color
case used by contextual descent. No distinct-color cancellation is assumed. -/
theorem wt_context_pair_delete (μ : X) (L Q : List (Letter I)) (i : I) :
    wt D μ (L ++ dn i :: up i :: Q) = wt D μ (L ++ Q) := by
  simp [wt_append, wt_cons, sh, dn, up]

/-- Actual nondegeneracy follows from sorted independence and the two local
exchange comparisons. No homogeneous-coefficient or action premise is used. -/
theorem nondegeneracy_of_contextual_descent (cs : CScalars Sc)
    (hsorted : ∀ μ l r u v,
      BoundaryIndependence cs μ (ups u ++ dns r) (dns l ++ ups v))
    (hsource : SourceExchangeDescent cs) (htarget : TargetExchangeDescent cs) :
    NondegeneracyConjecture cs := by
  apply (nondegeneracyConjecture_iff_injective cs).mpr
  intro a b hab μ F
  have H := ContextualBoundary.boundary_induction (BoundaryIndependence cs μ)
    (fun u d e v => by
      simpa only [ContextualBoundary.signed, ups, dns, List.map_reverse, List.reverse_reverse] using
        hsorted μ e.reverse d.reverse u v)
    (hsource μ) (htarget μ)
  exact H a b hab F

end OddMath.SKM
