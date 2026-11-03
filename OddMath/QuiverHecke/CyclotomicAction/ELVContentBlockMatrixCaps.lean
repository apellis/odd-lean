import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareCounit
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixRows

/-! # Ordinary cap fields through canonical content source charts

Brundan–Ellis (1.13)–(1.14): the selected source comparison transports
the specified ordinary counit. Both the inclusion unit and its whole
coefficient action are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqJ" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hJ

/-- The whole selected ordinary source chart commutes with the prescribed counit. -/
theorem contentBlockCounit_square (M : ContentModules D Sc cutoff N γ)
    (t : ContentCategory D Sc cutoff N γ)
    (x : Obj J ((restriction J).obj M).toFunctor t) :
    unit Q₁ M.toFunctor t (restrictionCounitLinear J M t x) =
      counit T (induced Q₁ M).toFunctor t.obj
        (fullSquareOrdinarySourceLinear J Q₁ Q₀ T sqJ ((restriction J).obj M) T (induced Q₁ M)
          (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M) t x) := by
  exact fullSquareOrdinarySourceLinear_counit_unit J Q₁ Q₀ T sqJ M
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
    (contentBlockDistinctRestriction_unit D Sc cutoff N β i M) t x

end OddMath.QuiverHecke.ELVOld
