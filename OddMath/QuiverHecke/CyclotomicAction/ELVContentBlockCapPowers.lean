import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareSourceDots
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixCaps

/-! # Dotted caps through the chosen canonical content source chart

Brundan–Ellis (1.13)–(1.14): every ordinary dot/counit row is compared
through the same selected source chart and input inclusion unit.
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
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hGlobalDot" => truncatedDot_supernatural D Sc cutoff N i

/-- Every ordinary dot/counit row uses the given selected source chart. -/
theorem contentBlockCapDot_square (M : ContentModules D Sc cutoff N γ)
    (t : ContentCategory D Sc cutoff N γ) (n : ℕ)
    (x : Obj J ((restriction J).obj M).toFunctor t) :
    unit Q₁ M.toFunctor t (capDotLinear J hDot M n t x) =
      capDotLinear T hGlobalDot (induced Q₁ M) n t.obj
        (fullSquareOrdinarySourceLinear J Q₁ Q₀ T sqJ ((restriction J).obj M) T (induced Q₁ M)
          (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M) t x) := by
  exact fullSquareSourceLinear_capDot_unit J Q₁ Q₀ T sqJ M hDot hGlobalDot
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
    (contentBlockDistinctRestriction_unit D Sc cutoff N β i M) t (by
      intro s g
      rw [Functor.map_comp, map_twist]
      dsimp only [contentAppendTo, contentInclusion, contentAppendToComponent,
        Functor.comp_obj, Functor.comp_map]
      simp only [eqToHom_refl, Category.id_comp]) n x

end OddMath.QuiverHecke.ELVOld
