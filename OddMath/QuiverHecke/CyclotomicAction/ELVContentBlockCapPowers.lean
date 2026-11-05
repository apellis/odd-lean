import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareSourceDots
import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareCounit
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixRows

/-! # Dotted caps through the chosen canonical content source chart

Brundan–Ellis (1.13)–(1.14): every ordinary dot/counit row is compared
through the same selected source chart and input inclusion unit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
private theorem capDot_value
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k A (SVec k)) (n : ℕ) (w : A)
    (x : Obj J ((restriction J).obj M).toFunctor w) :
    (capDotRow J hα M n).total w x = capDotLinear J hα M n w x :=
  LinearMap.congr_fun (capDotRow_total J hα M n w) x

private theorem capDot_compare
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    {p q : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {δ : ∀ s, T.obj s ⟶ T.obj s} (hδ : IsSupernatural k q δ)
    (M : Superfunctor k A (SVec k)) (P : Superfunctor k E (SVec k)) (n : ℕ) (w : A) (z : E)
    (a : M.obj w → P.obj z)
    (c : Obj J ((restriction J).obj M).toFunctor w → Obj T ((restriction T).obj P).toFunctor z)
    (h : ∀ x, a (capDotLinear J hα M n w x) = capDotLinear T hδ P n z (c x))
    (x : Obj J ((restriction J).obj M).toFunctor w) :
    a ((capDotRow J hα M n).total w x) = (capDotRow T hδ P n).total z (c x) := by
  have hL := congrArg a (capDot_value J hα M n w x)
  have hR := capDot_value T hδ P n z (c x)
  exact hL.trans ((h x).trans hR.symm)

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

/-- The square retains the literal totals of the specified module cap rows. -/
theorem contentBlockCapDotRow_square (M : ContentModules D Sc cutoff N γ)
    (t : ContentCategory D Sc cutoff N γ) (n : ℕ)
    (x : Obj J ((restriction J).obj M).toFunctor t) :
    unit Q₁ M.toFunctor t ((capDotRow J hDot M n).total t x) =
      (capDotRow T hGlobalDot (induced Q₁ M) n).total t.obj
        (fullSquareOrdinarySourceLinear J Q₁ Q₀ T sqJ ((restriction J).obj M) T (induced Q₁ M)
          (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M) t x) := by
  exact capDot_compare J T hDot hGlobalDot M (induced Q₁ M) n t t.obj
    (fun b => unit Q₁ M.toFunctor t b)
    (fullSquareOrdinarySourceLinear J Q₁ Q₀ T sqJ ((restriction J).obj M) T (induced Q₁ M)
      (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M) t)
    (fun y => contentBlockCapDot_square D Sc cutoff N β i M t n y) x

end OddMath.QuiverHecke.ELVOld
