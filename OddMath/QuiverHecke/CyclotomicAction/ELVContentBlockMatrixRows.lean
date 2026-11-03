import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareRows
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixMate

/-! # Dotted matrix fields through canonical content charts

Brundan–Ellis (1.13)–(1.14): compare the prescribed ordinary unit/dot
columns with the selected full-inclusion charts,
retaining arbitrary input vectors and every dot power.
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
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqK" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hK

/-- The canonical content unit/dot column uses the specified affine dot. -/
theorem contentBlockMatrixDot_supernatural : IsSupernatural k (D.parity i)
    (contentAppendToComponent D Sc cutoff N hK hK (dotE D Sc [i] 0)) :=
  contentAppendTo_supernatural D Sc cutoff N hK hK (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hGlobalDot" => truncatedDot_supernatural D Sc cutoff N i

/-- Every ordinary unit/dot column commutes with the selected target chart. -/
theorem contentBlockUnitDot_square (M : ContentModules D Sc cutoff N β)
    (t : ContentCategory D Sc cutoff N β) (n : ℕ) (b : M.obj t) :
    fullSquareTargetLinear K Q₁ Q₀ T sqK M ((K).obj t) ((T).obj t.obj)
      (congrArg (fun F => F.obj t) sqK) (unitDotLinear K hDot M n t b) =
      unitDotLinear T hGlobalDot (induced Q₀ M) n t.obj (unit Q₀ M.toFunctor t b) := by
  exact fullSquareTargetLinear_unitDot K Q₁ Q₀ T sqK M hDot hGlobalDot t n b (by
    intro s g
    rw [Functor.map_comp, map_twist]
    dsimp only [contentAppendTo, contentInclusion, contentAppendToComponent,
      Functor.comp_obj, Functor.comp_map]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id])

end OddMath.QuiverHecke.ELVOld
