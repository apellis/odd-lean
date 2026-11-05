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
private theorem unitDot_value
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (R : Superfunctor k C (SVec k)) (n : ℕ) (t : C) (b : R.obj t) :
    (unitDotColumn J hα R n).total t b = unitDotLinear J hα R n t b :=
  LinearMap.congr_fun (unitDotColumn_total J hα R n t) b

private theorem unitDot_compare
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    {p q : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {δ : ∀ s, T.obj s ⟶ T.obj s} (hδ : IsSupernatural k q δ)
    (R : Superfunctor k C (SVec k)) (P : Superfunctor k B (SVec k))
    (n : ℕ) (s : C) (t : B)
    (c : Obj J R.toFunctor (J.obj s) → Obj T P.toFunctor (T.obj t))
    (a : R.obj s → P.obj t)
    (h : ∀ b, c (unitDotLinear J hα R n s b) = unitDotLinear T hδ P n t (a b))
    (b : R.obj s) :
    c ((unitDotColumn J hα R n).total s b) = (unitDotColumn T hδ P n).total t (a b) := by
  have hL := congrArg c (unitDot_value J hα R n s b)
  have hR := unitDot_value T hδ P n t (a b)
  exact hL.trans ((h b).trans hR.symm)

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

/-- The same square uses the literal total components of the specified module columns. -/
theorem contentBlockUnitDotColumn_square (M : ContentModules D Sc cutoff N β)
    (t : ContentCategory D Sc cutoff N β) (n : ℕ) (b : M.obj t) :
    fullSquareTargetLinear K Q₁ Q₀ T sqK M ((K).obj t) ((T).obj t.obj)
      (congrArg (fun F => F.obj t) sqK) ((unitDotColumn K hDot M n).total t b) =
      (unitDotColumn T hGlobalDot (induced Q₀ M) n).total t.obj (unit Q₀ M.toFunctor t b) := by
  exact unitDot_compare K T hDot hGlobalDot M (induced Q₀ M) n t t.obj
    (fullSquareTargetLinear K Q₁ Q₀ T sqK M ((K).obj t) ((T).obj t.obj)
      (congrArg (fun F => F.obj t) sqK))
    (fun x => unit Q₀ M.toFunctor t x)
    (fun x => contentBlockUnitDot_square D Sc cutoff N β i M t n x) b

end OddMath.QuiverHecke.ELVOld
