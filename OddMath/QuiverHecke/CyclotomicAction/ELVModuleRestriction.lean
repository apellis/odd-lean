/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppendTransform
import StringDiagrams.Super.SVec

/-! # Restriction on ELV supermodules

The all-supermodule target is the superfunctor category from the truncated
ELV category to `SVec k`. Restriction along right append and evaluation of
its homogeneous transformations are constructed, including naturality
against odd module maps. This supplies the restriction side of
`DeformedActionAssembly.md` §5. Induction, its adjunction, integer grading,
and the normalized factor action remain separate constructions.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Parity-graded modules on the coefficient-truncated ELV category. -/
abbrev TruncatedModules :=
  Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec.{u} k)

/-- Restriction along right append, on all supernatural module maps. -/
def moduleRestriction (σ : List I) :
    TruncatedModules D Sc cutoff N ⥤ TruncatedModules D Sc cutoff N where
  obj M := (⟨truncatedAppend D Sc cutoff N σ⟩ :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (TruncatedCategory D Sc cutoff N)).comp M
  map f := Superfunctor.whiskerLeft ⟨truncatedAppend D Sc cutoff N σ⟩ f
  map_id M := Superfunctor.whiskerLeft_id _ M
  map_comp f g := Superfunctor.whiskerLeft_comp _ f g

instance moduleRestriction_additive (σ : List I) :
    (moduleRestriction D Sc cutoff N σ).Additive where
  map_add := Superfunctor.whiskerLeft_add _ _ _

instance moduleRestriction_linear (σ : List I) :
    (moduleRestriction D Sc cutoff N σ).Linear k where
  map_smul f c := Superfunctor.whiskerLeft_smul _ c f

instance moduleRestriction_super (σ : List I) :
    IsSuperfunctor k (moduleRestriction D Sc cutoff N σ) where
  map_mem := Superfunctor.whiskerLeft_mem _

/-- A homogeneous appended morphism acts on every module by evaluation. -/
def moduleRestrictionComponent {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) (M : TruncatedModules D Sc cutoff N) :
    (moduleRestriction D Sc cutoff N σ).obj M ⟶
      (moduleRestriction D Sc cutoff N τ).obj M :=
  Superfunctor.whiskerRight
    (Superfunctor.homMk (truncatedAppendTransform D Sc cutoff N hh)) M

theorem moduleRestrictionComponent_mem {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) (M : TruncatedModules D Sc cutoff N) :
    moduleRestrictionComponent D Sc cutoff N hh M ∈ parity (R := k) _ _ p := by
  exact Superfunctor.whiskerRight_mem
    (F := ⟨truncatedAppend D Sc cutoff N σ⟩)
    (H := ⟨truncatedAppend D Sc cutoff N τ⟩)
    (Superfunctor.IsSupernatural.toSuperNatTrans_mem
      (F := ⟨truncatedAppend D Sc cutoff N σ⟩)
      (G := ⟨truncatedAppend D Sc cutoff N τ⟩)
      (truncatedAppendComponent_supernatural D Sc cutoff N hh)) M

theorem moduleRestrictionComponent_supernatural {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) :
    IsSupernatural k p (moduleRestrictionComponent D Sc cutoff N hh) where
  mem := moduleRestrictionComponent_mem D Sc cutoff N hh
  naturality := by
    intro M L q f hf
    have ht := Superfunctor.IsSupernatural.toSuperNatTrans_mem
      (F := ⟨truncatedAppend D Sc cutoff N σ⟩)
      (G := ⟨truncatedAppend D Sc cutoff N τ⟩)
      (truncatedAppendComponent_supernatural D Sc cutoff N hh)
    have he := Superfunctor.whisker_exchange ht hf
    have he' := congrArg (fun z => koszulSign p q • z) he
    rw [koszulSign_smul_smul] at he'
    simpa only [koszulSign_smul (R := k), moduleRestriction,
      moduleRestrictionComponent, truncatedAppendTransform] using he'.symm

/-- The transformation on restriction, including its exterior-coefficient signs. -/
def moduleRestrictionTransform {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) :
    SuperNatTrans k (moduleRestriction D Sc cutoff N σ)
      (moduleRestriction D Sc cutoff N τ) :=
  (moduleRestrictionComponent_supernatural D Sc cutoff N hh).toSuperNatTrans

/-- Evaluation of the homogeneous restriction transformation is the specified
quotient morphism, not a chosen module endomorphism. -/
@[simp] theorem moduleRestrictionTransform_app {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) (M : TruncatedModules D Sc cutoff N)
    (v : TruncatedCategory D Sc cutoff N) :
    ((moduleRestrictionTransform D Sc cutoff N hh).app p M).app p v =
      M.map (truncatedAppendComponent D Sc cutoff N h v) := by
  simp only [moduleRestrictionTransform, IsSupernatural.toSuperNatTrans,
    ↓reduceIte, moduleRestrictionComponent, Superfunctor.whiskerRight_app,
    Superfunctor.homMk, truncatedAppendTransform]

/-- The appended dot acting on restriction. No induction normalization is asserted. -/
def moduleRestrictionDot (i : I) :
    SuperNatTrans k (moduleRestriction D Sc cutoff N [i])
      (moduleRestriction D Sc cutoff N [i]) :=
  moduleRestrictionTransform D Sc cutoff N (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The raw appended crossing acting on restriction, with its specified colour order. -/
def moduleRestrictionCross (i j : I) :
    SuperNatTrans k (moduleRestriction D Sc cutoff N [i, j])
      (moduleRestriction D Sc cutoff N [j, i]) :=
  moduleRestrictionTransform D Sc cutoff N (crossTwo_mem D Sc i j)

/-- Evaluation transfers equality of quotient composites to every module. -/
theorem module_map_relation (M : TruncatedModules D Sc cutoff N)
    {v w z : TruncatedCategory D Sc cutoff N} (a : v ⟶ w) (b : w ⟶ z)
    (c : v ⟶ z) (h : a ≫ b = c) : M.map a ≫ M.map b = M.map c := by
  rw [← M.toFunctor.map_comp, h]

end OddMath.QuiverHecke.ELVOld
