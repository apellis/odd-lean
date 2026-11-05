/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.WhiskerReduction

/-! # Whiskered evaluation in the swapped layer representation, entry by entry

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5, in the
matrix form of `docs/Nondegeneracy/SwappedActionAssembly.md`: the whiskered evaluation
`u ⊗ X ⊗ v` of a linear combination of diagrams `X` in `ProbeReservoir.layerRep` is the
matrix product of the input family with the block-diagonal entries of `X`. The block at the
outer paths `pu`, `pv` is `F_{pu}` applied to the entry of `X` at the object `F_{pv} Z`
(`evalW_apply_whisker`). This is the evaluation used for closed diagrams placed beside the
strands of an upward word (`docs/Nondegeneracy/SwappedVacuumBubbles.md`, §5).
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u uB v w

variable {I X : Type u}
variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc) {Gs Ys : ∀ s, P.H s}

/-- **Entries of a whiskered evaluation.** The entry of `u ⊗ X ⊗ v` applied to a matrix `x`,
at the path `pu q pv`, is the sum over the middle paths `p` of the entry of `x` at `pu p pv`
followed by `F_{pu}` applied to the entry of `X` from `p` to `q` at `F_{pv} Z`. -/
theorem evalW_apply_whisker (gens : P.Generators) {a b : Obj (SKM.sig D)} (X : (a ⟶ b) →₀ k)
    (u : Obj (SKM.sig D)) (v : List (SKM.sig D).Colour) (hw : a.WhiskerOK u v)
    (x : P.Mod Gs Ys (a.whisker u v)) {s x' y t : Sector I}
    (ht : P.wt t = (b.whisker u v).endR) (hta : P.wt t = (a.whisker u v).endR)
    (pu : SPath u.word s x') (q : SPath b.word x' y) (pv : SPath v y t)
    [Fintype (SPath a.word x' y)] :
    ((P.layerRep Gs Ys gens).toLocal.evalW (a.whisker u v) (b.whisker u v) u v X x :
        P.Mod Gs Ys (b.whisker u v)) s ⟨t, ht⟩ ((pu.append q).append pv) =
      ∑ p : SPath a.word x' y, x s ⟨t, hta⟩ ((pu.append p).append pv) ≫
        eqToHom (P.pathFunctor_append_append_obj pu p pv (Ys t)) ≫
          (P.pathFunctor pu).map (compEval gens X p q ((P.pathFunctor pv).obj (Ys t))) ≫
            eqToHom (P.pathFunctor_append_append_obj pu q pv (Ys t)).symm := by
  classical
  rw [LocalInterpretation.evalW, Finsupp.linearCombination_apply]
  rw [Finsupp.sum, LinearMap.sum_apply, Mod.sum_apply]
  let _ : Fintype (SPath (a.whisker u v).word s t) := Fintype.ofFinite _
  let _ : Fintype (SPath.Dec u.word a.word v s t) := Fintype.ofFinite _
  have hterm : ∀ d : a ⟶ b,
      ((X d • ((P.layerRep Gs Ys gens).toLocal.res (b.whisker u v) ∘ₗ
        (P.layerRep Gs Ys gens).toLocal.opList ((Diagram.layers d).map (·.whisker u v)) ∘ₗ
        (P.layerRep Gs Ys gens).toLocal.ext (a.whisker u v))) x :
          P.Mod Gs Ys (b.whisker u v)) s ⟨t, ht⟩ ((pu.append q).append pv) =
      ∑ pp, x s ⟨t, hta⟩ pp ≫
        (X d • compList gens _ ((Diagram.chain d).whisker hw) pp
          ((pu.append q).append pv) (Ys t)) := by
    intro d
    rw [LinearMap.smul_apply, Mod.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      res_opList_ext_apply gens _ ((Diagram.chain d).whisker hw), Finset.smul_sum]
    simp only [Linear.comp_smul]
  erw [Finset.sum_congr rfl fun d _ => hterm d]
  rw [Finset.sum_comm]
  simp only [← Preadditive.comp_sum]
  refine (SPath.sum_cast_dec (l := u.word) (m := a.word) (r := v) (w := (a.whisker u v).word) rfl _).trans ?_
  refine (SPath.sum_dec_eq pu pv _ ?_).trans ?_
  rotate_left
  · refine Finset.sum_congr rfl fun p _ => ?_
    have := compEval_whisker gens u v X hw pu p q pv (Ys t)
    simp only [Finsupp.sum] at this
    simp only [SPath.cast_self]
    erw [this]
    rfl
  · rintro ⟨⟨x1, y1⟩, pu1, p1, pv1⟩ hd
    refine (congrArg _ (Finset.sum_eq_zero fun d _ => ?_)).trans Limits.comp_zero
    simp only [SPath.cast_self]
    erw [compList_whisker_eq_zero gens u v _ (Diagram.chain d) hw pu1 p1 pv1 pu q pv hd]
    simp

/-- **Entries of a whiskered diagram up to equalities of boundary objects.** The evaluation
of the whiskered layers of a diagram `d : a ⟶ b`, read on objects `A = u ⊗ a ⊗ v` and
`B = u ⊗ b ⊗ v` given only up to equality, is block diagonal with blocks `F_{pu}` of the
entries of `d`. -/
theorem res_opList_ext_whisker_apply (gens : P.Generators) {a b : Obj (SKM.sig D)}
    (d : a ⟶ b) (u : Obj (SKM.sig D)) (v : List (SKM.sig D).Colour) (hw : a.WhiskerOK u v)
    {A C : Obj (SKM.sig D)} (eA : a.whisker u v = A) (eC : b.whisker u v = C)
    (x : P.Mod Gs Ys A) {s x' y t : Sector I}
    (ht : P.wt t = C.endR) (hta : P.wt t = A.endR)
    (pu : SPath u.word s x') (q : SPath b.word x' y) (pv : SPath v y t)
    [Fintype (SPath a.word x' y)] :
    ((P.layerRep Gs Ys gens).toLocal.res C
        ((P.layerRep Gs Ys gens).toLocal.opList ((Diagram.layers d).map (·.whisker u v))
          ((P.layerRep Gs Ys gens).toLocal.ext A x)) : P.Mod Gs Ys C) s ⟨t, ht⟩
        (((pu.append q).append pv).cast (congrArg Obj.word eC)) =
      ∑ p : SPath a.word x' y,
        x s ⟨t, hta⟩ (((pu.append p).append pv).cast (congrArg Obj.word eA)) ≫
          eqToHom (by rw [P.pathFunctor_cast]; exact P.pathFunctor_append_append_obj pu p pv (Ys t)) ≫
            (P.pathFunctor pu).map (compDiag gens d p q ((P.pathFunctor pv).obj (Ys t))) ≫
              eqToHom (by
                rw [P.pathFunctor_cast]; exact (P.pathFunctor_append_append_obj pu q pv (Ys t)).symm) := by
  subst eA eC
  have h := evalW_apply_whisker P gens (Finsupp.single d (1 : k)) u v hw x ht hta pu q pv
  erw [LocalInterpretation.evalW_single, one_smul] at h
  simp only [SPath.cast_rfl]
  erw [h]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [compEval, Finsupp.sum_single_index, zero_smul, one_smul]

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
