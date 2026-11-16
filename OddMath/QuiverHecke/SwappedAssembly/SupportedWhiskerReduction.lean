import OddMath.QuiverHecke.SwappedAssembly.WhiskerReduction

/-! # Relations on path-closed families of Hom inputs

Brundan–Ellis Definition 1.5 and `SwappedActionAssembly.md` F4/(A1):
whiskered relation evaluation needs the unwhiskered equation only on
objects reached from the chosen rightmost input along a summand path.
A path-closed object property therefore suffices; no equation on the
remaining raw Hom objects is assumed.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc} {Gs Ys : ∀ s, P.H s}

/-- Unwhiskered equations on a path-closed family suffice for every valid context. -/
theorem evalW_eq_zero_of_compEval_wt_on
    (Q : ∀ t, ObjectProperty (P.H t))
    (hpath : ∀ {w : List (Col I X)} {s t : Sector I} (p : SPath w s t) (Z : P.H t),
      Q t Z → Q s ((P.pathFunctor p).obj Z))
    (hYs : ∀ t, Q t (Ys t)) (gens : P.Generators) {a b : Obj (SKM.sig D)}
    (X : (a ⟶ b) →₀ k)
    (hX : ∀ {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t),
      Q t Z → P.wt t = a.endR → compEval gens X p q Z = 0)
    (u : Obj (SKM.sig D)) (v : List (SKM.sig D).Colour) (hw : a.WhiskerOK u v) :
    (P.layerRep Gs Ys gens).toLocal.evalW (a.whisker u v) (b.whisker u v) u v X = 0 := by
  classical
  ext x : 1
  funext s t Q
  rw [LocalInterpretation.evalW, Finsupp.linearCombination_apply]
  simp only [LinearMap.zero_apply]
  rw [Finsupp.sum, LinearMap.sum_apply, Mod.sum_apply, Mod.zero_apply]
  let _ : Fintype (SPath (a.whisker u v).word s t.1) := Fintype.ofFinite _
  rcases X.support.eq_empty_or_nonempty with hX0 | ⟨d0, -⟩
  · rw [hX0, Finset.sum_empty]
  have hend : P.wt t.1 = (a.whisker u v).endR := t.2.trans ((Diagram.chain d0).whisker hw).endR_eq
  have hterm : ∀ d : a ⟶ b,
      ((X d • ((P.layerRep Gs Ys gens).toLocal.res (b.whisker u v) ∘ₗ
        (P.layerRep Gs Ys gens).toLocal.opList ((Diagram.layers d).map (·.whisker u v)) ∘ₗ
        (P.layerRep Gs Ys gens).toLocal.ext (a.whisker u v))) x :
          P.Mod Gs Ys (b.whisker u v)) s t Q =
      ∑ pp, x s ⟨t.1, hend⟩ pp ≫
        (X d • compList gens _ ((Diagram.chain d).whisker hw) pp Q (Ys t.1)) := by
    intro d
    rw [LinearMap.smul_apply, Mod.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      res_opList_ext_apply gens _ ((Diagram.chain d).whisker hw), Finset.smul_sum]
    simp only [Linear.comp_smul]
  erw [Finset.sum_congr rfl fun d _ => hterm d]
  refine (Finset.sum_comm).trans (Finset.sum_eq_zero fun pp _ => ?_)
  rw [← Preadditive.comp_sum]
  obtain ⟨⟨⟨x1, y1⟩, pu, p, pv⟩, rfl⟩ :
      ∃ d : SPath.Dec u.word a.word v s t.1, d.path = pp := ⟨_, SPath.path_decOf _ _ pp⟩
  obtain ⟨⟨⟨x2, y2⟩, pu', q, pv'⟩, rfl⟩ :
      ∃ e : SPath.Dec u.word b.word v s t.1, e.path = Q := ⟨_, SPath.path_decOf _ _ Q⟩
  by_cases hout : ((⟨x1, pu⟩ : Σ z, SPath u.word s z), (⟨y1, pv⟩ : Σ z, SPath v z t.1)) =
      (⟨x2, pu'⟩, ⟨y2, pv'⟩)
  · simp only [Prod.mk.injEq, Sigma.mk.injEq] at hout
    obtain ⟨⟨rfl, h1⟩, ⟨rfl, h2⟩⟩ := hout
    cases h1; cases h2
    have hy : P.wt y1 = a.endR := by
      refine P.wt_eq_of_ok pv a.endR hw.2.2 (hend.trans ?_)
      rw [Obj.endR, Obj.whisker_start, Obj.whisker_word, Signature.endR_append,
        Signature.endR_append]
      exact congrArg (fun r => (SKM.sig D).endR ((SKM.sig D).endR r a.word) v) hw.2.1
    have := compEval_whisker gens u v X hw pu p q pv (Ys t.1)
    simp only [Finsupp.sum] at this
    erw [this, hX p q _ (hpath pv _ (hYs _)) hy]
    simp
  · refine (congrArg _ (Finset.sum_eq_zero fun d _ => ?_)).trans (Limits.comp_zero)
    erw [compList_whisker_eq_zero gens u v _ (Diagram.chain d) hw pu p pv pu' q pv' hout]
    simp

/-- A defining relation need only hold at the retained, weight-matched inputs. -/
theorem relHolds_of_compEval_wt_on
    (Q : ∀ t, ObjectProperty (P.H t))
    (hpath : ∀ {w : List (Col I X)} {s t : Sector I} (p : SPath w s t) (Z : P.H t),
      Q t Z → Q s ((P.pathFunctor p).obj Z))
    (hYs : ∀ t, Q t (Ys t)) (gens : P.Generators) (r : SKM.Rel D)
    (h : ∀ {s t : Sector I} (p : SPath ((SKM.pres D Sc).dom r).word s t)
      (q : SPath ((SKM.pres D Sc).cod r).word s t) (Z : P.H t), Q t Z →
      P.wt t = ((SKM.pres D Sc).dom r).endR →
      compEval gens ((SKM.pres D Sc).rel r) p q Z = 0) :
    RelHolds Sc (P.layerRep Gs Ys gens) r := fun u v hw =>
  evalW_eq_zero_of_compEval_wt_on Q hpath hYs gens _ h u v hw

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
