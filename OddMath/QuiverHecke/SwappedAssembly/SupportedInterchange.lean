import OddMath.QuiverHecke.SwappedAssembly.SupportedRelationLifting
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Generators

/-! # Interchange from supernaturality on retained inputs

The super interchange law in `SwappedActionAssembly.md` §3 only uses
the generator naturality equations at path images of the given source
objects. Thus a full input subcategory preserved by every native path
suffices; no naturality on unrelated raw Hom objects is asserted.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
universe u uB vB wB

section Exchange
variable {k : Type*} [CommRing k]

/-- The exchange calculation uses naturality on a full input subcategory,
provided its two intermediate objects lie in that subcategory. -/
theorem eqToHom_map_comp_exchange_on {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Preadditive C₀] [Linear k C₀] [Preadditive C₁] [Linear k C₁] [Supercategory k C₁]
    [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
    [Preadditive C₃] [Linear k C₃] [Supercategory k C₃]
    (Fu : C₁ ⥤ C₀) (Fa Fa' : C₂ ⥤ C₁) (Fm : C₃ ⥤ C₂) (Fb Fb' : C₄ ⥤ C₃) (Z : C₄)
    {γ : ∀ W, Fa.obj W ⟶ Fa'.obj W} {η : Fb.obj Z ⟶ Fb'.obj Z} {p q : ZMod 2}
    {S : ObjectProperty C₂}
    (hγ : IsSupernatural k p (F := S.ι ⋙ Fa) (G := S.ι ⋙ Fa') (fun W => γ W.obj))
    (hη : η ∈ parity (R := k) _ _ q)
    (hS₁ : S (Fm.obj (Fb.obj Z))) (hS₂ : S (Fm.obj (Fb'.obj Z)))
    (hFu : ∀ {X Y : C₁} (c : k) (f : X ⟶ Y), Fu.map (c • f) = c • Fu.map f)
    (hFm : ∀ {X Y : C₃} {f : X ⟶ Y}, f ∈ parity (R := k) X Y q →
      Fm.map f ∈ parity (R := k) _ _ q)
    (G₁ G₂ : C₃ ⥤ C₀) (hG₁ : G₁ = Fm ⋙ Fa ⋙ Fu) (hG₂ : G₂ = Fm ⋙ Fa' ⋙ Fu)
    (W₁ W₂ : C₂) (hW₁ : W₁ = Fm.obj (Fb.obj Z)) (hW₂ : W₂ = Fm.obj (Fb'.obj Z)) {A B : C₀}
    (e₁ : A = Fu.obj (Fa.obj W₁)) (e₂ : Fu.obj (Fa'.obj W₁) = G₂.obj (Fb.obj Z))
    (e₃ : G₂.obj (Fb'.obj Z) = B)
    (f₁ : A = G₁.obj (Fb.obj Z)) (f₂ : G₁.obj (Fb'.obj Z) = Fu.obj (Fa.obj W₂))
    (f₃ : Fu.obj (Fa'.obj W₂) = B) :
    eqToHom e₁ ≫ Fu.map (γ W₁) ≫ eqToHom e₂ ≫ G₂.map η ≫ eqToHom e₃ =
      sign k (p*q) • (eqToHom f₁ ≫ G₁.map η ≫ eqToHom f₂ ≫ Fu.map (γ W₂) ≫ eqToHom f₃) := by
  subst hG₁ hG₂ hW₁ hW₂ e₁ f₃
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id,Functor.comp_map,Functor.comp_obj]
  have hn : Fa.map (Fm.map η) ≫ γ (Fm.obj (Fb'.obj Z)) =
      sign k (p*q) • (γ (Fm.obj (Fb.obj Z)) ≫ Fa'.map (Fm.map η)) :=
    hγ.naturality (f := ObjectProperty.homMk (X := ⟨_,hS₁⟩) (Y := ⟨_,hS₂⟩) (Fm.map η)) (hFm hη)
  rw [← Fu.map_comp,← Fu.map_comp,hn,hFu,smul_smul,Supercategory.sign_mul_self,one_smul]
end Exchange

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{wB,vB} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}

/-- Generator naturality after the full inclusion of the retained inputs. -/
def GeneratorsSupernaturalOn (Q : ∀ s, ObjectProperty (P.H s)) (gens : P.Generators) : Prop :=
  ∀ (g : (SKM.sig D).Gen) {t s : Sector I} (p : SPath (wd D g.2 g.1.dom) t s)
    (p' : SPath (wd D g.2 g.1.cod) t s),
    IsSupernatural k (g.1.parity D) (F := (Q s).ι ⋙ P.pathFunctor p)
      (G := (Q s).ι ⋙ P.pathFunctor p') (fun Z => gens.image g p p' Z.obj)

/-- The native layer representation satisfies super interchange when its
source objects and their path images retain the stated naturality domain. -/
theorem interchangeLaw_on (Q : ∀ s, ObjectProperty (P.H s))
    (hpath : ∀ {w : List (Col I X)} {s t : Sector I} (p : SPath w s t) (Z : P.H t),
      Q t Z → Q s ((P.pathFunctor p).obj Z))
    (Gs Ys : ∀ s, P.H s) (hYs : ∀ s, Q s (Ys s))
    {gens : P.Generators} (hs : GeneratorsSupernaturalOn Q gens) :
    InterchangeLaw (P.layerRep Gs Ys gens) := by
  intro x hx u v _
  refine (P.layerRep Gs Ys gens).toLocal.evalW_interchange_eq_zero
    (fun s l m r g g' => LinearMap.ext fun y => ?_) x hx u v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LayerRep.toLocal_κ]
  rw [LayerRep.res_op_op_ext _ _ _ (by simp [Layer.dom]) (by simp [Layer.dom, Layer.cod])
      (by simp [Layer.cod]),
    LayerRep.res_op_op_ext _ _ _ (by simp [Layer.dom]) (by simp [Layer.dom, Layer.cod])
      (by simp [Layer.cod])]
  by_cases hv : (⟨s, l, g, m ++ ((SKM.sig D).dom g' ++ r)⟩ : Layer (SKM.sig D)).Valid ∧
      (⟨s, l ++ ((SKM.sig D).cod g ++ m), g', r⟩ : Layer (SKM.sig D)).Valid
  swap
  · have hv' : ¬ ((⟨s, l, g, m ++ ((SKM.sig D).cod g' ++ r)⟩ : Layer (SKM.sig D)).Valid ∧
        (⟨s, l ++ ((SKM.sig D).dom g ++ m), g', r⟩ : Layer (SKM.sig D)).Valid) :=
      fun ⟨h1, h2⟩ => hv (valid_interchange_of_valid ⟨h1.cod_ok, h1.cod_end⟩
        ⟨h2.dom_ok, h2.dom_end⟩ h1.dom_end h1 h2)
    rw [not_and_or] at hv hv'
    rcases hv with hv | hv <;> rcases hv' with hv' | hv' <;>
    · have h0 : (P.layerRep Gs Ys gens).act _ = 0 := layerMap_of_not_valid gens hv
      have h0' : (P.layerRep Gs Ys gens).act _ = 0 := layerMap_of_not_valid gens hv'
      simp only [h0, h0', LinearMap.zero_apply]
      repeat (first
        | erw [LayerRep.cast_zero (P.layerRep Gs Ys gens)]
        | erw [map_zero]
        | erw [smul_zero])
      all_goals simp [Layer.cod, Layer.dom]
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨h1', h2'⟩ : (⟨s, l, g, m ++ ((SKM.sig D).cod g' ++ r)⟩ : Layer (SKM.sig D)).Valid ∧
      (⟨s, l ++ ((SKM.sig D).dom g ++ m), g', r⟩ : Layer (SKM.sig D)).Valid :=
    valid_interchange_of_valid ⟨h1.dom_ok, h1.dom_end⟩ ⟨h2.cod_ok, h2.cod_end⟩ h1.cod_end h1 h2
  funext s0 t q
  dsimp only [LayerRep.toLocal_κ] at q t
  obtain ⟨t1, pu, q1, rfl⟩ := SPath.exists_eq_append l q
  obtain ⟨t2, qa, q2, rfl⟩ := SPath.exists_eq_append _ q1
  obtain ⟨t3, pm, q3, rfl⟩ := SPath.exists_eq_append m q2
  obtain ⟨t4, qb, pr, rfl⟩ := SPath.exists_eq_append _ q3
  erw [Mod.cast_apply (by simp [Layer.cod]) _ s0 t _
    (((pu.append (qa.append pm)).append qb).append pr)
    (heq_assoc₁ pu qa pm qb pr)]
  rw [layerRep_act]
  erw [layerMap_apply_append gens _ h2 _ (pu.append (qa.append pm)) qb pr]
  conv_lhs =>
    enter [1, 2, pb]
    unfold layerEntry
    erw [Mod.cast_apply (by simp [Layer.cod, Layer.dom]) _ s0 _ _
      ((pu.append qa).append (pm.append (pb.append pr))) (heq_assoc₂ pu qa pm pb pr)]
    rw [layerRep_act]
    erw [layerMap_apply_append gens _ h1 _ pu qa (pm.append (pb.append pr))]
    enter [1, 1, 2, pa]
    unfold layerEntry
    erw [Mod.cast_apply (by simp [Layer.dom]) _ s0 _ _
      (pu.append (pa.append (pm.append (pb.append pr))))
      (SPath.append_assoc_heq pu pa _).symm]
  refine Eq.trans ?_ (Mod.smul_apply (P := P) (Gs := Gs) (Ys := Ys)
    (a := ⟨s, l ++ ((SKM.sig D).cod g ++ (m ++ ((SKM.sig D).cod g' ++ r)))⟩) _ _ _ _ _).symm
  erw [Mod.cast_apply (by simp [Layer.cod]) _ s0 t _
    ((pu.append qa).append (pm.append (qb.append pr))) (SPath.append_assoc_heq pu qa _)]
  rw [layerRep_act]
  erw [layerMap_apply_append gens _ h1' _ pu qa (pm.append (qb.append pr))]
  conv_rhs =>
    enter [2, 1, 2, pa]
    unfold layerEntry
    erw [Mod.cast_apply (by simp [Layer.cod, Layer.dom]) _ s0 _ _
      (((pu.append (pa.append pm)).append qb).append pr) (heq_assoc₂ pu pa pm qb pr).symm]
    rw [layerRep_act]
    erw [layerMap_apply_append gens _ h2' _ (pu.append (pa.append pm)) qb pr]
    enter [1, 1, 2, pb]
    unfold layerEntry
    erw [Mod.cast_apply (by simp [Layer.dom]) _ s0 _ _
      (pu.append (pa.append (pm.append (pb.append pr)))) (heq_assoc₁ pu pa pm pb pr).symm]
  simp only [Preadditive.sum_comp, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pa _ => Finset.sum_congr rfl fun pb _ => ?_
  rw [← Linear.comp_smul, interchange_sign]
  congr 1
  exact eqToHom_map_comp_exchange_on (P.pathFunctor pu) (P.pathFunctor pa) (P.pathFunctor qa)
    (P.pathFunctor pm) (P.pathFunctor pb) (P.pathFunctor qb) ((P.pathFunctor pr).obj (Ys t))
    (hs g pa qa) ((hs g' pb qb).mem ⟨_,hpath pr _ (hYs t)⟩)
    (hpath pm _ (hpath pb _ (hpath pr _ (hYs t))))
    (hpath pm _ (hpath qb _ (hpath pr _ (hYs t))))
    (P.pathFunctor_map_smul pu) (P.pathFunctor_map_mem pm)
    _ _ (by rw [pathFunctor_append, pathFunctor_append]; rfl)
    (by rw [pathFunctor_append, pathFunctor_append]; rfl)
    _ _ (by rw [pathFunctor_append, pathFunctor_append]; rfl)
    (by rw [pathFunctor_append, pathFunctor_append]; rfl) _ _ _ _ _ _

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
