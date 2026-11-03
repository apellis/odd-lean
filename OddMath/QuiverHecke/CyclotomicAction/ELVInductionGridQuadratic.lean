import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularMate

/-! # Quadratic transport through the chosen rectangular induction charts

Brundan–Ellis (1.7): signed source quadratics pass to whole module maps
through both prescribed composition charts. The source polynomial is
separate from the crossings; concrete applications must prove its relation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem conjugate_pair_comp {V : Type*} [Category V]
    {x x' y y' : V} (e : x ≅ x') (f : y ≅ y')
    (c : x' ⟶ y') (d : y' ⟶ x') :
    (e.hom ≫ c ≫ f.inv) ≫ (f.hom ≫ d ≫ e.inv) =
      e.hom ≫ (c ≫ d) ≫ e.inv := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  {F G : C ⥤ E}
  [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  [G.Additive] [G.Linear k] [IsSuperfunctor k G]
  {p : ZMod 2} {a : ∀ s, F.obj s ⟶ G.obj s} {b : ∀ s, G.obj s ⟶ F.obj s}
  {Q : ∀ s, F.obj s ⟶ F.obj s}
  (ha : IsSupernatural k p a) (hb : IsSupernatural k p b)
  (hQ : IsSupernatural k 0 Q)
  (hs : ∀ s, sign k p • (a s ≫ b s) = Q s)

omit [IsSuperfunctor k F] [IsSuperfunctor k G] in
include ha hb hs in
/-- The literal signed source polynomial inherits even supernaturality. -/
theorem signedQuadratic_supernatural : IsSupernatural k 0 Q := by
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with he | he <;> simp [he]
  have hc : IsSupernatural k 0 (fun s => a s ≫ b s) := by
    simpa only [hpp] using ha.comp hb
  have hsm : IsSupernatural k 0 (fun s => sign k p • (a s ≫ b s)) := {
    mem := fun s => Submodule.smul_mem _ _ (hc.mem s)
    naturality := by
      intro s t q f hf
      simp only [Linear.comp_smul, Linear.smul_comp]
      rw [hc.naturality hf]
      simp only [zero_mul, Supercategory.sign_zero, one_smul] }
  simpa only [hs] using hsm

include hs in
/-- The superopposite composition sign is absorbed by the signed source polynomial. -/
theorem transformComponent_signed_quadratic (N : Superfunctor k C (SVec k)) :
    transformComponent hb N ≫ transformComponent ha N = transformComponent hQ N := by
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with he | he <;> simp [he]
  have hsq : p * p = p := by
    rcases parity_eq_zero_or_one p with he | he <;> simp [he]
  have hl (w : E) : transformLinear ha N w ∘ₗ transformLinear hb N w =
      transformLinear hQ N w := by
    rw [transformLinear_comp]
    apply hom_ext
    intro s g n
    simp only [LinearMap.smul_apply, transformLinear_tensor]
    change sign k (p * p) • tensor F N.toFunctor s
      ((a s ≫ b s) ≫ twist k (p + p) g) n =
      tensor F N.toFunctor s (Q s ≫ twist k 0 g) n
    rw [hpp, twist_zero, hsq, ← hs s, Linear.smul_comp]
    simp only [tensor, ← TensorProduct.smul_tmul', map_smul]
  apply Superfunctor.hom_ext
  intro r w
  have he := hl w
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp only [Superfunctor.comp_app, transformComponent_app,
      SVec.zmod2_one_add_one, zero_add, add_zero, ↓reduceIte, one_ne_zero, zero_ne_one,
      CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp,
      zero_add, add_zero] <;> exact he

section Rectangular
variable {A B : Type u}
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ T).obj s}
  {β : ∀ s, (K ⋙ T).obj s ⟶ (J ⋙ L).obj s}
  {P : ∀ s, (K ⋙ T).obj s ⟶ (K ⋙ T).obj s}
  (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β)
  (hP : IsSupernatural k 0 P)
  (hsource : ∀ s, sign k p • (β s ≫ α s) = P s)

include hsource in
/-- Both selected flattenings cancel between the actual rectangular crossings. -/
theorem rectangularCrossComponent_signed_quadratic (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hα N ≫
      rectangularCrossComponent K J T L hβ N =
      (inductionComp K T).hom.app N ≫ transformComponent hP N ≫
        (inductionComp K T).inv.app N := by
  have he := transformComponent_signed_quadratic hβ hα hP hsource N
  let e : induced T (induced K N) ≅ induced (K ⋙ T) N := (inductionComp K T).app N
  let f : induced L (induced J N) ≅ induced (J ⋙ L) N := (inductionComp J L).app N
  exact (conjugate_pair_comp e f (transformComponent hα N) (transformComponent hβ N)).trans
    (congrArg (fun c => e.hom ≫ c ≫ e.inv) he)
include hsource in
/-- The reverse crossing may retain its own propositionally equal parity label. -/
theorem rectangularCrossComponent_signed_quadratic_of_parity
    {q : ZMod 2} (hβ' : IsSupernatural k q β) (hpq : q = p)
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hα N ≫
      rectangularCrossComponent K J T L hβ' N =
      (inductionComp K T).hom.app N ≫ transformComponent hP N ≫
        (inductionComp K T).inv.app N := by
  cases hpq
  exact rectangularCrossComponent_signed_quadratic J K L T hα hβ' hP hsource N

end Rectangular
end OddMath.QuiverHecke.ELVOld.BalancedInduction
