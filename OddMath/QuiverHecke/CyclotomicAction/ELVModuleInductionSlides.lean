import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionRelations

/-! # Homogeneous slides under balanced induction

Brundan–Ellis (1.8): a source dot/crossing slide induces the corresponding
whole module-map slide, with the two superopposite composition signs
cancelling. This supplies the distinct-colour probe relation on direct
induction before its chosen pair flattenings are applied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  {F G : C ⥤ A}
  [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  [G.Additive] [G.Linear k] [IsSuperfunctor k G]
  {p q : ZMod 2} {x : ∀ v, F.obj v ⟶ F.obj v}
  {c : ∀ v, F.obj v ⟶ G.obj v} {y : ∀ v, G.obj v ⟶ G.obj v}
  (hx : IsSupernatural k p x) (hc : IsSupernatural k q c)
  (hy : IsSupernatural k p y) (a : k)
  (hs : ∀ v, x v ≫ c v = a • (c v ≫ y v))

include hs in
/-- The original scalar remains after both contravariant composition signs. -/
theorem transformLinear_rectangular_slide (M : Superfunctor k C (SVec k)) (w : A) :
    transformLinear hx M w ∘ₗ transformLinear hc M w =
      a • (transformLinear hc M w ∘ₗ transformLinear hy M w) := by
  rw [transformLinear_comp, transformLinear_comp]
  apply hom_ext
  intro v h m
  simp only [LinearMap.smul_apply, transformLinear_tensor]
  change sign k (p * q) • tensor F M.toFunctor v ((x v ≫ c v) ≫ twist k (p + q) h) m =
    a • (sign k (q * p) • tensor F M.toFunctor v ((c v ≫ y v) ≫ twist k (q + p) h) m)
  rw [hs v, Linear.smul_comp, mul_comm q p, add_comm q p]
  simp only [tensor, ← TensorProduct.smul_tmul', map_smul]
  exact smul_comm _ _ _

include hs in
/-- The homogeneous slide holds on entire induced module maps. -/
theorem transformComponent_rectangular_slide (M : Superfunctor k C (SVec k)) :
    transformComponent hc M ≫ transformComponent hx M =
      a • (transformComponent hy M ≫ transformComponent hc M) := by
  apply Superfunctor.hom_ext
  intro r w
  have he := transformLinear_rectangular_slide hx hc hy a hs M w
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp only [Superfunctor.comp_app, Superfunctor.smul_app, transformComponent_app,
      SVec.zmod2_one_add_one, zero_add, add_zero, ↓reduceIte, one_ne_zero, zero_ne_one,
      CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp, smul_zero,
      zero_add, add_zero] <;> exact he

end OddMath.QuiverHecke.ELVOld.BalancedInduction
