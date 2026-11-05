import OddMath.Algebra.HomogeneousSuperfunctorIso
import StringDiagrams.Super.SVec

/-! # Supermodule isomorphisms from bijective total components

The pointwise inverse step for the prescribed module matrices in
Brundan–Ellis (1.13)–(1.14), after their actual forward maps and parity
have been established. No pointwise inverse family is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.HomogeneousSuperfunctorIso
universe u v w
variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {F G : Superfunctor k C (SVec k)}

/-- Bijective total components invert the specified homogeneous module map. -/
def ofBijectiveTotals {p : ZMod 2} (f : F ⟶ G) (hf : f ∈ parity (R := k) _ _ p)
    (hb : ∀ X, Function.Bijective (f.total X)) : F ≅ G :=
  ofHom f hf
    (fun X => SVec.isoOfLinearEquiv (LinearEquiv.ofBijective (SVec.toLinearMap (f.total X)) (hb X)))
    (fun _ => rfl)

/-- Its forward is the given map, without an additional compatibility premise. -/
@[simp] theorem ofBijectiveTotals_hom {p : ZMod 2} (f : F ⟶ G) (hf : f ∈ parity (R := k) _ _ p)
    (hb : ∀ X, Function.Bijective (f.total X)) : (ofBijectiveTotals f hf hb).hom = f :=
  ofHom_hom f hf _ _

@[simp] theorem ofBijectiveTotals_hom_inv_id {p : ZMod 2} (f : F ⟶ G) (hf : f ∈ parity (R := k) _ _ p)
    (hb : ∀ X, Function.Bijective (f.total X)) : f ≫ (ofBijectiveTotals f hf hb).inv = 𝟙 F := by
  simpa only [ofBijectiveTotals_hom] using (ofBijectiveTotals f hf hb).hom_inv_id

@[simp] theorem ofBijectiveTotals_inv_hom_id {p : ZMod 2} (f : F ⟶ G) (hf : f ∈ parity (R := k) _ _ p)
    (hb : ∀ X, Function.Bijective (f.total X)) : (ofBijectiveTotals f hf hb).inv ≫ f = 𝟙 G := by
  simpa only [ofBijectiveTotals_hom] using (ofBijectiveTotals f hf hb).inv_hom_id

end OddMath.HomogeneousSuperfunctorIso
