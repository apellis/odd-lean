import OddMath.SKM.RouquierHomPreInverse
import OddMath.SKM.RouquierSupernaturalInverse

/-!
# Precomposition augmented inverses in the Hom supercategory

The normalized precomposition mate and its dotted windows from
`SwappedHomInversion.md`, §2, retain signed naturality on odd Hom maps.
The homogeneous shift removals are themselves supernatural of the
left-adjunction parity; their two contributions cancel in inverse entries.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

/-- An invertible homogeneous supernatural family has a supernatural inverse. -/
theorem isSupernatural_iso_inv {k : Type r} [CommRing k]
    {C C' : Type*} [Category C] [Category C']
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive C'] [Linear k C'] [Supercategory k C']
    {F G : C ⥤ C'} [F.Additive] [F.Linear k] [G.Additive] [G.Linear k]
    {p : ZMod 2} (a : ∀ Z, F.obj Z ≅ G.obj Z)
    (ha : IsSupernatural k p (fun Z => (a Z).hom)) :
    IsSupernatural k p (F := G) (G := F) (fun Z => (a Z).inv) where
  mem Z := inv_mem (a Z) (ha.mem Z)
  naturality := by
    intro Z Z' q f hf
    have hn := ha.naturality hf
    apply (cancel_mono (a Z').hom).mp
    simp only [Linear.smul_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn, Linear.comp_smul, smul_smul, sign_mul_self,
      one_smul, Iso.inv_hom_id_assoc]

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
  (i : I) (muM : X) {muP nuP rhoP : X}
  (h : -nuP + D.α i = -muP) (h₂ : -rhoP + D.α i = -nuP)

instance : (homContentPreE T W i muM h).Additive := by
  unfold homContentPreE
  infer_instance

instance : (homContentPreE T W i muM h).Linear k := by
  unfold homContentPreE
  infer_instance

instance : (homContentPreF T W i muM h).Additive := by
  unfold homContentPreF
  infer_instance

instance : (homContentPreF T W i muM h).Linear k := by
  unfold homContentPreF
  infer_instance

instance : IsSuperfunctor k (homContentPreF T W i muM h) := by
  unfold homContentPreF
  infer_instance

/-- The prescribed normalized mate is signed-natural on odd Hom morphisms. -/
theorem homContentPreMate_supernatural :
    IsSupernatural k (D.parity i)
      (F := homContentPreF T W i muM h ⋙ homContentPreE T W i muM h)
      (G := homContentPreE T W i muM h₂ ⋙ homContentPreF T W i muM h₂)
      (homContentPreMate T W i muM h h₂) :=
  (rouquierMate (homContentSuperAdjunction T W i muM h)
    (homContentSuperAdjunction T W i muM h₂)
    (homContentCrossing T W i muM h h₂)).isSupernatural (D.parity i)

/-- The specified mate as a homogeneous transformation on the full Hom space. -/
def homContentPreSuperMate :
    homContentSuperF T W i muM h ≫ homContentSuperE T W i muM h ⟶
      homContentSuperE T W i muM h₂ ≫ homContentSuperF T W i muM h₂ :=
  (homContentPreMate_supernatural T W i muM h h₂).toSuperNatTrans

/-- The bundled mate is the actual cup–crossing–cap mate. -/
theorem homContentPreSuperMate_eq : homContentPreSuperMate T W i muM h h₂ =
    rouquierMate (homContentSuperAdjunction T W i muM h)
      (homContentSuperAdjunction T W i muM h₂)
      (homContentCrossing T W i muM h h₂) := by
  have hm := rouquierMate_homogeneous
    (homContentSuperAdjunction T W i muM h)
    (homContentSuperAdjunction T W i muM h₂)
    (homContentCrossing_mem T W i muM h h₂)
  apply Superfunctor.hom_ext
  intro q Z
  change (if q = D.parity i then _ else 0) = _
  by_cases hq : q = D.parity i
  · subst q; rw [ite_eq_left rfl]; rfl
  · rw [ite_eq_right hq]
    exact (Superfunctor.app_eq_zero_of_mem hm hq Z).symm

end OddMath.SKM
