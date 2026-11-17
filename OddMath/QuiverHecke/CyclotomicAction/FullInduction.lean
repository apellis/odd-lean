import OddMath.QuiverHecke.CyclotomicAction.ContentModule.ContentSupportedExtension
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed.InductionMixedCrossTensor
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend.WeightedMatrixRows

/-!
# Full induction

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # A commuting induction square with full upper inclusion

The canonical content chart in Brundan–Ellis (1.12) is the induction
composition comparison followed by restriction along a full inclusion.
Its selected full-inclusion unit and its generator formula are evaluated
before specializing any coefficient quotient or content category.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem blockFullComparison_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Full] [J.Faithful] [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M : Superfunctor k C (SVec k)) (P : Superfunctor k A (SVec k))
    (e : induced J M ≅ P) (v : C) (b : M.obj v) :
    ((fullyFaithfulUnitIso J M ≪≫
      (restriction J).mapIso e).hom).total v b =
      e.hom.total (J.obj v) (unit J M.toFunctor v b) := by
  have hu : (fullyFaithfulUnitIso J M).hom.total v b =
      unit J M.toFunctor v b := by
    rw [fullyFaithfulUnitIso_hom]
    exact unit_total_apply J M v b
  rw [Iso.trans_hom, Functor.mapIso_hom, Superfunctor.comp_total]
  change ((restriction J).map e.hom).total v
    ((fullyFaithfulUnitIso J M).hom.total v b) = _
  exact congrArg (fun a => ((restriction J).map e.hom).total v a) hu

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T)

/-- The chosen extension comparison on arbitrary supernatural module maps. -/
def fullSquareExtensionIso : induction (k := k) J ⋙ induction U ≅ induction Q ⋙ induction T :=
  inductionComp J U ≪≫ inductionFunctorIsoOfEq (J ⋙ U) (Q ⋙ T) h ≪≫ (inductionComp Q T).symm

/-- Restrict the chosen extension comparison after its selected full-inclusion unit. -/
def fullSquareRestrictionIso (M : Superfunctor k C (SVec k)) :
    induced J M ≅ (restriction U).obj (induced T (induced Q M)) :=
  fullyFaithfulUnitIso U (induced J M) ≪≫
    (restriction U).mapIso ((fullSquareExtensionIso J U Q T h).app M)

omit [U.Full] [U.Faithful] in
private theorem fullSquareExtension_hom_square (M : Superfunctor k C (SVec k)) :
    (fullSquareExtensionIso J U Q T h).hom.app M =
      squareComparison J U Q T h M (induced Q M) (𝟙 _) := by
  have hi := (induction (k := k) T).map_id ((induction (k := k) Q).obj M)
  unfold fullSquareExtensionIso squareComparison
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
  rw [hi]
  set_option backward.dsimp.instances true in
    dsimp only [induction, Functor.comp_obj] at *
  rw [Category.comp_id]

private theorem fullSquareRestriction_total (M : Superfunctor k C (SVec k)) (w : A)
    (b : (induced J M).obj w) :
    (fullSquareRestrictionIso J U Q T h M).hom.total w b =
      ((fullSquareExtensionIso J U Q T h).hom.app M).total (U.obj w)
        (unit U (induced J M).toFunctor w b) :=
  blockFullComparison_total U (induced J M) (induced T (induced Q M))
    ((fullSquareExtensionIso J U Q T h).app M) w b

/-- The selected comparison with both literal raw coend endpoints fixed. -/
def fullSquareRestrictionLinear (M : Superfunctor k C (SVec k)) (w : A) :
    Obj J M.toFunctor w →ₗ[k] Obj T (induced Q M).toFunctor (U.obj w) :=
  (fullSquareRestrictionIso J U Q T h M).hom.total w

/-- Whole coefficient arrows retain the canonical input inclusion unit. -/
theorem fullSquareRestrictionLinear_tensor (M : Superfunctor k C (SVec k))
    (s : C) (w : A) (g : J.obj s ⟶ w) (b : M.obj s) :
    fullSquareRestrictionLinear J U Q T h M w (tensor J M.toFunctor s g b) =
      tensor T (induced Q M).toFunctor (Q.obj s)
        (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)
        (unit Q M.toFunctor s b) := by
  have h0 := fullSquareRestriction_total J U Q T h M w (tensor J M.toFunctor s g b)
  have h1 := congrArg (fun f => f.total (U.obj w)
    (unit U (induced J M).toFunctor w (tensor J M.toFunctor s g b)))
    (fullSquareExtension_hom_square J U Q T h M)
  have h2 := squareLinear_tensor J U Q T h M (induced Q M) (𝟙 _) (id_mem _) s w g b
  set_option backward.dsimp.instances true in
    dsimp only [induction, squareLinear] at h2
  rw [Superfunctor.id_app_zero, SVec.id_apply] at h2
  have h3 := h0.trans h1
  unfold fullSquareRestrictionLinear
  rw [unit_apply] at h3
  exact h3.trans h2

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Ordinary coefficient coordinates for restriction coends

The mixed mate quotient comparison in Brundan–Ellis (1.12) uses the native
restriction module and the identical ordinary composition coefficient
functor. Their canonical coordinate equivalence is fixed before
specializing the old and truncated categories. The right action is unchanged.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A B : C ⥤ C) [B.Additive] [B.Linear k] [IsSuperfunctor k B]
  (M : Superfunctor k C (SVec k))

/-- Native restriction has the same ordinary coefficient functor. -/
def restrictionCoefficientCoordinates :
    ((restriction B).obj M).toFunctor ≅ B ⋙ M.toFunctor := Iso.refl _

/-- Both quotient coends use the identical ordinary right action. -/
def restrictionCoendCoordinates (w : C) :
    Obj A ((restriction B).obj M).toFunctor w ≃ₗ[k] Obj A (B ⋙ M.toFunctor) w :=
  coefficientEquiv A (restrictionCoefficientCoordinates B M) w

@[simp] theorem restrictionCoendCoordinates_tensor (s w : C) (g : A.obj s ⟶ w)
    (b : M.obj (B.obj s)) :
    restrictionCoendCoordinates A B M w
      (tensor A ((restriction B).obj M).toFunctor s g b) =
      tensor A (B ⋙ M.toFunctor) s g b :=
  coefficientEquiv_tensor A (restrictionCoefficientCoordinates B M) w s g b

@[simp] theorem restrictionCoendCoordinates_symm_tensor (s w : C) (g : A.obj s ⟶ w)
    (b : M.obj (B.obj s)) :
    (restrictionCoendCoordinates A B M w).symm
      (tensor A (B ⋙ M.toFunctor) s g b) =
      tensor A ((restriction B).obj M).toFunctor s g b :=
  coefficientMap_tensor A (restrictionCoefficientCoordinates B M).inv w s g b

/-- The same forward formula with its raw linear-map endpoint fixed. -/
theorem restrictionCoendCoordinates_hom_tensor (s w : C) (g : A.obj s ⟶ w)
    (b : M.obj (B.obj s)) :
    (restrictionCoendCoordinates A B M w).toLinearMap
      (tensor A ((restriction B).obj M).toFunctor s g b) =
      tensor A (B ⋙ M.toFunctor) s g b :=
  coefficientMap_tensor A (restrictionCoefficientCoordinates B M).hom w s g b

/-- The inverse coefficient map retains both literal tensor factors. -/
theorem restrictionCoendCoordinates_inv_tensor (s w : C) (g : A.obj s ⟶ w)
    (b : M.obj (B.obj s)) :
    (restrictionCoendCoordinates A B M w).symm.toLinearMap
      (tensor A (B ⋙ M.toFunctor) s g b) =
      tensor A ((restriction B).obj M).toFunctor s g b :=
  coefficientMap_tensor A (restrictionCoefficientCoordinates B M).inv w s g b

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Input-module isomorphisms after a full induction square

The mixed source chart for Brundan–Ellis (1.12) applies a chosen even
restriction-extension isomorphism after the selected append comparison.
Both its raw component and its tensor formula are evaluated before the
content categories and their quotient coefficients are substituted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem sourceRestriction_total
    {k C E : Type u} [CommRing k] [Category.{u} C] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (U : C ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    {M : Superfunctor k C (SVec k)} {P R : Superfunctor k E (SVec k)}
    (f : M ⟶ (restriction U).obj P) (g : P ⟶ R) (w : C) (b : M.obj w) :
    (f ≫ (restriction U).map g).total w b = g.total (U.obj w) (f.total w b) := by
  rw [Superfunctor.comp_total]
  rfl

private theorem sourceMap_even_tensor
    {k C E : Type u} [CommRing k] [Category.{u} C] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (A : C ⥤ E) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    {M P : Superfunctor k C (SVec k)} (f : M ⟶ P)
    (hf : f ∈ parity (R := k) _ _ 0) (w : E) (s : C) (g : A.obj s ⟶ w) (b : M.obj s) :
    (moduleMap A f).total w (tensor A M.toFunctor s g b) =
      tensor A P.toFunctor s g (f.total s b) := by
  have h := moduleMap_total_tensor_even A f hf w s g b
  have hz := Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide) s
  simpa only [SuperNatTrans.total, hz, add_zero] using h

private def fullSourceCoefficientIso
    {k B : Type u} [CommRing k] [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) :
    ((restriction V).obj G).toFunctor ≅ V ⋙ G.toFunctor := Iso.refl _

private def fullSourceCoordinates
    {k B E : Type u} [CommRing k] [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E]
    (T : B ⥤ E) (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) (w : E) :
    Obj T ((restriction V).obj G).toFunctor w ≃ₗ[k] Obj T (V ⋙ G.toFunctor) w :=
  coefficientEquiv T (fullSourceCoefficientIso V G) w

private theorem fullSourceCoordinates_tensor
    {k B E : Type u} [CommRing k] [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E]
    (T : B ⥤ E) (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) (s : B) (w : E) (g : T.obj s ⟶ w) (b : G.obj (V.obj s)) :
    (fullSourceCoordinates T V G w).toLinearMap
      (tensor T ((restriction V).obj G).toFunctor s g b) = tensor T (V ⋙ G.toFunctor) s g b :=
  coefficientMap_tensor T (fullSourceCoefficientIso V G).hom w s g b

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k)) (P : Superfunctor k B (SVec k))
  (e : induced Q M ≅ P)

/-- Ambient induction acts on its own unit tensor by literal postcomposition. -/
theorem fullSourceInduced_map_unit (s : C) (w : B) (g : Q.obj s ⟶ w) (b : M.obj s) :
    (induced Q M).map g (unit Q M.toFunctor s b) = tensor Q M.toFunctor s g b :=
  postcompose_unit Q M.toFunctor g b

/-- The selected restricted square chart is bijective on its complete raw coend. -/
theorem fullSquareRestrictionLinear_bijective (w : A) :
    Function.Bijective (fullSquareRestrictionLinear J U Q T h M w) :=
  coendIsoLinear_bijective J T U M (induced Q M) (fullSquareRestrictionIso J U Q T h M) w

/-- The selected square chart followed by the chosen input isomorphism under induction. -/
def fullSquareSourceIso : induced J M ≅ (restriction U).obj (induced T P) :=
  fullSquareRestrictionIso J U Q T h M ≪≫ (restriction U).mapIso ((induction T).mapIso e)

/-- The selected source chart with raw coend carriers fixed before specialization. -/
def fullSquareSourceLinear (w : A) : Obj J M.toFunctor w →ₗ[k] Obj T P.toFunctor (U.obj w) :=
  coendIsoLinear J T U M P (fullSquareSourceIso J U Q T h M P e) w

/-- The raw source chart is a component of the specified isomorphism, hence bijective. -/
theorem fullSquareSourceLinear_bijective (w : A) :
    Function.Bijective (fullSquareSourceLinear J U Q T h M P e w) :=
  coendIsoLinear_bijective J T U M P (fullSquareSourceIso J U Q T h M P e) w

/-- The whole selected coefficient and input isomorphism survive on every tensor. -/
theorem fullSquareSourceLinear_tensor (he : e.hom ∈ parity (R := k) _ _ 0)
    (s : C) (w : A) (g : J.obj s ⟶ w) (b : M.obj s) :
    fullSquareSourceLinear J U Q T h M P e w (tensor J M.toFunctor s g b) =
      tensor T P.toFunctor (Q.obj s)
        (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)
        (e.hom.total (Q.obj s) (unit Q M.toFunctor s b)) := by
  have h0 := sourceRestriction_total U (fullSquareRestrictionIso J U Q T h M).hom
    ((induction T).map e.hom) w (tensor J M.toFunctor s g b)
  have hE := fullSquareRestrictionLinear_tensor J U Q T h M s w g b
  have hMap := congrArg (fun z => ((induction T).map e.hom).total (U.obj w) z) hE
  have hInd := sourceMap_even_tensor T e.hom he (U.obj w) (Q.obj s)
    (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)
    (unit Q M.toFunctor s b)
  set_option backward.dsimp.instances true in
    dsimp only [induction, fullSquareRestrictionLinear] at hMap hInd
  exact h0.trans (hMap.trans hInd)

/-- A chosen input vector formula transfers before the square is specialized. -/
theorem fullSquareSourceLinear_tensor_of_image (he : e.hom ∈ parity (R := k) _ _ 0)
    (s : C) (w : A) (g : J.obj s ⟶ w) (b : M.obj s) (b' : P.obj (Q.obj s))
    (hb : e.hom.total (Q.obj s) (unit Q M.toFunctor s b) = b') :
    fullSquareSourceLinear J U Q T h M P e w (tensor J M.toFunctor s g b) =
      tensor T P.toFunctor (Q.obj s)
        (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) b' :=
  (fullSquareSourceLinear_tensor J U Q T h M P e he s w g b).trans
    (congrArg (fun x => tensor T P.toFunctor (Q.obj s)
      (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) x) hb)

/-- Read the selected source isomorphism in ordinary restriction coefficient coordinates. -/
def fullSquareOrdinarySourceLinear (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) (a : induced Q M ≅ (restriction V).obj G) (w : A) :
    Obj J M.toFunctor w →ₗ[k] Obj T (V ⋙ G.toFunctor) (U.obj w) :=
  (fullSourceCoordinates T V G (U.obj w)).toLinearMap ∘ₗ
    fullSquareSourceLinear J U Q T h M ((restriction V).obj G) a w

theorem fullSquareOrdinarySourceLinear_bijective
    (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) (a : induced Q M ≅ (restriction V).obj G) (w : A) :
    Function.Bijective (fullSquareOrdinarySourceLinear J U Q T h M V G a w) :=
  (fullSourceCoordinates T V G (U.obj w)).bijective.comp
    (fullSquareSourceLinear_bijective J U Q T h M ((restriction V).obj G) a w)

/-- The prescribed input vector formula is retained in ordinary coefficient coordinates. -/
theorem fullSquareOrdinarySourceLinear_tensor_of_image
    (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) (a : induced Q M ≅ (restriction V).obj G)
    (ha : a.hom ∈ parity (R := k) _ _ 0) (s : C) (w : A) (g : J.obj s ⟶ w)
    (b : M.obj s) (b' : G.obj (V.obj (Q.obj s)))
    (hb : a.hom.total (Q.obj s) (unit Q M.toFunctor s b) = b') :
    fullSquareOrdinarySourceLinear J U Q T h M V G a w (tensor J M.toFunctor s g b) =
      tensor T (V ⋙ G.toFunctor) (Q.obj s)
        (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) b' := by
  have hS := fullSquareSourceLinear_tensor_of_image J U Q T h M ((restriction V).obj G)
    a ha s w g b b' hb
  have hMap := congrArg (fullSourceCoordinates T V G (U.obj w)).toLinearMap hS
  have hC := fullSourceCoordinates_tensor T V G (Q.obj s) (U.obj w)
    (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) b'
  exact hMap.trans hC

/-- Reindex the selected target chart along a specified equality of its output object. -/
def fullSquareTargetLinear (w : A) (z : E) (hz : U.obj w = z) :
    Obj J M.toFunctor w →ₗ[k] Obj T (induced Q M).toFunctor z :=
  postcompose T (induced Q M).toFunctor (eqToHom hz) ∘ₗ
    fullSquareRestrictionLinear J U Q T h M w

theorem fullSquareTargetLinear_bijective (w : A) (z : E) (hz : U.obj w = z) :
    Function.Bijective (fullSquareTargetLinear J U Q T h M w z hz) := by
  subst z
  rw [fullSquareTargetLinear, eqToHom_refl, postcompose_id, LinearMap.id_comp]
  exact fullSquareRestrictionLinear_bijective J U Q T h M w

/-- The object transport is appended to the entire selected coefficient arrow. -/
theorem fullSquareTargetLinear_tensor (s : C) (w : A) (z : E) (hz : U.obj w = z)
    (g : J.obj s ⟶ w) (b : M.obj s) :
    fullSquareTargetLinear J U Q T h M w z hz (tensor J M.toFunctor s g b) =
      tensor T (induced Q M).toFunctor (Q.obj s)
        ((eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) ≫ eqToHom hz)
        (unit Q M.toFunctor s b) := by
  have hE := fullSquareRestrictionLinear_tensor J U Q T h M s w g b
  have hMap := congrArg (postcompose T (induced Q M).toFunctor (eqToHom hz)) hE
  exact hMap.trans (postcompose_tensor T (induced Q M).toFunctor (eqToHom hz)
    (Q.obj s) (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)
    (unit Q M.toFunctor s b))

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # A rectangular mate through chosen full-inclusion charts

For Brundan–Ellis (1.12), compare the actual positive rectangular mate
with its ambient mixed mate before specializing any content category.
The hypotheses are the commuting coefficient square and the chosen
restriction chart's unit formula. They impose no invertibility condition
on either mate. Ordinary coend balance retains the whole right action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C H V W E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} H] [Preadditive H] [Linear k H] [Supercategory k H]
  [Category.{u} V] [Preadditive V] [Linear k V] [Supercategory k V]
  [Category.{u} W] [Preadditive W] [Linear k W] [Supercategory k W]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ H) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ V) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : H ⥤ W) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (U : V ⥤ W) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
  (Q₀ : C ⥤ E) [Q₀.Additive] [Q₀.Linear k] [IsSuperfunctor k Q₀]
  (Qj : H ⥤ E) [Qj.Additive] [Qj.Linear k] [IsSuperfunctor k Qj]
  (Qi : V ⥤ E) [Qi.Additive] [Qi.Linear k] [IsSuperfunctor k Qi] [Qi.Full] [Qi.Faithful]
  (Qw : W ⥤ E) [Qw.Additive] [Qw.Linear k] [IsSuperfunctor k Qw] [Qw.Full] [Qw.Faithful]
  (A B : E ⥤ E) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B.Additive] [B.Linear k] [IsSuperfunctor k B]
  (hJ : J ⋙ Qj = Q₀ ⋙ B) (hK : K ⋙ Qi = Q₀ ⋙ A)
  (hL : L ⋙ Qw = Qj ⋙ A) (hU : U ⋙ Qw = Qi ⋙ B)
  {p : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ U).obj s}
  (hα : IsSupernatural k p α)
  {χ : ∀ s, (B ⋙ A).obj s ⟶ (A ⋙ B).obj s} (hχ : IsSupernatural k p χ)
  (M : Superfunctor k H (SVec k))
local notation "G" => induced Qj M
local notation "Input" => CategoryTheory.Functor.obj (restriction J) M

/-- The whole two mates commute with their chosen source and target charts. -/
theorem fullContentMate_square
    (e : induced Q₀ Input ≅ (restriction B).obj G) (he : e.hom ∈ parity (R := k) _ _ 0)
    (hUnit : ∀ s (b : M.obj (J.obj s)),
      e.hom.total (Q₀.obj s) (unit Q₀ (Input).toFunctor s b) =
        (G).map (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hJ))
          (unit Qj M.toFunctor (J.obj s) b))
    (hCoeff : ∀ s t (g : K.obj s ⟶ t),
      (eqToHom (congrArg (fun F : H ⥤ E => F.obj (J.obj s)) hL).symm ≫
        Qw.map (α s ≫ twist k p (U.map g))) ≫
          eqToHom (congrArg (fun F : V ⥤ E => F.obj t) hU) =
      A.map (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hJ)) ≫
        (χ (Q₀.obj s) ≫ twist k p (B.map
          (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hK).symm ≫ Qi.map g))))
    (t : V) :
    fullSquareTargetLinear L Qw Qj A hL M (U.obj t) (B.obj (Qi.obj t))
        (congrArg (fun F : V ⥤ E => F.obj t) hU) ∘ₗ
      orderedRectangularMateLinear J K L U hα M t =
      orderedMixedMateCoend A B hχ G (Qi.obj t) ∘ₗ
        fullSquareOrdinarySourceLinear K Qi Q₀ A hK Input B G e t := by
  apply hom_ext
  intro s g b
  have hM := orderedRectangularMateLinear_tensor J K L U hα M s t g b
  have hLeft := congrArg
    (fullSquareTargetLinear L Qw Qj A hL M (U.obj t) (B.obj (Qi.obj t))
      (congrArg (fun F : V ⥤ E => F.obj t) hU)) hM
  have hT := fullSquareTargetLinear_tensor L Qw Qj A hL M (J.obj s) (U.obj t)
    (B.obj (Qi.obj t)) (congrArg (fun F : V ⥤ E => F.obj t) hU)
    (α s ≫ twist k p (U.map g)) b
  have hS := fullSquareOrdinarySourceLinear_tensor_of_image K Qi Q₀ A hK Input B G e he s t g b
    ((G).map (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hJ))
      (unit Qj M.toFunctor (J.obj s) b)) (hUnit s b)
  have hRight := congrArg (orderedMixedMateCoend A B hχ G (Qi.obj t)) hS
  have hGlobal := orderedMixedMateCoend_tensor A B hχ G (Q₀.obj s) (Qi.obj t)
    (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hK).symm ≫ Qi.map g)
    ((G).map (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hJ))
      (unit Qj M.toFunctor (J.obj s) b))
  have hC := congrArg (fun a => tensor A (G).toFunctor (Qj.obj (J.obj s)) a
    (unit Qj M.toFunctor (J.obj s) b)) (hCoeff s t g)
  have hBalance := balance A (G).toFunctor
    (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hJ))
    (χ (Q₀.obj s) ≫ twist k p (B.map
      (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hK).symm ≫ Qi.map g)))
    (unit Qj M.toFunctor (J.obj s) b)
  simp only [LinearMap.comp_apply]
  exact (hLeft.trans (hT.trans (hC.trans hBalance))).trans (hRight.trans hGlobal).symm

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Evenness of the selected full-inclusion charts

The canonical parity-coordinate comparison for Brundan–Ellis
(1.13)–(1.14) uses the selected extension and restriction isomorphisms,
whose forward and inverse module maps are even.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem natIso_app_hom {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) (x : C) : (e.app x).hom = e.hom.app x := rfl

private theorem functorEq_mem
    {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive D] [Linear k D] [Supercategory k D]
    (J K : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K)
    (M : Superfunctor k C (SVec k)) :
    (inductionFunctorIsoOfEq J K h).hom.app M ∈ parity (R := k) _ _ 0 := by
  subst K
  exact id_mem _

private theorem restrictedTriple_total
    {k C A B : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {F G : Superfunctor k A (SVec k)} {P V : Superfunctor k B (SVec k)}
    (f : F ⟶ G) (a : (restriction J).obj G ⟶ (restriction Q).obj P)
    (b : P ⟶ V) (w : C) (x : F.obj (J.obj w)) :
    ((restriction J).map f ≫ a ≫ (restriction Q).map b).total w x =
      b.total (Q.obj w) (a.total w (f.total (J.obj w) x)) := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  rfl

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k))

omit [U.Full] [U.Faithful] in
/-- All three legs of the chosen induction extension comparison are even. -/
theorem fullSquareExtensionIso_hom_mem :
    (fullSquareExtensionIso J U Q T h).hom.app M ∈ parity (R := k) _ _ 0 := by
  have h0 := comp_mem (inductionComp_hom_mem J U M)
    (comp_mem (functorEq_mem (J ⋙ U) (Q ⋙ T) h M) (inductionComp_inv_mem Q T M))
  simpa only [fullSquareExtensionIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Category.assoc, zero_add] using h0

/-- The selected full-inclusion unit and extension comparison are even. -/
theorem fullSquareRestrictionIso_hom_mem :
    (fullSquareRestrictionIso J U Q T h M).hom ∈ parity (R := k) _ _ 0 := by
  have hU : (fullyFaithfulUnitIso U (induced J M)).hom ∈ parity (R := k) _ _ 0 := by
    rw [fullyFaithfulUnitIso_hom]
    exact adjunctionUnit_mem U (induced J M)
  have hE := map_mem (restriction U) (fullSquareExtensionIso_hom_mem J U Q T h M)
  have h0 := comp_mem hU hE
  simp only [fullSquareRestrictionIso, Iso.trans_hom, Functor.mapIso_hom, natIso_app_hom]
  set_option backward.dsimp.instances true in
    dsimp only [induction, Functor.comp_obj] at h0 ⊢
  simpa only [zero_add] using h0

/-- An even chosen input isomorphism retains evenness of the full source chart. -/
theorem fullSquareSourceIso_hom_mem (P : Superfunctor k B (SVec k)) (e : induced Q M ≅ P)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (fullSquareSourceIso J U Q T h M P e).hom ∈ parity (R := k) _ _ 0 := by
  have hE := map_mem (restriction U) (map_mem (induction T) he)
  have h0 := comp_mem (fullSquareRestrictionIso_hom_mem J U Q T h M) hE
  simp only [fullSquareSourceIso, Iso.trans_hom, Functor.mapIso_hom]
  set_option backward.dsimp.instances true in
    dsimp only [induction, Functor.comp_obj] at h0 ⊢
  simpa only [zero_add] using h0

/-- The complete chosen target chart keeps its strict restriction square and final target comparison. -/
def fullSquareTargetRetargetIso (P V : Superfunctor k B (SVec k))
    (a : (restriction J).obj ((restriction U).obj (induced T (induced Q M))) ≅ (restriction Q).obj P)
    (b : P ≅ V) : (restriction J).obj (induced J M) ≅ (restriction Q).obj V :=
  (restriction J).mapIso (fullSquareRestrictionIso J U Q T h M) ≪≫ a ≪≫ (restriction Q).mapIso b

theorem fullSquareTargetRetargetIso_hom_mem (P V : Superfunctor k B (SVec k))
    (a : (restriction J).obj ((restriction U).obj (induced T (induced Q M))) ≅ (restriction Q).obj P)
    (b : P ≅ V) (ha : a.hom ∈ parity (R := k) _ _ 0) (hb : b.hom ∈ parity (R := k) _ _ 0) :
    (fullSquareTargetRetargetIso J U Q T h M P V a b).hom ∈ parity (R := k) _ _ 0 := by
  have h0 := comp_mem (map_mem (restriction J) (fullSquareRestrictionIso_hom_mem J U Q T h M))
    (comp_mem ha (map_mem (restriction Q) hb))
  simpa only [fullSquareTargetRetargetIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, zero_add] using h0

/-- The full target component retains both specified endpoint maps. -/
theorem fullSquareTargetRetargetIso_total_apply
    (P V : Superfunctor k B (SVec k))
    (a : (restriction J).obj ((restriction U).obj (induced T (induced Q M))) ≅ (restriction Q).obj P)
    (b : P ≅ V) (w : C) (x : ((restriction J).obj (induced J M)).obj w) :
    (fullSquareTargetRetargetIso J U Q T h M P V a b).hom.total w x =
      b.hom.total (Q.obj w) (a.hom.total w
        ((fullSquareRestrictionIso J U Q T h M).hom.total (J.obj w) x)) := by
  simpa only [fullSquareTargetRetargetIso, Iso.trans_hom, Functor.mapIso_hom] using
    restrictedTriple_total J Q (fullSquareRestrictionIso J U Q T h M).hom a.hom b.hom w x

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Ordinary unit and dot fields through a full-inclusion square

The unit/dot part of Brundan–Ellis (1.13)–(1.14) is compared before
specializing the canonical content inclusion. The selected chart, the
ordinary unit, and all dot powers retain their literal coend formulas.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem coend_ext
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    {f g : Obj J M w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      f (tensor J M s a b) = g (tensor J M s a b)) : f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

private theorem unitDot_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (P : Superfunctor k C (SVec k)) (n : ℕ) (s : C) (b : P.obj s) :
    unitDotLinear J hα P n s b = ((transformLinear hα P (J.obj s)) ^ n) (unit J P.toFunctor s b) := rfl

private theorem raw_pow_square {k V W : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (c : V →ₗ[k] W) (f : V →ₗ[k] V) (g : W →ₗ[k] W)
    (h : c ∘ₗ f = g ∘ₗ c) (n : ℕ) : c ∘ₗ (f ^ n) = (g ^ n) ∘ₗ c :=
  intertwine_pow c f g h n

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k))

/-- The selected target chart carries the ordinary unit to the ordinary unit. -/
theorem fullSquareTargetLinear_unit (s : C) (b : M.obj s) :
    fullSquareTargetLinear J U Q T h M (J.obj s) (T.obj (Q.obj s))
      (congrArg (fun F : C ⥤ E => F.obj s) h) (unit J M.toFunctor s b) =
      unit T (induced Q M).toFunctor (Q.obj s) (unit Q M.toFunctor s b) := by
  have hC := fullSquareTargetLinear_tensor J U Q T h M s (J.obj s) (T.obj (Q.obj s))
    (congrArg (fun F : C ⥤ E => F.obj s) h) (𝟙 (J.obj s)) b
  have he : ((eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map (𝟙 (J.obj s))) ≫
      eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h)) = 𝟙 (T.obj (Q.obj s)) := by
    simp
  have hL := congrArg (fullSquareTargetLinear J U Q T h M (J.obj s) (T.obj (Q.obj s))
    (congrArg (fun F : C ⥤ E => F.obj s) h)) (unit_apply J M.toFunctor s b)
  have hE := congrArg (fun a => tensor T (induced Q M).toFunctor (Q.obj s) a
    (unit Q M.toFunctor s b)) he
  have hR := unit_apply T (induced Q M).toFunctor (Q.obj s) (unit Q M.toFunctor s b)
  have hh := hL.trans (hC.trans (hE.trans hR.symm))
  exact hh

variable {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, T.obj s ⟶ T.obj s} (hβ : IsSupernatural k p β)

/-- The whole selected chart intertwines homogeneous dot operators when their
coefficient square commutes. Canonical content supplies that coefficient equality. -/
theorem fullSquareTargetLinear_transform (w : A) (z : E) (hz : U.obj w = z)
    (hCoeff : ∀ s (g : J.obj s ⟶ w),
      ((eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map (α s ≫ twist k p g)) ≫ eqToHom hz) =
        β (Q.obj s) ≫ twist k p ((eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) ≫ eqToHom hz)) :
    fullSquareTargetLinear J U Q T h M w z hz ∘ₗ transformLinear hα M w =
      transformLinear hβ (induced Q M) z ∘ₗ fullSquareTargetLinear J U Q T h M w z hz := by
  apply coend_ext _ _
  intro s g b
  have hL := congrArg (fullSquareTargetLinear J U Q T h M w z hz)
    (transformLinear_tensor hα M w s g b)
  have hC := fullSquareTargetLinear_tensor J U Q T h M s w z hz (α s ≫ twist k p g) b
  have hR := congrArg (transformLinear hβ (induced Q M) z)
    (fullSquareTargetLinear_tensor J U Q T h M s w z hz g b)
  have hT := transformLinear_tensor hβ (induced Q M) z (Q.obj s)
    ((eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) ≫ eqToHom hz)
    (unit Q M.toFunctor s b)
  have hCo := congrArg (fun a => tensor T (induced Q M).toFunctor (Q.obj s) a
    (unit Q M.toFunctor s b)) (hCoeff s g)
  exact (hL.trans (hC.trans hCo)).trans (hR.trans hT).symm

/-- The selected target chart transports every ordinary unit/dot column.
The coefficient condition is discharged for the prescribed content dot. -/
theorem fullSquareTargetLinear_unitDot (s : C) (n : ℕ) (b : M.obj s)
    (hCoeff : ∀ v (g : J.obj v ⟶ J.obj s),
      ((eqToHom (congrArg (fun F : C ⥤ E => F.obj v) h).symm ≫ U.map (α v ≫ twist k p g)) ≫
        eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h)) =
      β (Q.obj v) ≫ twist k p ((eqToHom (congrArg (fun F : C ⥤ E => F.obj v) h).symm ≫ U.map g) ≫
        eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h))) :
    fullSquareTargetLinear J U Q T h M (J.obj s) (T.obj (Q.obj s))
      (congrArg (fun F : C ⥤ E => F.obj s) h) (unitDotLinear J hα M n s b) =
      unitDotLinear T hβ (induced Q M) n (Q.obj s) (unit Q M.toFunctor s b) := by
  have hD := fullSquareTargetLinear_transform J U Q T h M hα hβ (J.obj s) (T.obj (Q.obj s))
    (congrArg (fun F : C ⥤ E => F.obj s) h) hCoeff
  have hP := raw_pow_square
    (fullSquareTargetLinear J U Q T h M (J.obj s) (T.obj (Q.obj s))
      (congrArg (fun F : C ⥤ E => F.obj s) h))
    (transformLinear hα M (J.obj s)) (transformLinear hβ (induced Q M) (T.obj (Q.obj s)))
    hD n
  have hP' := LinearMap.congr_fun hP (unit J M.toFunctor s b)
  simp only [LinearMap.comp_apply] at hP'
  have hR := congrArg ((transformLinear hβ (induced Q M) (T.obj (Q.obj s))) ^ n)
    (fullSquareTargetLinear_unit J U Q T h M s b)
  have hL := congrArg (fullSquareTargetLinear J U Q T h M (J.obj s) (T.obj (Q.obj s))
    (congrArg (fun F : C ⥤ E => F.obj s) h)) (unitDot_apply J hα M n s b)
  have hO := unitDot_apply T hβ (induced Q M) n (Q.obj s) (unit Q M.toFunctor s b)
  have hOut := hR.trans hO.symm
  have hMid := hP'.trans hOut
  have hFinal := hL.trans hMid
  exact hFinal

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # The ordinary counit through a full-inclusion source chart

Brundan–Ellis (1.13)–(1.14): retain the specified ordinary counit and
chosen restriction chart. The input module is independent until the
zeroth-component transpose is specialized to the identity map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem coend_ext_2
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (R : C ⥤ SVec k) {w : A}
    {f g : Obj J R w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : R.obj s), f (tensor J R s a b) = g (tensor J R s a b)) : f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J R w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

section Transpose
variable {k C A : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (R : Superfunctor k C (SVec k)) (M : Superfunctor k A (SVec k))

/-- Transpose of the zeroth component, with independent input module. -/
def evenTransposeLinear (c : R ⟶ (restriction J).obj M) (w : A) :
    Obj J R.toFunctor w →ₗ[k] M.obj w :=
  restrictionCounitLinear J M w ∘ₗ mapComponent J c 0 w

theorem evenTransposeLinear_tensor (c : R ⟶ (restriction J).obj M)
    (s : C) (w : A) (g : J.obj s ⟶ w) (b : R.obj s) :
    evenTransposeLinear J R M c w (tensor J R.toFunctor s g b) = M.map g (c.app 0 s b) := by
  rw [evenTransposeLinear, LinearMap.comp_apply, mapComponent_tensor, twist_zero]
  exact restrictionCounitLinear_tensor J M s w g (c.app 0 s b)

/-- Specializing the independent input map to the identity recovers the given counit. -/
theorem evenTransposeLinear_id (w : A) :
    evenTransposeLinear J ((restriction J).obj M) M (𝟙 _) w = restrictionCounitLinear J M w := by
  apply coend_ext_2 _ _
  intro s g b
  have h := evenTransposeLinear_tensor J ((restriction J).obj M) M (𝟙 _) s w g b
  have hi : (𝟙 ((restriction J).obj M) : _ ⟶ _).app 0 s b = b := rfl
  exact (h.trans (congrArg (M.map g) hi)).trans (restrictionCounitLinear_tensor J M s w g b).symm

end Transpose

private theorem evenMap_value_naturality
    {k A B : Type u} [CommRing k]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (U : A ⥤ B) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    (M : Superfunctor k A (SVec k)) (P : Superfunctor k B (SVec k))
    (a : M ⟶ (restriction U).obj P) (ha : a ∈ parity (R := k) _ _ 0)
    (s w : A) (g : s ⟶ w) (b : M.obj s) :
    a.total w (M.map g b) = P.map (U.map g) (a.total s b) := by
  rw [HomogeneousSuperfunctorIso.total_eq_app a ha w, HomogeneousSuperfunctorIso.total_eq_app a ha s]
  exact congrArg (fun f : M.obj s ⟶ ((restriction U).obj P).obj w => f b)
    (a.toNatTrans.naturality g)

private theorem module_map_comp_value
    {k B : Type u} [CommRing k] [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (P : Superfunctor k B (SVec k)) {s w z : B} (g : s ⟶ w) (h : w ⟶ z) (b : P.obj s) :
    P.map h (P.map g b) = P.map (g ≫ h) b :=
  (congrArg (fun f : P.obj s ⟶ P.obj z => f b) (P.toFunctor.map_comp g h)).symm

variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ B) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ B) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T)
  (R : Superfunctor k C (SVec k)) (M : Superfunctor k A (SVec k)) (P : Superfunctor k B (SVec k))
  (c : R ⟶ (restriction J).obj M)
  (a : M ⟶ (restriction U).obj P) (ha : a ∈ parity (R := k) _ _ 0)
  (e : induced Q R ≅ (restriction T).obj P) (he : e.hom ∈ parity (R := k) _ _ 0)

include ha he in
/-- The selected source chart transports the prescribed ordinary counit.
Its unit condition is verified for the canonical full-content restriction chart. -/
theorem fullSquareOrdinarySourceLinear_counit
    (hUnit : ∀ s (b : R.obj s), e.hom.total (Q.obj s) (unit Q R.toFunctor s b) =
      P.map (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h)) (a.total (J.obj s) (c.app 0 s b))) (w : A) :
    a.total w ∘ₗ evenTransposeLinear J R M c w =
      counit T P.toFunctor (U.obj w) ∘ₗ fullSquareOrdinarySourceLinear J U Q T h R T P e w := by
  apply coend_ext_2 _ _
  intro s g b
  have hL := congrArg (a.total w) (evenTransposeLinear_tensor J R M c s w g b)
  have hN := evenMap_value_naturality U M P a ha (J.obj s) w g (c.app 0 s b)
  have hS := fullSquareOrdinarySourceLinear_tensor_of_image J U Q T h R T P e he s w g b
    (P.map (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h)) (a.total (J.obj s) (c.app 0 s b))) (hUnit s b)
  have hR := congrArg (counit T P.toFunctor (U.obj w)) hS
  have hEval := counit_tensor T P.toFunctor (U.obj w) (Q.obj s)
    (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h).symm ≫ U.map g)
    (P.map (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h)) (a.total (J.obj s) (c.app 0 s b)))
  have hComp := module_map_comp_value P (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h))
    (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h).symm ≫ U.map g) (a.total (J.obj s) (c.app 0 s b))
  have hCoef : eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h) ≫
      (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h).symm ≫ U.map g) = U.map g := by simp
  have hCancel := congrArg (fun v => P.map v (a.total (J.obj s) (c.app 0 s b))) hCoef
  exact (hL.trans hN).trans (hR.trans (hEval.trans (hComp.trans hCancel))).symm

/-- The selected ordinary source chart commutes with the literal local and
ambient counits after the canonical input inclusion unit. -/
theorem fullSquareOrdinarySourceLinear_counit_unit
    (a : induced Q ((restriction J).obj M) ≅ (restriction T).obj (induced U M))
    (ha : a.hom ∈ parity (R := k) _ _ 0)
    (hUnit : ∀ s (b : M.obj (J.obj s)),
      a.hom.total (Q.obj s) (unit Q ((restriction J).obj M).toFunctor s b) =
        (induced U M).map (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h))
          (unit U M.toFunctor (J.obj s) b))
    (w : A) (x : Obj J ((restriction J).obj M).toFunctor w) :
    unit U M.toFunctor w (restrictionCounitLinear J M w x) =
      counit T (induced U M).toFunctor (U.obj w)
        (fullSquareOrdinarySourceLinear J U Q T h ((restriction J).obj M) T (induced U M) a w x) := by
  have hCompat : ∀ s (b : ((restriction J).obj M).obj s),
      a.hom.total (Q.obj s) (unit Q ((restriction J).obj M).toFunctor s b) =
        (induced U M).map (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h))
          (((adjunctionUnit U).app M).total (J.obj s) ((𝟙 ((restriction J).obj M) : _ ⟶ _).app 0 s b)) := by
    intro s b
    have hU := unit_total_apply U M (J.obj s) b
    have hi : (𝟙 ((restriction J).obj M) : _ ⟶ _).app 0 s b = b := rfl
    have hI := congrArg (((adjunctionUnit U).app M).total (J.obj s)) hi
    exact (hUnit s b).trans (congrArg ((induced U M).map
      (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h))) (hU.symm.trans hI.symm))
  have hMap := fullSquareOrdinarySourceLinear_counit J U Q T h
    ((restriction J).obj M) M (induced U M) (𝟙 _) ((adjunctionUnit U).app M)
    (adjunctionUnit_mem U M) a ha hCompat w
  have hPoint := LinearMap.congr_fun hMap x
  simp only [LinearMap.comp_apply] at hPoint
  have hTrans := LinearMap.congr_fun (evenTransposeLinear_id J M w) x
  have hI := congrArg (((adjunctionUnit U).app M).total w) hTrans
  have hU := unit_total_apply U M w (restrictionCounitLinear J M w x)
  exact hU.symm.trans (hI.symm.trans hPoint)

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Signed dot powers through the selected full-inclusion source chart

The dotted cap rows in Brundan–Ellis (1.13)–(1.14) use the same source
comparison as the principal mate. Its native and ordinary coefficient
coordinates agree and its whole signed dot operator is intertwined.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem coend_ext_3
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (R : C ⥤ SVec k) {w : A}
    {f g : Obj J R w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : R.obj s), f (tensor J R s a b) = g (tensor J R s a b)) : f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J R w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

private theorem raw_pow_square_2 {k V W : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (c : V →ₗ[k] W) (f : V →ₗ[k] V) (g : W →ₗ[k] W)
    (h : c ∘ₗ f = g ∘ₗ c) (n : ℕ) : c ∘ₗ (f ^ n) = (g ^ n) ∘ₗ c :=
  intertwine_pow c f g h n

private theorem capDot_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k A (SVec k)) (n : ℕ) (w : A)
    (x : Obj J ((restriction J).obj M).toFunctor w) :
    capDotLinear J hα M n w x = restrictionCounitLinear J M w
      (((transformLinear hα ((restriction J).obj M) w) ^ n) x) := rfl

section Square
variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T) (R : Superfunctor k C (SVec k))

/-- The ordinary coefficient realization changes no value of the selected source chart. -/
theorem fullSquareOrdinarySourceLinear_eq_source
    (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) (e : induced Q R ≅ (restriction V).obj G)
    (he : e.hom ∈ parity (R := k) _ _ 0) (w : A) :
    fullSquareOrdinarySourceLinear J U Q T h R V G e w =
      fullSquareSourceLinear J U Q T h R ((restriction V).obj G) e w := by
  apply coend_ext_3 _ _
  intro s g b
  have hO := fullSquareOrdinarySourceLinear_tensor_of_image J U Q T h R V G e he s w g b
    (e.hom.total (Q.obj s) (unit Q R.toFunctor s b)) rfl
  have hN := fullSquareSourceLinear_tensor J U Q T h R ((restriction V).obj G) e he s w g b
  have hC : tensor T (V ⋙ G.toFunctor) (Q.obj s)
      (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)
      (e.hom.total (Q.obj s) (unit Q R.toFunctor s b)) =
      tensor T ((restriction V).obj G).toFunctor (Q.obj s)
      (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)
      (e.hom.total (Q.obj s) (unit Q R.toFunctor s b)) := rfl
  exact hO.trans (hC.trans hN.symm)

variable (S : Superfunctor k B (SVec k)) (e : induced Q R ≅ S)
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, T.obj s ⟶ T.obj s} (hβ : IsSupernatural k p β)

/-- The entire selected native source chart intertwines the two signed dots. -/
theorem fullSquareSourceLinear_transform (he : e.hom ∈ parity (R := k) _ _ 0) (w : A)
    (hCoeff : ∀ s (g : J.obj s ⟶ w),
      eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map (α s ≫ twist k p g) =
        β (Q.obj s) ≫ twist k p (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)) :
    fullSquareSourceLinear J U Q T h R S e w ∘ₗ transformLinear hα R w =
      transformLinear hβ S (U.obj w) ∘ₗ fullSquareSourceLinear J U Q T h R S e w := by
  apply coend_ext_3 _ _
  intro s g b
  have hL := congrArg (fullSquareSourceLinear J U Q T h R S e w)
    (transformLinear_tensor hα R w s g b)
  have hC := fullSquareSourceLinear_tensor J U Q T h R S e he s w (α s ≫ twist k p g) b
  have hR := congrArg (transformLinear hβ S (U.obj w))
    (fullSquareSourceLinear_tensor J U Q T h R S e he s w g b)
  have hT := transformLinear_tensor hβ S (U.obj w) (Q.obj s)
    (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)
    (e.hom.total (Q.obj s) (unit Q R.toFunctor s b))
  have hCo := congrArg (fun a => tensor T S.toFunctor (Q.obj s) a
    (e.hom.total (Q.obj s) (unit Q R.toFunctor s b))) (hCoeff s g)
  exact (hL.trans (hC.trans hCo)).trans (hR.trans hT).symm

/-- Every ordinary power uses that same selected source chart. -/
theorem fullSquareSourceLinear_transform_pow (he : e.hom ∈ parity (R := k) _ _ 0) (w : A)
    (hCoeff : ∀ s (g : J.obj s ⟶ w),
      eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map (α s ≫ twist k p g) =
        β (Q.obj s) ≫ twist k p (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)) (n : ℕ) :
    fullSquareSourceLinear J U Q T h R S e w ∘ₗ ((transformLinear hα R w) ^ n) =
      ((transformLinear hβ S (U.obj w)) ^ n) ∘ₗ fullSquareSourceLinear J U Q T h R S e w :=
  raw_pow_square_2 _ _ _ (fullSquareSourceLinear_transform J U Q T h R S e hα hβ he w hCoeff) n

end Square
section Caps
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ B) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ B) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k A (SVec k))
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, T.obj s ⟶ T.obj s} (hβ : IsSupernatural k p β)

/-- Every ordinary dot/counit row uses the same selected source and value charts.
The unit and dot coefficient conditions are supplied by the chosen content charts. -/
theorem fullSquareSourceLinear_capDot_unit
    (e : induced Q ((restriction J).obj M) ≅ (restriction T).obj (induced U M))
    (he : e.hom ∈ parity (R := k) _ _ 0)
    (hUnit : ∀ s (b : M.obj (J.obj s)),
      e.hom.total (Q.obj s) (unit Q ((restriction J).obj M).toFunctor s b) =
        (induced U M).map (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h))
          (unit U M.toFunctor (J.obj s) b))
    (w : A)
    (hCoeff : ∀ s (g : J.obj s ⟶ w),
      eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h).symm ≫ U.map (α s ≫ twist k p g) =
        β (Q.obj s) ≫ twist k p (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h).symm ≫ U.map g))
    (n : ℕ) (x : Obj J ((restriction J).obj M).toFunctor w) :
    unit U M.toFunctor w (capDotLinear J hα M n w x) =
      capDotLinear T hβ (induced U M) n (U.obj w)
        (fullSquareOrdinarySourceLinear J U Q T h ((restriction J).obj M) T (induced U M) e w x) := by
  have hE := fullSquareOrdinarySourceLinear_eq_source J U Q T h ((restriction J).obj M) T (induced U M) e he w
  have hP := fullSquareSourceLinear_transform_pow J U Q T h ((restriction J).obj M)
    ((restriction T).obj (induced U M)) e hα hβ he w hCoeff n
  have hPx := LinearMap.congr_fun hP x
  simp only [LinearMap.comp_apply] at hPx
  have hL := congrArg (unit U M.toFunctor w) (capDot_apply J hα M n w x)
  have hZero := fullSquareOrdinarySourceLinear_counit_unit J U Q T h M e he hUnit w
    (((transformLinear hα ((restriction J).obj M) w) ^ n) x)
  have hSwitch := congrArg (counit T (induced U M).toFunctor (U.obj w))
    (LinearMap.congr_fun hE (((transformLinear hα ((restriction J).obj M) w) ^ n) x))
  have hDot := congrArg (counit T (induced U M).toFunctor (U.obj w)) hPx
  have hOut := capDot_apply T hβ (induced U M) n (U.obj w)
    (fullSquareSourceLinear J U Q T h ((restriction J).obj M)
      ((restriction T).obj (induced U M)) e w x)
  have hCounit := restrictionCounitLinear_apply T (induced U M) (U.obj w)
    (((transformLinear hβ ((restriction T).obj (induced U M)) (U.obj w)) ^ n)
      (fullSquareSourceLinear J U Q T h ((restriction J).obj M)
        ((restriction T).obj (induced U M)) e w x))
  have hBack := congrArg (capDotLinear T hβ (induced U M) n (U.obj w)) (LinearMap.congr_fun hE x).symm
  have hFinal := hL.trans (hZero.trans (hSwitch.trans (hDot.trans (hCounit.symm.trans (hOut.symm.trans hBack)))))
  exact hFinal

end Caps
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
