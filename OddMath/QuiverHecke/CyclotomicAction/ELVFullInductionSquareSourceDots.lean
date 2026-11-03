import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareCounit

/-! # Signed dot powers through the selected full-inclusion source chart

The dotted cap rows in Brundan–Ellis (1.13)–(1.14) use the same source
comparison as the principal mate. Its native and ordinary coefficient
coordinates agree and its whole signed dot operator is intertwined.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem coend_ext
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

private theorem raw_pow_square {k V W : Type u} [CommRing k]
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
  apply coend_ext _ _
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
  apply coend_ext _ _
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
  raw_pow_square _ _ _ (fullSquareSourceLinear_transform J U Q T h R S e hα hβ he w hCoeff) n

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
end OddMath.QuiverHecke.ELVOld.BalancedInduction
