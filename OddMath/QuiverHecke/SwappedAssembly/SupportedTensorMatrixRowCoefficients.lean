import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorMatrixCoefficients
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorRowLayers

/-! # Full source coefficients in the vacuum matrix row

SwappedVacuumCoordinates §§5–7: the specified matrix-row projection carries
the complete source coefficient action to postcomposition on the chosen
ambient path. Both terminal-object transport and full inclusion are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
private theorem functorEquality_square {C B : Type*} [Category* C] [Category* B]
    (F G : C ⥤ B) (h : F = G) {V W : C} (f : V ⟶ W) :
    F.map f ≫ eqToHom (congrArg (fun H => H.obj W) h) =
    eqToHom (congrArg (fun H => H.obj V) h) ≫ G.map f := by
  subst G
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

private theorem composeSquares {C : Type*} [Category* C] {U V W X : C}
    (f : U ⟶ V) (e : V ⟶ W) (d : W ⟶ X) (a : End V) (b : End W) (c : End X)
    (h₁ : a ≫ e = e ≫ b) (h₂ : b ≫ d = d ≫ c) :
    (f ≫ a) ≫ e ≫ d = (f ≫ e ≫ d) ≫ c := by
  simp only [Category.assoc]
  rw [← Category.assoc a e d, h₁, Category.assoc, h₂]

local instance tensorMatrixRowCoefficientHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
omit [Fintype I] in
private def coefficientAtEquality {C : Type*} [Category* C] [Preadditive C] [Linear k C]
    {V W : C} (h : V = W) (φ : SYM D k →ₐ[k] End V) : SYM D k →ₐ[k] End W := by
  subst W
  exact φ

omit [Fintype I] in
private theorem map_coefficientAtEquality {C B : Type*}
    [Category* C] [Preadditive C] [Linear k C] [Category* B]
    (F : C ⥤ B) {V W : C} (h : V = W) (φ : SYM D k →ₐ[k] End W) (a : SYM D k) :
    F.map (coefficientAtEquality D h.symm φ a) ≫ eqToHom (congrArg F.obj h) =
      eqToHom (congrArg F.obj h) ≫ F.map (φ a) := by
  subst W
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

variable (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR

private theorem factorPath_coefficient_square {l : List (Col I X)} {s t : Sector I}
    (p : SPath l s t) (Z : H D Tw m cutoff N ΛP ΛR t) (a : End Z) :
    ((pathFunctor D Tw m cutoff N ΛP ΛR p).map a).hom ≫
      eqToHom (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR p Z) =
    eqToHom (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR p Z) ≫
      ((P).pathFunctor p).map a.hom :=
  functorEquality_square _ _ (factor_pathFunctor_inclusion D Sc m cutoff N ΛP ΛR hP hR p) a

private theorem targetFamily_coefficient_square {l : List (Col I X)} {s : Sector I}
    (p : SPath l s (0,0)) (a : SYM D k) :
    ((P).pathFunctor p).map ((tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a).hom) ≫
      eqToHom (congrArg ((P).pathFunctor p).obj
        (congrArg (fun Z : H D Tw m cutoff N ΛP ΛR (0,0) => Z.obj)
          (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L))) =
    eqToHom (congrArg ((P).pathFunctor p).obj
      (congrArg (fun Z : H D Tw m cutoff N ΛP ΛR (0,0) => Z.obj)
        (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L))) ≫
      ((P).pathFunctor p).map ((tensorVacuumCoefficientAction D Sc m cutoff L ΛP ΛR a).hom) := by
  have h := map_coefficientAtEquality D
    (inclusion D Tw m cutoff N ΛP ΛR (0,0) ⋙ (P).pathFunctor p)
    (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L)
    (tensorVacuumCoefficientAction D Sc m cutoff L ΛP ΛR) a
  simp only [tensorTargetFamilyCoefficientAction, ↓reduceDIte]
  exact h

private theorem vacuumRow_apply (s : List I) {b : Obj (SKM.sig D)}
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = b.endR)
    (p : SPath b.word (0,tensorSourceContent D ΛP ΛR s) (0,0))
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s)
      (tensorTargetFamily D Sc m cutoff ΛP ΛR L) b) :
    tensorVacuumRowProjection D Sc m cutoff ΛP ΛR L hP hR s hEnd p x =
    (x (0,tensorSourceContent D ΛP ΛR s) ⟨(0,0),hEnd⟩ p).hom ≫
      eqToHom (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR p
        (tensorTargetFamily D Sc m cutoff ΛP ΛR L (0,0))) ≫
      eqToHom (congrArg ((P).pathFunctor p).obj
        (congrArg (fun Z : H D Tw m cutoff N ΛP ΛR (0,0) => Z.obj)
          (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L))) := by
  simp only [tensorVacuumRowProjection, MatrixSourceRow.projectionAt,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Linear.homCongr_apply,
    MatrixSourceRow.projection, entryEquiv, LinearEquiv.trans_apply,
    Iso.refl_inv, Category.id_comp]
  exact Category.assoc _ _ _

/-- Projecting the full matrix source-coefficient action gives the same
literal vacuum-path coefficient on the complete ambient row Hom. -/
theorem tensorVacuumRowProjection_coefficient (s : List I) {b : Obj (SKM.sig D)}
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = b.endR)
    (p : SPath b.word (0,tensorSourceContent D ΛP ΛR s) (0,0)) (a : SYM D k)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s)
      (tensorTargetFamily D Sc m cutoff ΛP ΛR L) b) :
    tensorVacuumRowProjection D Sc m cutoff ΛP ΛR L hP hR s hEnd p
      (tensorMatrixCoefficientAction D Sc m cutoff ΛP ΛR L s b a x) =
    tensorVacuumRowProjection D Sc m cutoff ΛP ΛR L hP hR s hEnd p x ≫
      ((P).pathFunctor p).map ((tensorVacuumCoefficientAction D Sc m cutoff L ΛP ΛR a).hom) := by
  have h₁ := factorPath_coefficient_square D Sc m cutoff ΛP ΛR L hP hR p
    (tensorTargetFamily D Sc m cutoff ΛP ΛR L (0,0))
    (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a)
  have h₂ := targetFamily_coefficient_square D Sc m cutoff ΛP ΛR L hP hR p a
  rw [vacuumRow_apply, vacuumRow_apply, tensorMatrixCoefficientAction_apply,
    InducedCategory.comp_hom]
  exact composeSquares _ _ _ _ _ _ h₁ h₂

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
