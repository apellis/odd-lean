import OddMath.QuiverHecke.SwappedAssembly.SupportedGeneratorEntries

/-! # Matrix modules of supported path functors

SwappedActionAssembly F4/(A1) and the matrix construction of Brundan–Ellis
Definition 1.5. The canonical full inclusions and computed chosen-factor
path charts identify the supported matrix modules with the existing
chosen factor matrix modules. The generator entries retain their literal
components under these identifications.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance matrixHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

/-- A supported matrix entry has the same Hom module as its chosen ambient entry. -/
def entryEquiv {w : List (Col I X)} {s t : Sector I} (p : SPath w s t)
    (G : H D Sc' m cutoff bound ΛP ΛR s) (Z : H D Sc' m cutoff bound ΛP ΛR t) :
    (G ⟶ (pathFunctor D Sc' m cutoff bound ΛP ΛR p).obj Z) ≃ₗ[k]
      (G.obj ⟶ ((P).pathFunctor p).obj Z.obj) :=
  (InducedCategory.homLinearEquiv (R := k)).trans
    (Linear.homCongr k (Iso.refl G.obj)
      (eqToIso (factor_path_obj D Sc m cutoff bound ΛP ΛR hP hR p Z)))

/-- Matrix modules with literal supported path targets and their original sector indices. -/
def matrixModule (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
    (ΛP ΛR : X)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (a : Obj (SKM.sig D)) : Type (u + 1) :=
  ∀ (s : Sector I)
    (t : {t : Sector I // (ΛP - contentWeight D t.1) + (-ΛR + contentWeight D t.2) = a.endR})
    (p : SPath a.word s t.1),
    Gs s ⟶ (pathFunctor D (parameterTwist D Sc) m cutoff bound ΛP ΛR p).obj (Ys t.1)

instance matrixModule_addCommGroup (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ)
    (bound : ℕ) (ΛP ΛR : X)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (a : Obj (SKM.sig D)) : AddCommGroup (matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys a) := by
  unfold matrixModule
  infer_instance

instance matrixModule_module (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ)
    (bound : ℕ) (ΛP ΛR : X)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (a : Obj (SKM.sig D)) : Module k (matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys a) := by
  unfold matrixModule
  infer_instance

/-- Entrywise full inclusion identifies the supported and chosen-factor matrix modules. -/
def matrixEquiv (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
    (ΛP ΛR : X) (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
    (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (a : Obj (SKM.sig D)) :
    matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys a ≃ₗ[k]
      (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).Mod
        (fun s => (Gs s).obj) (fun s => (Ys s).obj) a where
  toFun x := fun s t p => entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p (Gs s) (Ys t.1) (x s t p)
  invFun x := fun s t p => (entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p (Gs s) (Ys t.1)).symm (x s t p)
  left_inv x := by funext s t p; exact (entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p (Gs s) (Ys t.1)).left_inv _
  right_inv x := by funext s t p; exact (entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p (Gs s) (Ys t.1)).right_inv _
  map_add' x y := by
    funext s t p
    exact (entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p (Gs s) (Ys t.1)).map_add _ _
  map_smul' r x := by
    funext s t p
    exact (entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p (Gs s) (Ys t.1)).map_smul r _

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
