import OddMath.QuiverHecke.SwappedAssembly.SupportedFactorPaths
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Generators

/-! # Chosen generator entries on supported sectors

The matrix-entry attachment of F4/(A1) to the chosen OLD/ELV factor
families in `SwappedActionAssembly.md`. Every `ProbeReservoir.GenImage`
restricts at its original formal endpoints. The path comparison is the
computed comparison of the chosen factor fields, with no supplied
support premise. Supernatural entries retain their generator parity.
This transport does not assert the remaining central inverse or the
complete presentation relations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance generatorHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

/-- The included path object is exactly the chosen factor path object. -/
theorem factor_path_obj {w : List (Col I X)} {s t : Sector I} (p : SPath w s t)
    (Z : H D Sc' m cutoff bound ΛP ΛR t) :
    ((pathFunctor D Sc' m cutoff bound ΛP ΛR p).obj Z).obj =
      ((P).pathFunctor p).obj Z.obj :=
  congrArg (fun F => F.obj Z) (factor_pathFunctor_inclusion D Sc m cutoff bound ΛP ΛR hP hR p)

/-- Matrix entries on the supported sectors, with the same formal paths as the factor. -/
def GeneratorEntry (g : SKM.Shape I) (ν : X) :=
  ∀ {t s : Sector I} (p : SPath (wd D ν g.dom) t s) (q : SPath (wd D ν g.cod) t s)
    (Z : H D Sc' m cutoff bound ΛP ΛR s),
      (pathFunctor D Sc' m cutoff bound ΛP ΛR p).obj Z ⟶
        (pathFunctor D Sc' m cutoff bound ΛP ΛR q).obj Z

/-- Restrict an existing factor matrix entry, using the computed path charts. -/
def restrictGenImage {g : SKM.Shape I} {ν : X} (e : (P).GenImage g ν) :
    GeneratorEntry D Sc m cutoff bound ΛP ΛR g ν := fun p q Z =>
  ⟨eqToHom (factor_path_obj D Sc m cutoff bound ΛP ΛR hP hR p Z) ≫ e p q Z.obj ≫
    eqToHom (factor_path_obj D Sc m cutoff bound ΛP ΛR hP hR q Z).symm⟩

/-- The restricted family is supernatural whenever its literal factor family is. -/
theorem restrictGenImage_supernatural {g : SKM.Shape I} {ν : X} (e : (P).GenImage g ν)
    {t s : Sector I} (p : SPath (wd D ν g.dom) t s) (q : SPath (wd D ν g.cod) t s)
    {a : ZMod 2} (he : IsSupernatural k a (fun Z => e p q Z)) :
    IsSupernatural k a (fun Z => restrictGenImage D Sc m cutoff bound ΛP ΛR hP hR e p q Z) := by
  let := inclusion_additive D Sc' m cutoff bound ΛP ΛR s
  let := inclusion_linear D Sc' m cutoff bound ΛP ΛR s
  let := inclusion_super D Sc' m cutoff bound ΛP ΛR s
  have hi := he.whiskerLeft (inclusion D Sc' m cutoff bound ΛP ΛR s)
  have hr := IsSupernatural.of_eq_conj
    (factor_pathFunctor_inclusion D Sc m cutoff bound ΛP ΛR hP hR p)
    (factor_pathFunctor_inclusion D Sc m cutoff bound ΛP ΛR hP hR q) hi
    (fun Z => (restrictGenImage D Sc m cutoff bound ΛP ΛR hP hR e p q Z).hom)
    (factor_path_obj D Sc m cutoff bound ΛP ΛR hP hR p)
    (fun Z => (factor_path_obj D Sc m cutoff bound ΛP ΛR hP hR q Z).symm)
    (fun _ => rfl)
  exact ⟨fun Z => hr.mem Z, fun hf => InducedCategory.hom_ext (hr.naturality hf)⟩

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
