import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEntryParity
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentCategory

/-! # Actual probe modules on the untruncated old content category
A left module over the prescribed ordinary probe height algebra yields a genuine
old ELV supermodule. Its value at a word is the actual word-idempotent summand;
old arrows act by the checked scalar specialization entries.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k) [Fintype I]
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
variable (ν : List I)
local notation "ha" => probePolynomial_parity (k := k) D m
local notation "C" => ELVOld.OldContentCategory D Sc cut ν
local notation "word" => fun v : C => probeContentWord ν (ELVOld.oldContentWord D Sc cut ν v)

def probeOldWordIdempotent (v : C) : heightAlgebra D Sc a ν.length :=
  probeHeightMk D m Sc ν.length (Hn.wordIdempotent (word v))

theorem probeOldWordIdempotent_parity (v : C) :
    probeOldWordIdempotent D m Sc ν v ∈ heightParity D Sc a ha ν.length 0 := by
  apply probeHeightMk_parity D m Sc ha ν.length
  exact FiniteHomMatrix.single_mem_component _ _ (id_mem _)

variable {B : Type u} [Ring B] [Algebra k B] {GB : ZMod 2 → Submodule k B}
  (M : SuperBimodule
    (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) ν.length) GB)

/-- The actual fixed submodule of the specialized word idempotent. -/
def probeOldWordSubmodule (v : C) : Submodule k M.toSVec where
  carrier := {x | M.lact (probeOldWordIdempotent D m Sc ν v) x = x}
  zero_mem' := map_zero _
  add_mem' {x y} hx hy := by
    change M.lact _ x = x at hx
    change M.lact _ y = y at hy
    change M.lact _ (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' r x hx := by
    change M.lact _ x = x at hx
    change M.lact _ (r • x) = r • x
    rw [map_smul, hx]

theorem probeOldWordSubmodule_odd (v : C) (x : M.toSVec)
    (hx : x ∈ probeOldWordSubmodule D m Sc ν M v) :
    M.toSVec.odd x ∈ probeOldWordSubmodule D m Sc ν M v := by
  have h := SVec.apply_proj_of_mem
    (M.lact_mem 0 _ (probeOldWordIdempotent_parity D m Sc ν v)) 1 x
  change M.lact _ (M.toSVec.odd x) = M.toSVec.odd x
  change M.lact _ x = x at hx
  simpa only [add_zero, SVec.proj_one, hx] using h

/-- A word component of an ordinary probe module, with its inherited grading. -/
def probeOldWordSVec (v : C) : SVec k :=
  SVec.sub M.toSVec (probeOldWordSubmodule D m Sc ν M v)
    (probeOldWordSubmodule_odd D m Sc ν M v)

def probeOldWordEntry {v w : C} (f : v ⟶ w) : heightAlgebra D Sc a ν.length :=
  elvProbeHeightWordEntry D m Sc (word v) (word w) f

theorem probeOldWordEntry_target {v w : C} (f : v ⟶ w) :
    probeOldWordIdempotent D m Sc ν w * probeOldWordEntry D m Sc ν f =
      probeOldWordEntry D m Sc ν f :=
  elvProbeHeightWordEntry_target D m Sc (word v) (word w) f

theorem probeOldWordAction_mem {v w : C} (f : v ⟶ w)
    (x : M.toSVec) (_hx : x ∈ probeOldWordSubmodule D m Sc ν M v) :
    M.lact (probeOldWordEntry D m Sc ν f) x ∈
      probeOldWordSubmodule D m Sc ν M w := by
  have h := congrArg (fun z => M.lact z x) (probeOldWordEntry_target D m Sc ν f)
  change M.lact _ (M.lact _ x) = M.lact _ x
  simpa only [M.lact_mul, SVec.comp_apply] using h

/-- Old morphisms act on actual probe word components by left multiplication. -/
def probeOldWordAction {v w : C} (f : v ⟶ w) :
    probeOldWordSVec D m Sc ν M v ⟶ probeOldWordSVec D m Sc ν M w :=
  SVec.restrictHom (M.lact (probeOldWordEntry D m Sc ν f))
    (probeOldWordAction_mem D m Sc ν M f)

theorem probeOldWordEntry_id (v : C) :
    probeOldWordEntry D m Sc ν (𝟙 v) = probeOldWordIdempotent D m Sc ν v :=
  elvProbeHeightWordEntry_id D m Sc (word v)

theorem probeOldWordEntry_comp {v w z : C} (f : v ⟶ w) (g : w ⟶ z) :
    probeOldWordEntry D m Sc ν (f ≫ g) =
      probeOldWordEntry D m Sc ν g * probeOldWordEntry D m Sc ν f :=
  elvProbeHeightWordEntry_comp D m Sc (word v) (word w) (word z) f g

/-- Restriction of a genuine ordinary probe module to the old ELV content category. -/
def probeOldModuleFunctor : C ⥤ SVec k where
  obj := probeOldWordSVec D m Sc ν M
  map f := probeOldWordAction D m Sc ν M f
  map_id v := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact (probeOldWordEntry D m Sc ν (𝟙 v)) x.val = x.val
    rw [probeOldWordEntry_id]
    exact x.property
  map_comp f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact (probeOldWordEntry D m Sc ν (f ≫ g)) x.val =
      M.lact (probeOldWordEntry D m Sc ν g) (M.lact (probeOldWordEntry D m Sc ν f) x.val)
    rw [probeOldWordEntry_comp, M.lact_mul]
    rfl

instance probeOldModuleFunctor_additive : (probeOldModuleFunctor D m Sc ν M).Additive where
  map_add {v w} f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact (elvProbeHeightWordEntry D m Sc (word v) (word w) (f + g)) x.val =
      M.lact (elvProbeHeightWordEntry D m Sc (word v) (word w) f) x.val +
        M.lact (elvProbeHeightWordEntry D m Sc (word v) (word w) g) x.val
    rw [map_add, map_add]
    rfl

instance probeOldModuleFunctor_linear : (probeOldModuleFunctor D m Sc ν M).Linear k where
  map_smul {v w} f r := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact (elvProbeHeightWordEntry D m Sc (word v) (word w) (r • f)) x.val =
      r • M.lact (elvProbeHeightWordEntry D m Sc (word v) (word w) f) x.val
    rw [map_smul, map_smul]
    rfl

instance probeOldModuleFunctor_super : IsSuperfunctor k (probeOldModuleFunctor D m Sc ν M) where
  map_mem := by
    intro v w p f hf
    exact SVec.restrictHom_mem
      (M.lact_mem p _ (elvProbeHeightWordEntry_probeParity D m Sc (word v) (word w) hf))
      (probeOldWordAction_mem D m Sc ν M f)

/-- The actual probe module, as an even additive linear superfunctor. -/
def probeOldModule : Superfunctor k C (SVec k) :=
  ⟨probeOldModuleFunctor D m Sc ν M⟩

@[simp] theorem probeOldModule_map_apply {v w : C} (f : v ⟶ w)
    (x : probeOldWordSVec D m Sc ν M v) :
    ((show probeOldWordSubmodule D m Sc ν M w from
      (probeOldModule D m Sc ν M).map f x) : M.toSVec) =
      M.lact (probeOldWordEntry D m Sc ν f) x.val := rfl

end OddMath.QuiverHecke

