/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ScalarChange
import StringDiagrams.Interpretation

/-!
# Coefficient change on the SKM presentation

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, (1.7)–(1.14), and Definition 2.2. This constructs the
forward presentation comparison required by `GroundRingDescent.md`, §7.
The datum, weight group and all inverse-entry generators are unchanged.
No injectivity, flatness or nondegeneracy assumption is made.
-/

noncomputable section

namespace OddMath.SKM.ScalarChange

open CategoryTheory StringDiagrams Presentation

universe u v w w' u₀ u₁ u₂

variable {R : Type w} {S : Type w'} [CommRing R] [CommRing S] (f : R →+* S)

/-- Restrict the Hom scalar actions along a specified ring homomorphism.
This is deliberately not a global instance. -/
@[instance_reducible]
def restrictedLinear (C : Type*) [Category C] [Preadditive C] [Linear S C] :
    Linear R C where
  homModule A B := Module.compHom (A ⟶ B) f
  smul_comp A B C r g h := CategoryTheory.Linear.smul_comp A B C (f r) g h
  comp_smul A B C g r h := CategoryTheory.Linear.comp_smul A B C g (f r) h

variable {T : Signature.{u₀, u₁, u₂}} {a b c : Obj T}

/-- The free additive-category lift changes coefficients without changing diagrams. -/
def coeffFunctor : Free R (Obj T) ⥤ Free S (Obj T) :=
  letI := restrictedLinear f (Free S (Obj T))
  freeLift R (Free.embedding S (Obj T))

/-- Coefficient change on raw linear diagrams, semilinear along `f`. -/
def coeff : LinDiagram R a b →ₛₗ[f] LinDiagram S a b := by
  letI := restrictedLinear f (Free S (Obj T))
  exact {
    toFun := (coeffFunctor f).map
    map_add' := fun _ _ => (freeLift R (Free.embedding S (Obj T))).map_add
    map_smul' := fun r x => (freeLift R (Free.embedding S (Obj T))).map_smul r x }

@[simp] theorem coeff_single (g : a ⟶ b) (r : R) :
    coeff f (Finsupp.single g r) = Finsupp.single g (f r) := by
  let := restrictedLinear f (Free S (Obj T))
  change (freeLift R (Free.embedding S (Obj T))).map _ = _
  rw [freeLift_map_single]
  change f r • Finsupp.single g (1 : S) = Finsupp.single g (f r)
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

@[simp] theorem coeff_of (g : a ⟶ b) :
    coeff f (LinDiagram.of g) = LinDiagram.of g := by
  change coeff f (Finsupp.single g 1) = Finsupp.single g 1
  rw [coeff_single, map_one]

@[simp] theorem coeff_zero : coeff f (0 : LinDiagram R a b) = 0 := (coeff f).map_zero

@[simp] theorem coeff_add (x y : LinDiagram R a b) :
    coeff f (x + y) = coeff f x + coeff f y := (coeff f).map_add x y

@[simp] theorem coeff_sub (x y : LinDiagram R a b) :
    coeff f (x - y) = coeff f x - coeff f y := (coeff f).map_sub x y

@[simp] theorem coeff_neg (x : LinDiagram R a b) :
    coeff f (-x) = -coeff f x := (coeff f).map_neg x

@[simp] theorem coeff_smul (r : R) (x : LinDiagram R a b) :
    coeff f (r • x) = f r • coeff f x := (coeff f).map_smulₛₗ r x

@[simp] theorem coeff_sum {J : Type*} (s : Finset J) (x : J → LinDiagram R a b) :
    coeff f (∑ j ∈ s, x j) = ∑ j ∈ s, coeff f (x j) := map_sum (coeff f) x s

@[simp] theorem coeff_comp (x : LinDiagram R a b) (y : LinDiagram R b c) :
    coeff f (x ≫ y) = coeff f x ≫ coeff f y := (coeffFunctor f).map_comp x y

@[simp] theorem coeff_id (a : Obj T) :
    coeff f (𝟙 (Free.of R a)) = 𝟙 (Free.of S a) := (coeffFunctor f).map_id _

@[simp] theorem coeff_whisker (x : LinDiagram R a b) (l : Obj T) (r : List T.Colour)
    (h : a.WhiskerOK l r) :
    coeff f (LinDiagram.whisker x l r h) = LinDiagram.whisker (coeff f x) l r h := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [LinDiagram.whisker_add, map_add, hx, hy, map_add, LinDiagram.whisker_add]
  | single g t =>
    erw [LinDiagram.whisker_single, coeff_single, coeff_single, LinDiagram.whisker_single]

@[simp] theorem coeff_whisk (x : LinDiagram R a b) (l : Obj T) (r : List T.Colour) :
    coeff f (LinDiagram.whisk x l r) = LinDiagram.whisk (coeff f x) l r := by
  unfold LinDiagram.whisk
  split_ifs <;> simp

@[simp] theorem coeff_cast {a' b' : Obj T} (x : LinDiagram R a b)
    (ha : a = a') (hb : b = b') :
    coeff f (LinDiagram.cast x ha hb) = LinDiagram.cast (coeff f x) ha hb := by
  subst ha hb
  simp only [LinDiagram.cast_rfl]

@[simp] theorem map_zsign (p : ZMod 2) : f (zsign R p) = zsign S p := by
  unfold zsign
  split_ifs <;> simp

/-- Signed interchange commutes with arbitrary coefficient change. -/
theorem coeff_interchange (x : InterchangeData T) (hx : x.Valid) :
    coeff f (InterchangeData.rel R hx) = InterchangeData.rel S hx := by
  simp [InterchangeData.rel]

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) (Sc : Scalars D R)

/-- Every defining relation, including both products for each augmented
inverse matrix, specializes to the relation with the same label. -/
theorem coeff_relation (r : Rel D) :
    coeff f (relation D Sc r) = relation D (scalars D f Sc) r := by
  classical
  cases r <;> simp [relation, dg, idg, scalars] <;> split_ifs <;> simp

private theorem coeff_whisk_mem_of_eq (r : (pres D (scalars D f Sc)).AllRel)
    (x : LinDiagram R r.dom r.cod) (hx : coeff f x = r.rel)
    (l : Obj (sig D)) (v : List (sig D).Colour) (h : r.dom.WhiskerOK l v) :
    coeff f (LinDiagram.whisker x l v h) ∈
      (pres D (scalars D f Sc)).ideal (r.dom.whisker l v) (r.cod.whisker l v) := by
  rw [coeff_whisker, hx]
  exact (pres D (scalars D f Sc)).whisker_rel_mem_ideal r l v h

/-- Every horizontally contextualized user or interchange relation maps
into the target ideal. -/
theorem coeff_whiskRel_mem (r : (pres D Sc).AllRel)
    (l : Obj (sig D)) (v : List (sig D).Colour) (h : r.dom.WhiskerOK l v) :
    coeff f (LinDiagram.whisker r.rel l v h) ∈
      (pres D (scalars D f Sc)).ideal (r.dom.whisker l v) (r.cod.whisker l v) := by
  cases r with
  | user r =>
    exact coeff_whisk_mem_of_eq f D Sc (.user r) _ (coeff_relation f D Sc r) l v h
  | interchange x hx =>
    exact coeff_whisk_mem_of_eq f D Sc (.interchange x hx) _
      (coeff_interchange f x hx) l v h

/-- Arbitrary linear pre- and post-compositions of contextual relations
remain in the target ideal. -/
theorem coeff_gen_mem {a b : Obj (sig D)} {x : LinDiagram R a b}
    (hx : (pres D Sc).IdealGen x) : coeff f x ∈ (pres D (scalars D f Sc)).ideal a b := by
  obtain ⟨r, l, v, h, pre, post⟩ := hx
  rw [coeff_comp, coeff_comp]
  exact (pres D (scalars D f Sc)).comp_mem_ideal _
    ((pres D (scalars D f Sc)).mem_ideal_comp (coeff_whiskRel_mem f D Sc r l v h) _)

/-- Coefficient change preserves the entire vertical and horizontal
contextual ideal, not just its generating relations. -/
theorem coeff_mem_ideal {a b : Obj (sig D)} {x : LinDiagram R a b}
    (hx : x ∈ (pres D Sc).ideal a b) : coeff f x ∈ (pres D (scalars D f Sc)).ideal a b := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact coeff_gen_mem f D Sc hx
  | zero => rw [coeff_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [coeff_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [coeff_smul]; exact Submodule.smul_mem _ (f r) hx

/-- The induced semilinear map on the presented SKM Hom modules. -/
def homMap (a b : Obj (sig D)) :
    ((pres D Sc).obj a ⟶ (pres D Sc).obj b) →ₛₗ[f]
      ((pres D (scalars D f Sc)).obj a ⟶ (pres D (scalars D f Sc)).obj b) where
  toFun x := Quot.lift (fun y : LinDiagram R a b => (pres D (scalars D f Sc)).lin (coeff f y))
    (fun y z h => by
      have h' : (pres D Sc).homRel y z := by
        rwa [HomRel.compClosure_eq_self] at h
      rw [lin_eq_iff, ← coeff_sub]
      exact coeff_mem_ideal f D Sc h') x
  map_add' x y := by
    obtain ⟨x, rfl⟩ := (pres D Sc).lin_surjective x
    obtain ⟨y, rfl⟩ := (pres D Sc).lin_surjective y
    rw [← lin_add]
    change (pres D (scalars D f Sc)).lin (coeff f (x + y)) = _
    rw [coeff_add, lin_add]
    rfl
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := (pres D Sc).lin_surjective x
    rw [← lin_smul]
    change (pres D (scalars D f Sc)).lin (coeff f (r • x)) = _
    rw [coeff_smul, lin_smul]
    rfl

@[simp] theorem homMap_lin {a b : Obj (sig D)} (x : LinDiagram R a b) :
    homMap f D Sc a b ((pres D Sc).lin x) = (pres D (scalars D f Sc)).lin (coeff f x) := rfl

/-- Every raw diagram, hence every named generator and inverse entry,
is carried to the diagram with exactly the same label. -/
@[simp] theorem homMap_diag {a b : Obj (sig D)} (x : a ⟶ b) :
    homMap f D Sc a b ((pres D Sc).diag x) = (pres D (scalars D f Sc)).diag x := by
  simp only [diag, homMap_lin, coeff_of]

@[simp] theorem homMap_id (a : Obj (sig D)) :
    homMap f D Sc a a (𝟙 _) = 𝟙 _ := by
  rw [← lin_id, homMap_lin, coeff_id, lin_id]

@[simp] theorem homMap_comp {a b c : Obj (sig D)}
    (x : (pres D Sc).obj a ⟶ (pres D Sc).obj b)
    (y : (pres D Sc).obj b ⟶ (pres D Sc).obj c) :
    homMap f D Sc a c (x ≫ y) = homMap f D Sc a b x ≫ homMap f D Sc b c y := by
  obtain ⟨x, rfl⟩ := (pres D Sc).lin_surjective x
  obtain ⟨y, rfl⟩ := (pres D Sc).lin_surjective y
  rw [← lin_comp, homMap_lin, coeff_comp, lin_comp, homMap_lin, homMap_lin]

/-- The coefficient-change functor on the actual presented category. -/
def presentationFunctor : (pres D Sc).Presented ⥤ (pres D (scalars D f Sc)).Presented where
  obj a := (pres D (scalars D f Sc)).obj a.as
  map {a b} := homMap f D Sc a.as b.as
  map_id a := homMap_id f D Sc a.as
  map_comp x y := homMap_comp f D Sc x y

instance presentationFunctor_additive : (presentationFunctor f D Sc).Additive where
  map_add := (homMap f D Sc _ _).map_add _ _

/-- Coefficient change commutes with arbitrary horizontal contexts,
including the zero convention on incompatible boundaries. -/
@[simp] theorem homMap_whisk {a b : Obj (sig D)}
    (x : (pres D Sc).obj a ⟶ (pres D Sc).obj b)
    (l : Obj (sig D)) (v : List (sig D).Colour) :
    homMap f D Sc _ _ ((pres D Sc).whisk x l v) =
      (pres D (scalars D f Sc)).whisk (homMap f D Sc a b x) l v := by
  obtain ⟨x, rfl⟩ := (pres D Sc).lin_surjective x
  simp only [whisk_lin, homMap_lin, coeff_whisk]

@[simp] theorem homMap_smul {a b : Obj (sig D)} (r : R)
    (x : (pres D Sc).obj a ⟶ (pres D Sc).obj b) :
    homMap f D Sc a b (r • x) = f r • homMap f D Sc a b x :=
  (homMap f D Sc a b).map_smulₛₗ r x

/-- The formula includes all seven generator shapes: dot, crossing,
right cup, right cap, left crossing, and both inverse-matrix entry families. -/
@[simp] theorem homMap_layer (L : Layer (sig D)) (hv : L.Valid)
    {a b : Obj (sig D)} (ha : L.dom = a) (hb : L.cod = b) :
    homMap f D Sc a b ((pres D Sc).layer L hv ha hb) =
      (pres D (scalars D f Sc)).layer L hv ha hb :=
  homMap_diag f D Sc _

/-- The totalized normal-form diagram formula also preserves invalid
layer lists, which denote zero. -/
@[simp] theorem homMap_cl (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    homMap f D Sc _ _ (cl D Sc μ s t ls) = cl D (scalars D f Sc) μ s t ls := by
  classical
  unfold cl
  split_ifs <;> simp

/-- Supplied normalized left cups specialize with their original weight
and their prescribed unit, on both sides of the height test. -/
@[simp] theorem homMap_etaP (cs : CScalars Sc) (i : I) (μ : X) :
    homMap f D Sc _ _ (etaP cs i μ) = etaP (cScalars D f cs) i μ := by
  unfold etaP
  split_ifs <;> simp [cScalars]

/-- The inverse normalization unit in a left cap is preserved as well. -/
@[simp] theorem homMap_epsP (cs : CScalars Sc) (i : I) (μ : X) :
    homMap f D Sc _ _ (epsP cs i μ) = epsP (cScalars D f cs) i μ := by
  unfold epsP
  split_ifs <;> simp [cScalars]

end OddMath.SKM.ScalarChange
