/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RootCover
import OddMath.SKM.MoreGenerators
import StringDiagrams.LayerMap.Generators
import StringDiagrams.Biadjunction.Zigzag
import StringDiagrams.Transport

/-! # The projection functor from the root cover

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5 and (2.6):
the first projection `X × (I →₀ ℤ) → X` sends the roots `(αᵢ, eᵢ)` of `RootCover.rootCover D` to
the roots of `D` and is compatible with the coroots. It therefore maps every region, strand,
generator and defining relation of the presentation of the cover, with the same parameters
(`coverScalars`), to the corresponding one of `D`. This gives the presentation functor
`projectionFunctor : (pres (rootCover D) (coverScalars D Sc)).Presented ⥤ (pres D Sc).Presented`
and its maps `homMap` on Hom spaces at a fixed right region.

This is the direction used to compare the 2-categories of `D` and of its root cover (Brundan–
Wang–Webster, arXiv:2505.22929v2, Remark 2.4). With dependent simple roots there is no map in
the other direction. Whether `homMap` is bijective is not addressed here.
-/
noncomputable section
namespace OddMath.SKM.RootCover
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
local notation "Dc" => rootCover D

@[simp] theorem fst_sh (l : Letter I) : (sh Dc l).1 = sh D l := by
  unfold sh
  split_ifs <;> rfl

@[simp] theorem fst_wt (ν : X × (I →₀ ℤ)) (t : List (Letter I)) :
    (wt Dc ν t).1 = wt D ν.1 t := by
  induction t with
  | nil => rfl
  | cons l t ih => simp only [wt_cons, Prod.fst_add, fst_sh, ih]

/-- Keep the strand and project its right region. -/
def colour (c : Col I (X × (I →₀ ℤ))) : Col I X := ⟨c.l, c.r.1⟩

@[simp] theorem word (ν : X × (I →₀ ℤ)) (t : List (Letter I)) :
    (wd Dc ν t).map colour = wd D ν.1 t := by
  induction t with
  | nil => rfl
  | cons l t ih => simp [colour, ih]

/-- The first projection as a map of the complete SKM signature. -/
def projection : SigMap (sig Dc) (sig D) where
  region ν := ν.1
  colour := colour
  colourSrc c := by
    change sh D c.l + c.r.1 = (sh Dc c.l + c.r).1
    rw [Prod.fst_add, fst_sh]
  colourTgt _ := rfl
  gen g := (g.1, g.2.1)
  dom g := (word D g.2 g.1.dom).symm
  cod g := (word D g.2 g.1.cod).symm
  left g := (fst_wt D g.2 g.1.dom).symm
  right _ := rfl

theorem projection_odd (g : (sig Dc).Gen) :
    (sig D).odd ((projection D).gen g) = (sig Dc).odd g := by
  change decide (g.1.parity D = 1) = decide (g.1.parity Dc = 1)
  cases g.1 <;> rfl

@[simp] theorem projection_ob (ν : X × (I →₀ ℤ)) (t : List (Letter I)) :
    (projection D).obj (ob Dc ν t) = ob D ν.1 t := by
  apply Obj.ext <;>
    first
    | exact fst_wt D ν t
    | exact word D ν t
    | exact (fst_wt D ν t).symm
    | exact (word D ν t).symm

@[simp] theorem projection_lay (ν : X × (I →₀ ℤ)) (u : List (Letter I)) (g : Shape I)
    (v : List (Letter I)) :
    (projection D).layer (lay Dc ν u g v) = lay D ν.1 u g v := by
  simp [SigMap.layer, projection, lay, fst_wt, word]

/-- The same free diagram with all regions projected, at normal-form boundaries. -/
def diagram {ν : X × (I →₀ ℤ)} {t t' : List (Letter I)} (f : ob Dc ν t ⟶ ob Dc ν t') :
    ob D ν.1 t ⟶ ob D ν.1 t' :=
  Diagram.cast ((projection D).toLayerMap.map f) (projection_ob D ν t) (projection_ob D ν t')

@[simp] theorem diagram_mkD (ν : X × (I →₀ ℤ)) {t t' : List (Letter I)}
    (ls : List (LayerData I)) (h : SChain t ls t') :
    diagram D (mkD Dc ν ls h) = mkD D ν.1 ls h := by
  apply Diagram.ext
  change ((layList Dc ν ls).map (projection D).layer) = _
  simp only [layers_mkD, layList, List.map_map]
  apply List.map_congr_left
  intro x _
  exact projection_lay D ν x.1 x.2.1 x.2.2

@[simp] theorem diagram_id (ν : X × (I →₀ ℤ)) (t : List (Letter I)) :
    diagram D (𝟙 (ob Dc ν t)) = 𝟙 _ := rfl

variable {k : Type w} [CommRing k] (Sc : Scalars D k)
local notation "Scc" => coverScalars D Sc

/-- Project the free linear Hom, keeping the signed boundary words. -/
def linear (ν : X × (I →₀ ℤ)) (t t' : List (Letter I)) :
    LinDiagram k (ob Dc ν t) (ob Dc ν t') →ₗ[k] LinDiagram k (ob D ν.1 t) (ob D ν.1 t') :=
  Finsupp.lmapDomain k k (diagram D)

@[simp] theorem linear_of (ν : X × (I →₀ ℤ)) {t t' : List (Letter I)} (f : ob Dc ν t ⟶ ob Dc ν t') :
    linear (k := k) D ν t t' (LinDiagram.of f) = LinDiagram.of (diagram D f) :=
  Finsupp.mapDomain_single

@[simp] theorem linear_sub (ν : X × (I →₀ ℤ)) (t t' : List (Letter I))
    (f g : LinDiagram k (ob Dc ν t) (ob Dc ν t')) :
    linear D ν t t' (f - g) = linear D ν t t' f - linear D ν t t' g :=
  (linear D ν t t').map_sub f g

@[simp] theorem linear_add (ν : X × (I →₀ ℤ)) (t t' : List (Letter I))
    (f g : LinDiagram k (ob Dc ν t) (ob Dc ν t')) :
    linear D ν t t' (f + g) = linear D ν t t' f + linear D ν t t' g :=
  (linear D ν t t').map_add f g

@[simp] theorem linear_neg (ν : X × (I →₀ ℤ)) (t t' : List (Letter I))
    (f : LinDiagram k (ob Dc ν t) (ob Dc ν t')) :
    linear D ν t t' (-f) = -linear D ν t t' f :=
  (linear D ν t t').map_neg f

@[simp] theorem linear_smul (ν : X × (I →₀ ℤ)) (t t' : List (Letter I)) (a : k)
    (f : LinDiagram k (ob Dc ν t) (ob Dc ν t')) :
    linear D ν t t' (a • f) = a • linear D ν t t' f :=
  (linear D ν t t').map_smul a f

@[simp] theorem linear_sum (ν : X × (I →₀ ℤ)) (t t' : List (Letter I)) {ι : Type*}
    (s : Finset ι)
    (f : ι → LinDiagram k (ob Dc ν t) (ob Dc ν t')) :
    linear D ν t t' (∑ i ∈ s, f i) = ∑ i ∈ s, linear D ν t t' (f i) :=
  map_sum (linear D ν t t') f s

@[simp] theorem linear_zero (ν : X × (I →₀ ℤ)) (t t' : List (Letter I)) :
    linear (k := k) D ν t t' 0 = 0 := (linear D ν t t').map_zero

@[simp] theorem linear_ite (ν : X × (I →₀ ℤ)) (t t' : List (Letter I)) (p : Prop)
    [Decidable p]
    (f g : LinDiagram k (ob Dc ν t) (ob Dc ν t')) :
    linear D ν t t' (if p then f else g) =
      if p then linear D ν t t' f else linear D ν t t' g := by
  split_ifs <;> rfl

/-- Project all relation labels, retaining both inverse products and finite windows. -/
def relationLabel : Rel Dc → Rel D
  | .quadEq i ν => .quadEq i ν.1
  | .quadZero i j ν hij hd => .quadZero i j ν.1 hij (by simpa using hd)
  | .quadNe i j ν hij hd => .quadNe i j ν.1 hij (by simpa using hd)
  | .slideL i j ν hij => .slideL i j ν.1 hij
  | .slideLEq i ν => .slideLEq i ν.1
  | .slideR i j ν hij => .slideR i j ν.1 hij
  | .slideREq i ν => .slideREq i ν.1
  | .braid i j l ν h => .braid i j l ν.1 h
  | .braidEq i j ν hij => .braidEq i j ν.1 hij
  | .zigE i ν => .zigE i ν.1
  | .zigF i ν => .zigF i ν.1
  | .invNe₁ i j ν hij => .invNe₁ i j ν.1 hij
  | .invNe₂ i j ν hij => .invNe₂ i j ν.1 hij
  | .invP₁ i ν hh => .invP₁ i ν.1 (by simpa using hh)
  | .invP₂ i ν hh => .invP₂ i ν.1 (by simpa using hh)
  | .invP₃ i ν m hm => .invP₃ i ν.1 m (by simpa using hm)
  | .invP₄ i ν n hn => .invP₄ i ν.1 n (by simpa using hn)
  | .invP₅ i ν m n hm hn => .invP₅ i ν.1 m n (by simpa using hm) (by simpa using hn)
  | .invM₁ i ν hh => .invM₁ i ν.1 (by simpa using hh)
  | .invM₂ i ν hh => .invM₂ i ν.1 (by simpa using hh)
  | .invM₃ i ν m hm => .invM₃ i ν.1 m (by simpa using hm)
  | .invM₄ i ν n hn => .invM₄ i ν.1 n (by simpa using hn)
  | .invM₅ i ν m n hm hn => .invM₅ i ν.1 m n (by simpa using hm) (by simpa using hn)
  | .dcupZero i ν n hn => .dcupZero i ν.1 n (by simpa using hn)
  | .dcapZero i ν n hn => .dcapZero i ν.1 n (by simpa using hn)
  | .zInt (.sq i ν) => .zInt (.sq i ν.1)
  | .zInt (.right i ν n hn) => .zInt (.right i ν.1 n (by simpa using hn))
  | .zInt (.left i ν n hn) => .zInt (.left i ν.1 n (by simpa using hn))

@[simp] theorem relationLabel_dom (r : Rel Dc) : (relationLabel D r).dom = r.dom := by
  cases r <;> (try cases ‹ZBase _›) <;> rfl
@[simp] theorem relationLabel_cod (r : Rel Dc) : (relationLabel D r).cod = r.cod := by
  cases r <;> (try cases ‹ZBase _›) <;> rfl
@[simp] theorem relationLabel_region (r : Rel Dc) : (relationLabel D r).ν = r.ν.1 := by
  cases r <;> (try cases ‹ZBase _›) <;> rfl

/-- Every defining linear relation maps to the identical relation at the projected region. -/
theorem linear_relation (r : Rel Dc) :
    HEq (linear D r.ν r.dom r.cod (relation Dc Scc r)) (relation D Sc (relationLabel D r)) := by
  cases r
  case zInt b =>
    cases b <;> exact heq_of_eq (by
      simp only [relationLabel, Rel.ν, Rel.dom, Rel.cod, relation_zInt_of_scalars, linear_zero])
  all_goals apply heq_of_eq
  all_goals dsimp only [Rel.ν, Rel.dom, Rel.cod, relationLabel]
  all_goals
    simp [relation, dg, idg, linear_sub, linear_add, linear_neg,
      linear_ite, linear_zero, linear_of, diagram_mkD, diagram_id,
      coverScalars, rootCover_dn, rootCover_parity]

/-- The normal-form linear map is the signature map followed by its boundary casts. -/
theorem linear_eq_cast (ν : X × (I →₀ ℤ)) (s t : List (Letter I))
    (f : LinDiagram k (ob Dc ν s) (ob Dc ν t)) :
    linear D ν s t f = LinDiagram.cast ((projection D).toLayerMap.lin f)
      (projection_ob D ν s) (projection_ob D ν t) := by
  change Finsupp.mapDomain (diagram D) f =
    Finsupp.mapDomain (fun g => Diagram.cast g (projection_ob D ν s) (projection_ob D ν t))
      (Finsupp.mapDomain (projection D).toLayerMap.map f)
  exact Finsupp.mapDomain_comp (v := f) (f := (projection D).toLayerMap.map)
    (g := fun g => Diagram.cast g (projection_ob D ν s) (projection_ob D ν t))

private theorem lin_eq_zero_of_cast {a b a' b' : Obj (sig D)}
    (f : LinDiagram k a b) (ha : a = a') (hb : b = b')
    (hf : (pres D Sc).lin (LinDiagram.cast f ha hb) = 0) :
    (pres D Sc).lin f = 0 := by
  subst ha hb
  simpa only [LinDiagram.cast_rfl] using hf

private theorem lin_eq_zero_of_heq {a b a' b' : Obj (sig D)}
    (ha : a = a') (hb : b = b') (f : LinDiagram k a b) (g : LinDiagram k a' b')
    (h : HEq f g) (hg : (pres D Sc).lin g = 0) : (pres D Sc).lin f = 0 := by
  subst ha hb
  cases h
  exact hg

/-- Every projected defining relation vanishes in the presentation of `D`. -/
theorem linear_relation_zero (r : Rel Dc) :
    (pres D Sc).lin (linear D r.ν r.dom r.cod (relation Dc Scc r)) = 0 := by
  have hz : (pres D Sc).lin (relation D Sc (relationLabel D r)) = 0 :=
    (pres D Sc).lin_rel_self (relationLabel D r)
  exact lin_eq_zero_of_heq D Sc
    (by simp only [relationLabel_region, relationLabel_dom])
    (by simp only [relationLabel_region, relationLabel_cod])
    _ _ (linear_relation D Sc r) hz

/-- The literal unweighted signature interpretation kills all user relations. -/
theorem projection_relation (r : Rel Dc) :
    (freeLift k ((projection D).toLayerMap.toPresented (pres D Sc) (fun _ => 1))).map
      ((pres Dc Scc).rel r) = 0 := by
  rw [LayerMap.freeLift_toPresented_one]
  apply lin_eq_zero_of_cast D Sc _ (projection_ob D r.ν r.dom) (projection_ob D r.ν r.cod)
  rw [← linear_eq_cast]
  exact linear_relation_zero D Sc r

/-- The complete SKM presentation functor projecting the cover onto `D`. -/
def projectionFunctor : (pres Dc Scc).Presented ⥤ (pres D Sc).Presented :=
  (projection D).lift (pres Dc Scc) (projection_odd D) (projection_relation D Sc)

instance projectionFunctor_additive : (projectionFunctor D Sc).Additive := by
  unfold projectionFunctor
  infer_instance

instance projectionFunctor_linear : (projectionFunctor D Sc).Linear k := by
  unfold projectionFunctor
  infer_instance

@[simp] theorem projectionFunctor_obj (a : Obj (sig Dc)) :
    (projectionFunctor D Sc).obj ((pres Dc Scc).obj a) =
      (pres D Sc).obj ((projection D).obj a) := rfl

/-- All generators, including the inverse entries, retain their diagrams and coefficients. -/
theorem projectionFunctor_diag {a b : Obj (sig Dc)} (f : a ⟶ b) :
    (projectionFunctor D Sc).map ((pres Dc Scc).diag f) =
      (pres D Sc).diag ((projection D).toLayerMap.map f) := by
  simp only [projectionFunctor, SigMap.lift_diag, Diagram.weight_one, one_smul]

/-- The linear Hom map at a fixed right region of the cover, keeping the boundary words. -/
def homMap (ν : X × (I →₀ ℤ)) (s t : List (Letter I)) :
    ((pres Dc Scc).obj (ob Dc ν s) ⟶ (pres Dc Scc).obj (ob Dc ν t)) →ₗ[k]
      ((pres D Sc).obj (ob D ν.1 s) ⟶ (pres D Sc).obj (ob D ν.1 t)) :=
  ((pres D Sc).castLinearEquiv (projection_ob D ν s) (projection_ob D ν t)).toLinearMap.comp
    ((projectionFunctor D Sc).mapLinearMap k)

theorem homMap_apply (ν : X × (I →₀ ℤ)) (s t : List (Letter I))
    (f : (pres Dc Scc).obj (ob Dc ν s) ⟶ (pres Dc Scc).obj (ob Dc ν t)) :
    homMap D Sc ν s t f = (pres D Sc).castHom (projection_ob D ν s) (projection_ob D ν t)
      ((projectionFunctor D Sc).map f) := rfl

@[simp] theorem homMap_id (ν : X × (I →₀ ℤ)) (s : List (Letter I)) :
    homMap D Sc ν s s (𝟙 _) = 𝟙 _ := by
  exact (congrArg ((pres D Sc).castHom (projection_ob D ν s) (projection_ob D ν s))
    ((projectionFunctor D Sc).map_id _)).trans ((pres D Sc).castHom_id _)

theorem homMap_comp (ν : X × (I →₀ ℤ)) {s t r : List (Letter I)}
    (f : (pres Dc Scc).obj (ob Dc ν s) ⟶ (pres Dc Scc).obj (ob Dc ν t))
    (g : (pres Dc Scc).obj (ob Dc ν t) ⟶ (pres Dc Scc).obj (ob Dc ν r)) :
    homMap D Sc ν s r (f ≫ g) = homMap D Sc ν s t f ≫ homMap D Sc ν t r g := by
  exact (congrArg ((pres D Sc).castHom (projection_ob D ν s) (projection_ob D ν r))
    ((projectionFunctor D Sc).map_comp f g)).trans
      ((pres D Sc).castHom_comp (projection_ob D ν s) (projection_ob D ν t)
        (projection_ob D ν r) _ _)

@[simp] theorem homMap_diag {ν : X × (I →₀ ℤ)} {s t : List (Letter I)}
    (f : ob Dc ν s ⟶ ob Dc ν t) :
    homMap D Sc ν s t ((pres Dc Scc).diag f) = (pres D Sc).diag (diagram D f) := by
  rw [homMap_apply, projectionFunctor_diag, Presentation.castHom_diag]
  rfl

end OddMath.SKM.RootCover
