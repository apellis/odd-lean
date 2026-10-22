/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Idempotents.Basic
import OddMath.QuiverHecke.RowModules

/-!
# The category of graded supermodules is additive and idempotent complete

Brundan–Ellis, arXiv:1701.04133v2, §11: the category `A-GSMod` of graded `A`-supermodules, for
`A = Mat obj` (see `OddMath.QuiverHecke.GradedModules`). Its morphism spaces are `k`-modules
(`GSMod.instLinear`), finite families of modules have direct sums (`GSMod.sum`, giving
`HasFiniteBiproducts`), and idempotents split through their images (`IsIdempotentComplete`).
These are the properties used to extend the row-module functor to the graded super Karoubi
envelope. Direct sums and images of projective (finitely generated) modules are projective
(finitely generated).
-/

noncomputable section
open scoped Classical
open CategoryTheory Limits StringDiagrams

namespace OddMath.FiniteHomMatrix

universe u v w t z

namespace GSMod

variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
  [Supercategory k C] [GradedSupercategory k C] {J : Type t} {obj : J → C}

/-! ## Linear structure on morphisms -/

/-- The graded, equivariant linear maps, as a submodule of all linear maps. -/
def homSubmodule (M N : GSMod.{u, v, w, t, z} k obj) : Submodule k (M →ₗ[k] N) where
  carrier := {f | (∀ a m, f (M.act a m) = N.act a (f m)) ∧
    ∀ d m, m ∈ M.piece d → f m ∈ N.piece d}
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => by simp⟩
  add_mem' hf hg := ⟨fun a m => by simp [hf.1, hg.1], fun d m hm =>
    (N.piece d).add_mem (hf.2 d m hm) (hg.2 d m hm)⟩
  smul_mem' r f hf := ⟨fun a m => by simp [hf.1], fun d m hm =>
    (N.piece d).smul_mem r (hf.2 d m hm)⟩

variable {M N L : GSMod.{u, v, w, t, z} k obj}

theorem toLinearMap_mem (f : M ⟶ N) : f.toLinearMap ∈ homSubmodule M N :=
  ⟨f.map_act, f.map_piece⟩

/-- The morphism given by an element of `homSubmodule`. -/
def ofMem (f : M →ₗ[k] N) (h : f ∈ homSubmodule M N) : M ⟶ N := ⟨f, h.1, h.2⟩

theorem toLinearMap_injective : Function.Injective (fun f : M ⟶ N => f.toLinearMap) :=
  fun _ _ h => Hom.ext h

instance : Zero (M ⟶ N) := ⟨ofMem 0 (homSubmodule M N).zero_mem⟩
instance : Add (M ⟶ N) :=
  ⟨fun f g => ofMem _ ((homSubmodule M N).add_mem (toLinearMap_mem f) (toLinearMap_mem g))⟩
instance : Neg (M ⟶ N) := ⟨fun f => ofMem _ ((homSubmodule M N).neg_mem (toLinearMap_mem f))⟩
instance : Sub (M ⟶ N) :=
  ⟨fun f g => ofMem _ ((homSubmodule M N).sub_mem (toLinearMap_mem f) (toLinearMap_mem g))⟩
instance : SMul k (M ⟶ N) :=
  ⟨fun r f => ofMem _ ((homSubmodule M N).smul_mem r (toLinearMap_mem f))⟩
instance : SMul ℕ (M ⟶ N) :=
  ⟨fun r f => ofMem _ ((homSubmodule M N).toAddSubmonoid.nsmul_mem (toLinearMap_mem f) r)⟩
instance : SMul ℤ (M ⟶ N) :=
  ⟨fun r f => ofMem _ ((homSubmodule M N).toAddSubgroup.zsmul_mem (toLinearMap_mem f) r)⟩

instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup _ toLinearMap_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module k (M ⟶ N) :=
  Function.Injective.module k ⟨⟨fun f : M ⟶ N => f.toLinearMap, rfl⟩, fun _ _ => rfl⟩
    toLinearMap_injective (fun _ _ => rfl)

@[simp] theorem add_toLinearMap (f g : M ⟶ N) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := rfl

@[simp] theorem zero_toLinearMap : (0 : M ⟶ N).toLinearMap = 0 := rfl

@[simp] theorem neg_toLinearMap (f : M ⟶ N) : (-f).toLinearMap = -f.toLinearMap := rfl

@[simp] theorem smul_toLinearMap (r : k) (f : M ⟶ N) :
    (r • f).toLinearMap = r • f.toLinearMap :=
  rfl

instance instPreadditive : Preadditive (GSMod.{u, v, w, t, z} k obj) where
  add_comp _ _ _ _ _ _ := by ext; simp
  comp_add _ _ _ _ _ _ := by ext; simp

instance instLinear : Linear k (GSMod.{u, v, w, t, z} k obj) where
  smul_comp _ _ _ _ _ _ := by ext; simp
  comp_smul _ _ _ _ _ _ := by ext; simp

/-! ## Direct sums -/

omit [Supercategory k C] [GradedSupercategory k C] in
/-- Local units can be enlarged. -/
theorem localUnit_mul_localUnit {s s' : Finset J} (h : s ⊆ s') :
    localUnit (obj := obj) s * localUnit s' = localUnit s := by
  conv_lhs => rw [localUnit, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi => by rw [idem, single_mul_localUnit _ _ _ _ (h hi)]

theorem act_localUnit_of_subset (M : GSMod.{u, v, w, t, z} k obj) {s s' : Finset J} {m : M}
    (hm : M.act (localUnit s) m = m) (h : s ⊆ s') : M.act (localUnit s') m = m := by
  rw [← hm, ← M.act_mul, localUnit_mul_localUnit h]

theorem finset_sum_toLinearMap_apply {ι' : Type*} (S : Finset ι') (f : ι' → (M ⟶ N))
    (m : M) :
    (∑ i ∈ S, f i).toLinearMap m = ∑ i ∈ S, (f i).toLinearMap m := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, add_toLinearMap,
      LinearMap.add_apply, ih]

variable {ι : Type} [Fintype ι]

/-- **BE2 §11.** The direct sum of a finite family of graded supermodules. -/
abbrev sum (M : ι → GSMod.{u, v, w, t, z} k obj) : GSMod.{u, v, w, t, z} k obj where
  carrier := Π₀ i, M i
  piece := entrywise fun i => (M i).piece
  isInternal_piece := isInternal_entrywise _ fun i => (M i).isInternal_piece
  act := LinearMap.mk₂ k
    (fun a v => DFinsupp.mapRange (fun i => (M i).act a) (fun _ => by simp) v)
    (fun a a' v => by ext; simp)
    (fun r a v => by ext; simp)
    (fun a v v' => by ext; simp)
    (fun r a v => by ext; simp)
  act_mul a b v := by ext; simp [(M _).act_mul]
  exists_localUnit v := by
    choose s hs using fun i => (M i).exists_localUnit (v i)
    refine ⟨Finset.univ.biUnion s, ?_⟩
    ext i
    simpa using (M i).act_localUnit_of_subset (hs i) (Finset.subset_biUnion_of_mem s (by simp))
  act_mem ha hv i := by simpa using (M i).act_mem ha (hv i)

variable (M : ι → GSMod.{u, v, w, t, z} k obj)

@[simp] theorem sum_act_apply (a : Mat obj) (v : sum M) (i : ι) :
    ((sum M).act a v : Π₀ i, M i) i = (M i).act a ((v : Π₀ i, M i) i) := by
  simp [sum]

/-- The projection onto a summand. -/
def sumπ (i : ι) : sum M ⟶ M i where
  toLinearMap := DFinsupp.lapply (M := fun i => (M i : Type z)) i
  map_act a v := by simp
  map_piece d v hv := hv i

/-- The inclusion of a summand. -/
def sumι (i : ι) : M i ⟶ sum M where
  toLinearMap := DFinsupp.lsingle (M := fun i => (M i : Type z)) i
  map_act a m := by
    ext j
    by_cases h : j = i
    · subst j; simp [sum]
    · simp [sum, DFinsupp.single_apply]
  map_piece d m hm := single_mem_entrywise i hm

theorem sumι_sumπ (i j : ι) :
    sumι M i ≫ sumπ M j = if h : i = j then eqToHom (congrArg M h) else 0 := by
  split_ifs with h
  · subst j; ext m; simp [sumι, sumπ]
  · ext m; simp [sumι, sumπ, DFinsupp.single_apply, h]

theorem sum_total : ∑ i, sumπ M i ≫ sumι M i = 𝟙 (sum M) := by
  refine hom_ext fun v => ?_
  rw [finset_sum_toLinearMap_apply]
  change ∑ i, DFinsupp.single i ((v : Π₀ i, M i) i) = v
  ext j
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single j (fun i _ h => by
    simp [DFinsupp.single_apply, h]) (by simp)]
  simp

/-- The direct sum as a bicone. -/
def sumBicone : Bicone M where
  pt := sum M
  π := sumπ M
  ι := sumι M
  ι_π := sumι_sumπ M

instance hasFiniteBiproducts : HasFiniteBiproducts (GSMod.{u, v, w, t, z} k obj) :=
  ⟨fun _ => ⟨fun M => hasBiproduct_of_total (sumBicone M) (sum_total M)⟩⟩

/-! ## Images of idempotents -/

theorem idem_apply {M : GSMod.{u, v, w, t, z} k obj} {p : M ⟶ M} (hp : p ≫ p = p) (x : M) :
    p.toLinearMap (p.toLinearMap x) = p.toLinearMap x :=
  congrArg (fun f : M ⟶ M => f.toLinearMap x) hp

theorem mem_range_of_idem {M : GSMod.{u, v, w, t, z} k obj} {p : M ⟶ M} (hp : p ≫ p = p)
    {x : M} : x ∈ LinearMap.range p.toLinearMap ↔ p.toLinearMap x = x :=
  ⟨by rintro ⟨y, rfl⟩; exact idem_apply hp y, fun h => ⟨x, h⟩⟩

/-- The image of an idempotent endomorphism, as a graded supermodule. -/
def image {M : GSMod.{u, v, w, t, z} k obj} (p : M ⟶ M) (hp : p ≫ p = p) :
    GSMod.{u, v, w, t, z} k obj where
  carrier := LinearMap.range p.toLinearMap
  piece d := (M.piece d).comap (LinearMap.range p.toLinearMap).subtype
  isInternal_piece := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro S a ha hz d hd
      have h := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero M.piece).mp
        M.isInternal_piece.submodule_iSupIndep S (fun d => (a d : M)) (fun d hd => ha d hd)
          (by simpa using congrArg Subtype.val hz)
      exact Subtype.ext (h d hd)
    · rw [eq_top_iff]
      rintro x -
      obtain ⟨S, hS⟩ := M.exists_finset_sum_proj (x : M)
      have hx := (mem_range_of_idem hp).mp x.2
      have hmem : ∀ d, M.proj d x ∈ LinearMap.range p.toLinearMap := fun d =>
        (mem_range_of_idem hp).mpr (by rw [proj_map p.toLinearMap p.map_piece, hx])
      have : x = ∑ d ∈ S, (⟨M.proj d x, hmem d⟩ : LinearMap.range p.toLinearMap) :=
        Subtype.ext (by simpa using hS.symm)
      rw [this]
      exact Submodule.sum_mem _ fun d _ =>
        Submodule.mem_iSup_of_mem d (show (M.proj d x) ∈ M.piece d from M.proj_mem d x)
  act := LinearMap.mk₂ k (fun a x => ⟨M.act a x, (mem_range_of_idem hp).mpr (by
      rw [p.map_act, (mem_range_of_idem hp).mp x.2])⟩)
    (fun a a' x => Subtype.ext (by simp))
    (fun r a x => Subtype.ext (by simp))
    (fun a x x' => Subtype.ext (by simp))
    (fun r a x => Subtype.ext (by simp))
  act_mul a b x := Subtype.ext (M.act_mul a b x)
  exists_localUnit x := by
    obtain ⟨s, hs⟩ := M.exists_localUnit (x : M)
    exact ⟨s, Subtype.ext hs⟩
  act_mem ha hx := M.act_mem ha hx

/-- The inclusion of the image of an idempotent. -/
def imageι {M : GSMod.{u, v, w, t, z} k obj} (p : M ⟶ M) (hp : p ≫ p = p) :
    image p hp ⟶ M where
  toLinearMap := (LinearMap.range p.toLinearMap).subtype
  map_act _ _ := rfl
  map_piece _ _ h := h

/-- The projection onto the image of an idempotent. -/
def imageπ {M : GSMod.{u, v, w, t, z} k obj} (p : M ⟶ M) (hp : p ≫ p = p) :
    M ⟶ image p hp where
  toLinearMap := p.toLinearMap.rangeRestrict
  map_act a m := Subtype.ext (p.map_act a m)
  map_piece d m h := p.map_piece d m h

theorem imageι_imageπ {M : GSMod.{u, v, w, t, z} k obj} (p : M ⟶ M) (hp : p ≫ p = p) :
    imageι p hp ≫ imageπ p hp = 𝟙 _ := by
  ext x
  exact Subtype.ext ((mem_range_of_idem hp).mp x.2)

theorem imageπ_imageι {M : GSMod.{u, v, w, t, z} k obj} (p : M ⟶ M) (hp : p ≫ p = p) :
    imageπ p hp ≫ imageι p hp = p := rfl

instance isIdempotentComplete : IsIdempotentComplete (GSMod.{u, v, w, t, z} k obj) :=
  ⟨fun _ p hp =>
    ⟨image p hp, imageι p hp, imageπ p hp, imageι_imageπ p hp, imageπ_imageι p hp⟩⟩

end GSMod

end OddMath.FiniteHomMatrix
