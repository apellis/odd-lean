/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.UpwardClasses
import OddMath.QuiverHecke.SerreDividedPowersDown

/-!
# The class map of the downward functor `α'`

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, class step for
downward words. The downward functor `α' = ω ∘ α` of (11.8) is contravariant on 2-morphisms
(its source is a super-opposite), so its class map is built from a contravariant functor on the
even degree-zero envelopes.

* `Summands.baseOpp G`: for a graded superfunctor `G : A ⥤ B^{sop}`, the functor
  `Q^n Π^p X ↦ Q^{-n} Π^p G(X)` from the even degree-zero envelope of `A` to the opposite of that
  of `B`, with the signs `(-1)^{(p + 1) q}` on morphisms `Q^m Π^p X → Q^n Π^q Y` that correct the
  super-opposite composition law.
* `Mat_.transposeOp`, `Karoubi.unopFun`, `K₀.unopHom`: matrices and Karoubi envelopes over an
  opposite category, and the classes of an opposite category.
* `downK0 μ ν : K₀(Ḣ_{q,π}) →+ K₀(𝔘̇(𝔤))`, with
  `[Q^n Π^p (t, e)] ↦ [Q^{-n} Π^p (F_t 1_{-ν}, ω α(e))]` when `wt_ν(t) = μ` (`downK0_raw`) and
  `↦ 0` otherwise (`downK0_raw_of_ne`); the 1-morphism `F_t 1_{-ν}` runs from `-μ` to `-ν`.
-/

noncomputable section

namespace CategoryTheory.Mat_

variable {D : Type*} [Category D] [Preadditive D]

/-- Transposition: a matrix over `Dᵒᵖ` is the opposite of a matrix over `D`. -/
def transposeOp : Mat_ Dᵒᵖ ⥤ (Mat_ D)ᵒᵖ where
  obj M := Opposite.op ⟨M.ι, fun i => (M.X i).unop⟩
  map {M N} f := Quiver.Hom.op (fun j i => (f i j).unop :
    Hom (⟨N.ι, fun j => (N.X j).unop⟩ : Mat_ D) ⟨M.ι, fun i => (M.X i).unop⟩)
  map_id M := by
    apply Quiver.Hom.unop_inj
    refine hom_ext _ _ fun j i => ?_
    change ((𝟙 M : Hom M M) i j).unop = (𝟙 (⟨M.ι, fun i => (M.X i).unop⟩ : Mat_ D) :
      Hom _ _) j i
    rw [id_apply, id_apply]
    by_cases h : i = j
    · subst h
      simp
    · have h' : j ≠ i := fun e => h e.symm
      simp [h, h']
  map_comp {M N K} f g := by
    apply Quiver.Hom.unop_inj
    refine hom_ext _ _ fun k i => ?_
    change ((f ≫ g : Hom M K) i k).unop = ∑ j : N.ι, (g j k).unop ≫ (f i j).unop
    rw [comp_apply, unop_sum]
    rfl

instance : (transposeOp (D := D)).Additive where
  map_add {M N f g} := by
    apply Quiver.Hom.unop_inj
    refine hom_ext _ _ fun j i => ?_
    change ((f + g : Hom M N) i j).unop = (f i j).unop + (g i j).unop
    rfl

end CategoryTheory.Mat_

namespace CategoryTheory.Idempotents.Karoubi

variable {E : Type*} [Category E] [Preadditive E]

/-- The Karoubi envelope of an opposite category is the opposite of the Karoubi envelope. -/
def unopFun : Karoubi Eᵒᵖ ⥤ (Karoubi E)ᵒᵖ where
  obj P := Opposite.op ⟨P.X.unop, P.p.unop, by rw [← unop_comp, P.idem]⟩
  map {P Q} f := Quiver.Hom.op ⟨f.f.unop, by
    change Q.p.unop ≫ f.f.unop ≫ P.p.unop = f.f.unop
    rw [← unop_comp, ← unop_comp, Category.assoc, f.comm]⟩
  map_id P := rfl
  map_comp f g := rfl

instance : (unopFun (E := E)).Additive where
  map_add := rfl

end CategoryTheory.Idempotents.Karoubi

namespace StringDiagrams.K₀

open CategoryTheory Limits

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- The classes of an opposite category: `[X] ↦ [X.unop]`. -/
def unopHom : K₀ Cᵒᵖ →+ K₀ C :=
  lift (fun X => mk X.unop) (fun _ _ e => mk_eq_mk_of_iso e.unop.symm) (fun X Y => by
    change mk (X ⊞ Y).unop = mk X.unop + mk Y.unop
    rw [← mk_eq_mk_of_iso (biprod.opIso X.unop Y.unop).symm.unop, mk_biprod])

@[simp] theorem unopHom_mk (X : Cᵒᵖ) : unopHom (mk X) = mk X.unop := lift_mk _ _ _ X

end StringDiagrams.K₀

namespace OddMath.SKM.Summands

open CategoryTheory StringDiagrams GradedSupercategory Supercategory

variable {k : Type*} [CommRing k] {A : Type*} [Category A] [Preadditive A] [Linear k A]
  [Supercategory k A] [GradedSupercategory k A] {B : Type*} [Category B] [Preadditive B]
  [Linear k B] [Supercategory k B] [GradedSupercategory k B]
  (G : A ⥤ SOp k B) [G.Additive] [G.Linear k] [IsGradedSuperfunctor k G]

/-- The sign `(-1)^{(p + 1) q}` of `baseOpp` on a morphism `Q^m Π^p X → Q^n Π^q Y`. -/
abbrev oppSign (p q : ZMod 2) : k := sign k (p * q + q)

theorem oppSign_cocycle (p q r : ZMod 2) :
    oppSign (k := k) q r * oppSign p q * sign k ((p + q) * (q + r)) = oppSign p r := by
  simp only [oppSign, ← sign_add]
  congr 1
  fin_cases p <;> fin_cases q <;> fin_cases r <;> decide

theorem oppSign_self (p : ZMod 2) : oppSign (k := k) p p = 1 := by
  rw [oppSign, show p * p + p = 0 by fin_cases p <;> decide, sign_zero]

/-- **A graded superfunctor into a super-opposite, on even degree-zero envelopes**: the
contravariant functor `Q^n Π^p X ↦ Q^{-n} Π^p G(X)`, `f ↦ (-1)^{(p + 1) q} G(f)` on
`f : Q^m Π^p X → Q^n Π^q Y`. -/
def baseOpp : Base k A ⥤ (Base k B)ᵒᵖ where
  obj Y := Opposite.op (shifted (k := k) (G.obj Y.obj.obj.obj.obj).unop (-Y.obj.obj.obj.shift)
    Y.obj.obj.par)
  map {Y Y'} f := Quiver.Hom.op ⟨⟨oppSign Y.obj.obj.par Y'.obj.obj.par • SOp.unsop (G.map f.1.1),
    by
      have h := f.1.2
      change f.1.1 ∈ degree (R := k) (C := A) _ _
        (0 + (Y.obj.obj.obj.shift - Y'.obj.obj.obj.shift)) at h
      change _ ∈ degree (R := k) (C := B) _ _ (0 + (-Y'.obj.obj.obj.shift - -Y.obj.obj.obj.shift))
      rw [neg_sub_neg]
      exact Submodule.smul_mem _ _ (IsGradedSuperfunctor.map_mem_degree (R := k) (F := G) h)⟩,
    by
      have h := f.2
      change f.1.1 ∈ parity (R := k) (C := A) _ _ (0 + (Y.obj.obj.par + Y'.obj.obj.par)) at h
      change _ ∈ parity (R := k) (C := B) _ _ (0 + (Y'.obj.obj.par + Y.obj.obj.par))
      rw [add_comm Y'.obj.obj.par]
      exact Submodule.smul_mem _ _ (IsSuperfunctor.map_mem (R := k) (F := G) h)⟩
  map_id Y := by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext; apply Subtype.ext
    change oppSign Y.obj.obj.par Y.obj.obj.par • SOp.unsop (G.map (𝟙 _)) = 𝟙 _
    rw [oppSign_self]
    erw [one_smul, G.map_id]
    rfl
  map_comp {Y Y' Y''} f g := by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext; apply Subtype.ext
    have hf := f.2
    change f.1.1 ∈ parity (R := k) (C := A) _ _ (0 + (Y.obj.obj.par + Y'.obj.obj.par)) at hf
    have hg := g.2
    change g.1.1 ∈ parity (R := k) (C := A) _ _ (0 + (Y'.obj.obj.par + Y''.obj.obj.par)) at hg
    rw [zero_add] at hf hg
    change oppSign Y.obj.obj.par Y''.obj.obj.par • SOp.unsop (G.map (f.1.1 ≫ g.1.1)) =
      (oppSign Y'.obj.obj.par Y''.obj.obj.par • SOp.unsop (G.map g.1.1)) ≫
        (oppSign Y.obj.obj.par Y'.obj.obj.par • SOp.unsop (G.map f.1.1))
    rw [Linear.smul_comp, Linear.comp_smul, OddMath.QuiverHecke.SplitComplex.unsop_map_comp G hf hg,
      smul_smul, smul_smul, oppSign_cocycle]

instance : (baseOpp G).Additive where
  map_add {Y Y' f g} := by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext; apply Subtype.ext
    change oppSign Y.obj.obj.par Y'.obj.obj.par • SOp.unsop (G.map (f.1.1 + g.1.1)) =
      oppSign Y.obj.obj.par Y'.obj.obj.par • SOp.unsop (G.map f.1.1) +
        oppSign Y.obj.obj.par Y'.obj.obj.par • SOp.unsop (G.map g.1.1)
    rw [G.map_add, SOp.unsop_add, smul_add]

end OddMath.SKM.Summands

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams GradedSupercategory OddMath.SKM.Summands

variable {I : Type*} {X : Type*} [AddCommGroup X] {D : SKM.Datum I X} {k : Type*} [CommRing k]
  {Sc : SKM.Scalars D k} {sy : SKM.Symmetrizer D} {hc : Sc.Homogeneous}

variable (Sc sy hc) in
/-- **The downward map `α' = ω ∘ α_ν` on the words of weight `μ`**, contravariantly on the even
degree-zero envelopes: `Q^n Π^p t ↦ Q^{-n} Π^p F_t 1_{-ν}`, a 1-morphism from `-μ` to `-ν`. -/
def downFun (μ ν : X) :
    (wtProp Sc sy hc μ ν).FullSubcategory ⥤
      (Base k (SKM.negWeight (sy := sy) (hc := hc) ⟨μ⟩ ⟶
        SKM.negWeight (sy := sy) (hc := hc) ⟨ν⟩))ᵒᵖ :=
  upFun Sc sy hc μ ν ⋙ baseOpp (SKM.chevHom (sy := sy) (hc := hc) ⟨μ⟩ ⟨ν⟩)

instance (μ ν : X) : (downFun Sc sy hc μ ν).Additive := by
  unfold downFun; infer_instance

variable (Sc sy hc) in
/-- **The class map `[α'_ν] : K₀(Ḣ_{q,π}) → K₀(𝔘̇(𝔤))`, component `Hom(-μ, -ν)`**, induced
by the contravariant functor `downFun` on the summands of the words of weight `wt_ν = μ`, the
other words being sent to zero. -/
def downK0 (μ ν : X) : K₀ (HKar D Sc sy hc) →+ SKM.K0Relations.Grothendieck Sc sy hc :=
  (SerreComplex.toGr sy hc (-μ) (-ν)).comp (K₀.unopHom.comp
    (K₀.map (Idempotents.Karoubi.mapFun (Mat_.restrictMap (P := wtProp Sc sy hc μ ν)
      (fun hY hY' f => wtProp_hom_eq_zero hY hY' f) (downFun Sc sy hc μ ν)) ⋙
      Idempotents.Karoubi.mapFun Mat_.transposeOp ⋙ Idempotents.Karoubi.unopFun)))

theorem downK0_raw {μ ν : X} {t : List I} {e : HEnd D Sc sy hc t} (he : e ≫ e = e)
    (hd : e ∈ GradedSupercategory.degree (R := k) _ _ 0)
    (hp : e ∈ Supercategory.parity (R := k) _ _ 0) (n : ℤ) (p : ZMod 2)
    (h : SKM.wt D ν (upWord t) = μ) :
    downK0 Sc sy hc μ ν (K₀.mk (raw he hd hp n p)) =
      MulOpposite.op (K₀Ring.mk (B := SKM.UDot D Sc sy hc)
        (a := SKM.K0Relations.weight Sc sy hc (-μ)) (b := SKM.K0Relations.weight Sc sy hc (-ν))
        (SerreComplex.chevSummand sy hc (upProj_idem h he) (alpha_mem_degree D Sc sy ν hd)
          (alpha_mem_parity D Sc ν hp) (-n) p)) := by
  obtain ⟨i⟩ := Mat_.mapFun_restrictMap_single (P := wtProp Sc sy hc μ ν)
    (fun hY hY' f => wtProp_hom_eq_zero hY hY' f) (downFun Sc sy hc μ ν)
    (shifted (k := k) (hObj D Sc sy hc t) n p) h _
    (projector_idem he hd hp n p)
  have i' := ((Idempotents.Karoubi.mapFun Mat_.transposeOp ⋙
    Idempotents.Karoubi.unopFun).mapIso i).unop
  refine (congrArg (SerreComplex.toGr sy hc (-μ) (-ν)) ((K₀.unopHom_mk _).trans
    ((K₀.mk_eq_mk_of_iso i').symm.trans ?_))).trans rfl
  congr 1
  refine Idempotents.Karoubi.ext rfl ?_
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  refine Mat_.hom_ext _ _ fun a b => Subtype.ext (Subtype.ext ?_)
  exact (congrArg (fun c : k => c • SOp.unsop ((SKM.chevHom (sy := sy) (hc := hc) ⟨μ⟩ ⟨ν⟩).map
    (upProj h e))) (oppSign_self p)).trans (one_smul k _)

theorem downK0_raw_of_ne {μ ν : X} {t : List I} {e : HEnd D Sc sy hc t} (he : e ≫ e = e)
    (hd : e ∈ GradedSupercategory.degree (R := k) _ _ 0)
    (hp : e ∈ Supercategory.parity (R := k) _ _ 0) (n : ℤ) (p : ZMod 2)
    (h : SKM.wt D ν (upWord t) ≠ μ) :
    downK0 Sc sy hc μ ν (K₀.mk (raw he hd hp n p)) = 0 := by
  rw [downK0, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, K₀.map_mk]
  have hz := Mat_.isZero_mapFun_restrictMap_single (P := wtProp Sc sy hc μ ν)
    (fun hY hY' f => wtProp_hom_eq_zero hY hY' f) (downFun Sc sy hc μ ν)
    (shifted (k := k) (hObj D Sc sy hc t) n p) h _ (projector_idem he hd hp n p)
  have hz' := ((Idempotents.Karoubi.mapFun Mat_.transposeOp ⋙
    Idempotents.Karoubi.unopFun).map_isZero hz).unop
  exact (congrArg (SerreComplex.toGr sy hc (-μ) (-ν)) ((K₀.unopHom_mk _).trans
    ((K₀.mk_eq_mk_of_iso hz'.isoZero).trans K₀.mk_zero))).trans (map_zero _)

end OddMath.QuiverHecke
