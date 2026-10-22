/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CornerProjectors
import OddMath.QuiverHecke.SerreClassUp
import OddMath.SKM.KarSummandProducts
import OddMath.SKM.K0Relations

/-!
# The Serre idempotents as whiskered divided-power projectors

Brundan–Ellis, arXiv:1701.04133v2, proof of Lemma 11.6. On the word `w = l ++ t ++ r` of the
quiver Hecke supercategory, whiskering by `l` and `r` is a ring homomorphism
`End(t) → End(w)` (`blockHom`, and `blockOf` for a word only propositionally of this form)
carrying the dots and crossings of `t` to those of `w` shifted by `|l|`. Hence the idempotents
`1_{i^{(a)}} ⊗ 1_{j i^{M-a}}` and `1_{i^a j} ⊗ 1_{i^{(M-a)}}` of `SerreComplex` are the
whiskered divided-power projectors `idem ε 0 n` on `i^n` (`lIdem_eq_blockOf`,
`rIdem_eq_blockOf`).
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w}
  [CommRing k] (Sc : SKM.Scalars D k)

/-! ### Whiskering words -/

theorem whisk_cl (l r : List I) {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t')
    (gs' : List PG) (h' : SChain (l ++ t ++ r) (pl _ gs') (l ++ t' ++ r))
    (e : pl (l ++ t ++ r) gs' = (pl t gs).map (wh l r)) :
    (pres D Sc).whisk (cl D Sc t t' gs h) (ob D l) r = cl D Sc _ _ gs' h' := by
  rw [cl_eq_diag D Sc gs' h' _ (sChain_wh h l r) e, ← lin_whisker_dg]
  change (pres D Sc).whisk ((pres D Sc).lin (dg D (pl t gs) h)) (ob D l) r = _
  rw [Presentation.whisk_lin, LinDiagram.whisk_of_ok]

theorem whisk_genE (l r u v : List I) (g : Shape I) (hg : g.cod = g.dom) {t : List I}
    (ht : t = u ++ g.dom ++ v) :
    (pres D Sc).whisk (genE D Sc t (PG.ofShape g u.length)) (ob D l) r =
      genE D Sc (l ++ t ++ r) (PG.ofShape g (l ++ u).length) := by
  subst ht
  rw [genE_eq D Sc (sChain_ofShape u v g hg rfl),
    genE_eq D Sc (sChain_ofShape (l ++ u) (v ++ r) g hg (by simp))]
  refine whisk_cl D Sc l r _ _ _ _ ?_
  rw [show l ++ (u ++ g.dom ++ v) ++ r = (l ++ u) ++ g.dom ++ (v ++ r) by simp, pl_ofShape,
    pl_ofShape]
  simp [wh]

/-- Whiskering by `l` and `r`: `End(t) → End(l t r)`. -/
def blockHom (l t r : List I) :
    End ((pres D Sc).obj (ob D t)) →+* End ((pres D Sc).obj (ob D (l ++ t ++ r))) where
  toFun f := (pres D Sc).whisk f (ob D l) r
  map_one' := (pres D Sc).whisk_id _ _ _ (Obj.whiskerOK_of_subsingleton _ _ _)
  map_mul' f g := (pres D Sc).whisk_comp g f _ _
  map_zero' := (pres D Sc).whisk_zero _ _
  map_add' f g := (pres D Sc).whisk_add f g _ _

theorem blockHom_apply (l t r : List I) (f : End ((pres D Sc).obj (ob D t))) :
    blockHom D Sc l t r f = (pres D Sc).whisk f (ob D l) r := rfl

/-- Whiskering by `l` and `r`, onto a word `w = l t r`. -/
def blockOf {l t r w : List I} (hw : l ++ t ++ r = w) :
    End ((pres D Sc).obj (ob D t)) →+* End ((pres D Sc).obj (ob D w)) :=
  hw ▸ blockHom D Sc l t r

theorem blockOf_dot {l r w : List I} {i : I} {n : ℕ} (hw : l ++ List.replicate n i ++ r = w)
    {a : ℕ} (ha : a < n) :
    blockOf D Sc hw (dotE D Sc (List.replicate n i) a) = dotE D Sc w (l.length + a) := by
  subst hw
  have h := whisk_genE D Sc l r (List.replicate a i) (List.replicate (n - a - 1) i) (.dot i) rfl
    (replicate_eq_dot i ha)
  simp only [PG.ofShape, List.length_append, List.length_replicate] at h
  exact h

theorem blockOf_cross {l r w : List I} {i : I} {n : ℕ} (hw : l ++ List.replicate n i ++ r = w)
    {a : ℕ} (ha : a + 1 < n) :
    blockOf D Sc hw (crossE D Sc (List.replicate n i) a) = crossE D Sc w (l.length + a) := by
  subst hw
  have h := whisk_genE D Sc l r (List.replicate a i) (List.replicate (n - a - 2) i)
    (.cross i i) rfl (replicate_eq_cross i ha)
  simp only [PG.ofShape, List.length_append, List.length_replicate] at h
  exact h

/-- The Demazure idempotent on a block `i^n` of `w = l i^n r` is the whiskered one. -/
theorem idem_eq_blockOf {l r w : List I} {i : I} {n : ℕ} (hw : l ++ List.replicate n i ++ r = w)
    (ε : ℤˣ) :
    idem ε l.length n (dotE D Sc w) (crossE D Sc w) l.length n =
      blockOf D Sc hw (idem ε 0 n (dotE D Sc (List.replicate n i))
        (crossE D Sc (List.replicate n i)) 0 n) :=
  (map_idem (blockOf D Sc hw) ε (fun _ ha => blockOf_dot D Sc hw ha)
    (fun _ hj => blockOf_cross D Sc hw hj)).symm

/-! ### The Serre idempotents -/

namespace SerreComplex

variable {D Sc} {i j : I} {M : ℕ}

variable (D Sc i) in
/-- The divided-power projector `1_{i^{(n)}}` on `i^n`, uniform in the parity of `i`. -/
abbrev dpIdem (n : ℕ) : End ((pres D Sc).obj (ob D (List.replicate n i))) :=
  idem (eps D i) 0 n (dotE D Sc (List.replicate n i)) (crossE D Sc (List.replicate n i)) 0 n

theorem word_eq_left (a : ℕ) :
    [] ++ List.replicate a i ++ ([j] ++ List.replicate (M - a) i) = word i j M a := by
  simp [word]

theorem word_eq_right (a : ℕ) :
    (List.replicate a i ++ [j]) ++ List.replicate (M - a) i ++ [] = word i j M a := by
  simp [word]

variable (D Sc i j M) in
theorem lIdem_eq_blockOf (a : ℕ) :
    lIdem D Sc i j M a = blockOf D Sc (word_eq_left (i := i) (j := j) (M := M) a)
      (dpIdem D Sc i a) :=
  idem_eq_blockOf D Sc (word_eq_left a) _

variable (D Sc i j M) in
theorem rIdem_eq_blockOf (a : ℕ) :
    rIdem D Sc i j M a = blockOf D Sc (word_eq_right (i := i) (j := j) (M := M) a)
      (dpIdem D Sc i (M - a)) := by
  have h := idem_eq_blockOf D Sc (word_eq_right (i := i) (j := j) (M := M) a) (eps D i)
  simp only [List.length_append, List.length_replicate, List.length_singleton] at h
  exact h

end SerreComplex

/-! ### Heterogeneous equality of morphisms -/

theorem heq_conj {C : Type*} [Category C] {X X' Y Y' : C} (p : X = X') (q : Y' = Y)
    (f : X' ⟶ Y') : HEq (eqToHom p ≫ f ≫ eqToHom q) f := by
  subst p q; simp

theorem heq_comp {C : Type*} [Category C] {X Y Z X' Y' Z' : C} (hX : X = X') (hY : Y = Y')
    (hZ : Z = Z') {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'} (hf : HEq f f')
    (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst hX hY hZ; obtain rfl := eq_of_heq hf; obtain rfl := eq_of_heq hg; rfl

theorem whisk_heq {S : Signature} {R : Type*} [CommRing R] (P : Presentation S R)
    {a a' b b' u u' : Obj S} {v v' : List S.Colour} {f : P.obj a ⟶ P.obj b}
    {f' : P.obj a' ⟶ P.obj b'} (ha : a = a') (hb : b = b') (hf : HEq f f') (hu : u = u')
    (hv : v = v') : HEq (P.whisk f u v) (P.whisk f' u' v') := by
  subst ha hb hu hv; obtain rfl := eq_of_heq hf; rfl

/-! ### `α` of a whiskered endomorphism -/

theorem alpha_blockOf_heq (ν : X) {l t r w : List I} (hw : l ++ t ++ r = w)
    (f : End ((pres D Sc).obj (ob D t))) :
    HEq ((alpha D Sc ν).map (blockOf D Sc hw f))
      ((SKM.pres D Sc).whisk ((alpha D Sc (SKM.wt D ν (upWord r))).map f)
        (SKM.ob D (SKM.wt D (SKM.wt D ν (upWord r)) (upWord t)) (upWord l))
        (SKM.wd D ν (upWord r))) := by
  subst hw
  have h := LayerMap.lift_whisk (P := pres D Sc) (labelWhisker D) (fun _ => trivial)
    (label_rel D Sc) (fun μ _ hx => label_interchange D Sc μ hx) ν f (u := ob D l) (v := r)
    trivial (Obj.whiskerOK_of_subsingleton _ _ _) ⟨𝟙 _⟩
  exact (heq_of_eq h).trans (heq_conj _ _ _)

/-! ### Whiskering in `𝔘(𝔤)` -/

open BicategoryStruct

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

theorem whiskerRight_heq {l m n : SKM.UGr D Sc sy hc} {f f' : l ⟶ m} (η : f ⟶ f') (g : m ⟶ n) :
    HEq (η ▷ g) ((SKM.pres D Sc).whisk
      (show (SKM.pres D Sc).obj f.obj ⟶ (SKM.pres D Sc).obj f'.obj from η)
      (Obj.nil (show X from l.region)) g.obj.word) := by
  show HEq ((SKM.pres D Sc).wRAt _ (show (SKM.pres D Sc).obj f.obj ⟶ (SKM.pres D Sc).obj f'.obj
    from η) g.obj f.start_eq f'.start_eq) _
  unfold Presentation.wRAt
  exact heq_conj _ _ _

theorem whiskerLeft_heq {l m n : SKM.UGr D Sc sy hc} (f : l ⟶ m) {g g' : m ⟶ n} (θ : g ⟶ g') :
    HEq (f ◁ θ) ((SKM.pres D Sc).whisk
      (show (SKM.pres D Sc).obj g.obj ⟶ (SKM.pres D Sc).obj g'.obj from θ) f.obj []) := by
  show HEq ((SKM.pres D Sc).wL f.obj (show (SKM.pres D Sc).obj g.obj ⟶ (SKM.pres D Sc).obj g'.obj
    from θ)) _
  unfold Presentation.wL
  exact heq_conj _ _ _

theorem whiskerRight_whiskerRight_heq {a b c d : SKM.UGr D Sc sy hc} {f f' : a ⟶ b} (η : f ⟶ f')
    (g : b ⟶ c) (h : c ⟶ d) : HEq (η ▷ g ▷ h) (η ▷ (g ≫ h)) := by
  rw [TwoSupercategory.whiskerRight_comp (R := k)]
  show HEq _ (eqToHom (congrArg (SKM.pres D Sc).obj (Obj.tensor_assoc f.obj g.obj h.obj).symm) ≫
    (η ▷ g ▷ h : (SKM.pres D Sc).obj _ ⟶ (SKM.pres D Sc).obj _) ≫
      eqToHom (congrArg (SKM.pres D Sc).obj (Obj.tensor_assoc f'.obj g.obj h.obj)))
  exact (heq_conj (C := (SKM.pres D Sc).Presented) _ _ _).symm

/-! ### The Serre idempotent in `𝔘(𝔤)` as a horizontal composite -/

namespace SerreComplex

variable {D Sc} {i j : I} {M : ℕ} (ν : X)

/-- The weight `ν + (M - a) α_i + α_j` between `E_i^a` and `E_j E_i^{M-a} 1_ν`. -/
abbrev wtL (D : SKM.Datum I X) (ν : X) (i j : I) (M a : ℕ) : X := SKM.wt D ν (upWord ([j] ++ List.replicate (M - a) i))

/-- The weight `ν + (M - a) α_i` between `E_j` and `E_i^{M-a} 1_ν`. -/
abbrev wtR (D : SKM.Datum I X) (ν : X) (i : I) (M a : ℕ) : X := SKM.wt D ν (upWord (List.replicate (M - a) i))

theorem wt_left {a : ℕ} (ha : a ≤ M) :
    SKM.wt D (wtL D ν i j M a) (upWord (List.replicate a i)) = (M • D.α i + D.α j) + ν := by
  rw [← wt_word ν ha]
  simp only [wtL, word, upWord_append, List.append_assoc, SKM.wt_append]

variable (i j M) in
/-- `E_i^a 1_{ν + (M-a) α_i + α_j}`. -/
def leftHom (a : ℕ) (ha : a ≤ M) : UHom D Sc sy hc ((M • D.α i + D.α j) + ν) (wtL D ν i j M a) :=
  SKM.K0Relations.word Sc sy hc _ _ (upWord (List.replicate a i)) (wt_left ν ha)

variable (i j M) in
/-- `E_j 1_{ν + (M-a) α_i}`. -/
def midHom (a : ℕ) : UHom D Sc sy hc (wtL D ν i j M a) (wtR D ν i M a) :=
  SKM.K0Relations.word Sc sy hc _ _ (upWord [j]) rfl

variable (i M) in
/-- `E_i^{M-a} 1_ν`. -/
def rightHom (a : ℕ) : UHom D Sc sy hc (wtR D ν i M a) ν :=
  SKM.K0Relations.word Sc sy hc _ _ (upWord (List.replicate (M - a) i)) rfl

theorem obj_comp {a : ℕ} (ha : a ≤ M) :
    ((leftHom sy hc i j M ν a ha ≫ midHom sy hc i j M ν a) ≫ rightHom sy hc i M ν a).obj =
      SKM.ob D ν (upWord (word i j M a)) := by
  refine Obj.ext ?_ ?_
  · change SKM.wt D (wtL D ν i j M a) (upWord (List.replicate a i)) = _
    simp only [wtL, word, upWord_append, List.append_assoc, SKM.wt_append, SKM.ob_start]
  · change (SKM.wd D (wtL D ν i j M a) (upWord (List.replicate a i)) ++
      SKM.wd D (wtR D ν i M a) (upWord [j])) ++ SKM.wd D ν (upWord (List.replicate (M - a) i)) = _
    simp only [wtL, wtR, word, upWord_append, List.append_assoc, SKM.wd_append, SKM.wt_append,
      SKM.ob_word]

theorem wordHom_eq_comp {a : ℕ} (ha : a ≤ M) :
    wordHom D Sc sy hc i j M ν a ha =
      (leftHom sy hc i j M ν a ha ≫ midHom sy hc i j M ν a) ≫ rightHom sy hc i M ν a :=
  Presentation.Bicat.Hom.ext (obj_comp (i := i) (j := j) sy hc ν ha).symm

variable (i j M) in
/-- `α(1_{i^{(a)}})` on `E_i^a 1_{ν + (M-a) α_i + α_j}`. -/
def projL (a : ℕ) (ha : a ≤ M) : leftHom sy hc i j M ν a ha ⟶ leftHom sy hc i j M ν a ha :=
  (alpha D Sc (wtL D ν i j M a)).map (dpIdem D Sc i a)

variable (i M) in
/-- `α(1_{i^{(M-a)}})` on `E_i^{M-a} 1_ν`. -/
def projR (a : ℕ) : rightHom sy hc i M ν a ⟶ rightHom sy hc i M ν a :=
  (alpha D Sc ν).map (dpIdem D Sc i (M - a))

open BicategoryStruct in
/-- **`α(e_a)` is the horizontal composite** `α(1_{i^{(a)}}) 1_{E_j} α(1_{i^{(M-a)}})`. -/
theorem alpha_eIdem_heq {a : ℕ} (ha : a ≤ M) :
    HEq ((alpha D Sc ν).map (eIdem D Sc i j M a))
      (TwoSupercategory.hcomp
        (TwoSupercategory.hcomp (projL sy hc i j M ν a ha) (𝟙 (midHom sy hc i j M ν a)))
        (projR sy hc i M ν a)) := by
  have hobj := congrArg (SKM.pres D Sc).obj (obj_comp (i := i) (j := j) sy hc ν ha).symm
  rw [eIdem_eq_comp' a ha, Functor.map_comp, lIdem_eq_blockOf, rIdem_eq_blockOf]
  simp only [TwoSupercategory.hcomp]
  rw [TwoSupercategory.whiskerLeft_id (R := k), Category.comp_id]
  refine heq_comp (C := (SKM.pres D Sc).Presented) hobj hobj hobj ?_ ?_
  · refine (alpha_blockOf_heq D Sc ν _ _).trans ?_
    refine HEq.symm ((whiskerRight_whiskerRight_heq D Sc sy hc _ _ _).trans
      ((whiskerRight_heq D Sc sy hc _ _).trans ?_))
    refine whisk_heq _ rfl rfl HEq.rfl ?_ rfl
    exact Obj.ext (wt_left ν ha).symm rfl
  · refine (alpha_blockOf_heq D Sc ν _ _).trans ?_
    refine HEq.symm ((whiskerLeft_heq D Sc sy hc _ _).trans ?_)
    refine whisk_heq _ rfl rfl HEq.rfl ?_ rfl
    refine Obj.ext ?_ ?_
    · change SKM.wt D (wtL D ν i j M a) (upWord (List.replicate a i)) = _
      simp only [wtL, upWord_append, SKM.wt_append, SKM.ob_start]; rfl
    · change SKM.wd D (wtL D ν i j M a) (upWord (List.replicate a i)) ++
        SKM.wd D (wtR D ν i M a) (upWord [j]) = _
      simp only [wtL, wtR, upWord_append, SKM.wd_append, SKM.wt_append, SKM.ob_word]; rfl

/-! ### Divided-power summands -/

theorem dpIdem_family (n : ℕ) :
    IsSignedNilHeckeFamily (eps D i) 0 n (dotE D Sc (List.replicate n i))
      (crossE D Sc (List.replicate n i)) :=
  family_of_eq [] [] i n 0 (by simp) rfl

theorem dpIdem_idem (n : ℕ) : dpIdem D Sc i n * dpIdem D Sc i n = dpIdem D Sc i n :=
  (dpIdem_family n).idem_mul_idem 0 n

theorem dpIdem_one : dpIdem D Sc i 1 = 1 := rfl

theorem getElem?_replicate_of_lt {n p : ℕ} (h : p < n) : (List.replicate n i)[p]? = some i := by
  simp [h]

theorem dpIdem_degree (n : ℕ) :
    (dpIdem D Sc i n : hObj D Sc sy hc (List.replicate n i) ⟶ hObj D Sc sy hc _) ∈
      GradedSupercategory.degree (R := k) (C := HGr D Sc sy hc) _ _ 0 :=
  idem_mem (gdeg_dot_add_cross sy i)
    (fun _ _ hp => crossE_mem (getElem?_replicate_of_lt (by omega))
      (getElem?_replicate_of_lt (by omega)))
    (fun _ _ hp => dotE_mem (getElem?_replicate_of_lt (by omega))) 0 n

theorem dpIdem_even (n : ℕ) :
    (dpIdem D Sc i n : hObj D Sc sy hc (List.replicate n i) ⟶ hObj D Sc sy hc _) ∈
      Supercategory.parity (R := k) (C := HGr D Sc sy hc) _ _ 0 :=
  idem_mem (parityDeg_dot_add_cross i)
    (fun _ _ hp => crossE_mem (getElem?_replicate_of_lt (by omega))
      (getElem?_replicate_of_lt (by omega)))
    (fun _ _ hp => dotE_mem (getElem?_replicate_of_lt (by omega))) 0 n

variable (i) in
/-- `α_{n,ν}(1_{i^{(n)}})` on the 1-morphism `E_i^n 1_ν` from `μ` to `ν`. -/
def dpProj (n : ℕ) (μ ν : X) (hs : SKM.wt D ν (upWord (List.replicate n i)) = μ) :
    SKM.K0Relations.word Sc sy hc μ ν _ hs ⟶ SKM.K0Relations.word Sc sy hc μ ν _ hs :=
  (alpha D Sc ν).map (dpIdem D Sc i n)

theorem dpProj_idem (n : ℕ) (μ ν : X) (hs : SKM.wt D ν (upWord (List.replicate n i)) = μ) :
    dpProj sy hc i n μ ν hs ≫ dpProj sy hc i n μ ν hs = dpProj sy hc i n μ ν hs := by
  change (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _ = _
  rw [← Functor.map_comp]
  exact congrArg _ (dpIdem_idem n)

variable (i) in
/-- The summand `Q^m Π^p (E_i^n 1_ν, α(1_{i^{(n)}}))`. BE2's divided power `E_i^{(n)} 1_ν`
is `m = p = 0`; the corrected one of Lemma 11.5 is `m = d_i n(n-1)/2`, `p = |i| n(n-1)/2`. -/
abbrev dpSummand (n : ℕ) (μ ν : X) (hs : SKM.wt D ν (upWord (List.replicate n i)) = μ)
    (m : ℤ) (p : ZMod 2) :=
  SKM.Summands.raw (dpProj_idem sy hc n μ ν hs)
    (alpha_mem_degree D Sc sy ν (dpIdem_degree sy hc n))
    (alpha_mem_parity D Sc ν (dpIdem_even sy hc n)) m p

theorem raw_congr {A : Type*} [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    [GradedSupercategory k A] {f f' : A} (h : f = f') {e : f ⟶ f} {e' : f' ⟶ f'} (he : HEq e e')
    (hi : e ≫ e = e) (hd : e ∈ GradedSupercategory.degree (R := k) f f 0)
    (hp : e ∈ Supercategory.parity (R := k) f f 0) (hi' : e' ≫ e' = e')
    (hd' : e' ∈ GradedSupercategory.degree (R := k) f' f' 0)
    (hp' : e' ∈ Supercategory.parity (R := k) f' f' 0) (n : ℤ) (p : ZMod 2) :
    SKM.Summands.raw hi hd hp n p = SKM.Summands.raw hi' hd' hp' n p := by
  subst h; obtain rfl := eq_of_heq he; rfl

/-! ### The terms of the Serre complex as products -/

open SKM.K0Relations in
/-- **The terms of the Serre complex are products of divided powers**: in the split
Grothendieck ring of `𝔘̇_{q,π}(𝔤)`, with BE2's multiplication order,
`[termUp a] = [Q^{m_L} Π^{p_L} E_i^{(a)}] [E_j] [Q^{m_R} Π^{p_R} E_i^{(M-a)} 1_ν]` whenever the
shifts add up to those of `termUp a`. -/
theorem class_termUp {a : ℕ} (ha : a ≤ M) (mL mR : ℤ) (pL pR : ZMod 2)
    (hm : mL + 0 + mR = sh sy i M a) (hp : pL + 0 + pR = par D i j M a) :
    (MulOpposite.op (K₀Ring.mk (B := SKM.UDot D Sc sy hc)
        (a := weight Sc sy hc ((M • D.α i + D.α j) + ν)) (b := weight Sc sy hc ν)
        (termUp sy hc i j M ν a ha)) : Grothendieck Sc sy hc) =
      MulOpposite.op (K₀Ring.mk (B := SKM.UDot D Sc sy hc)
        (a := weight Sc sy hc ((M • D.α i + D.α j) + ν)) (b := weight Sc sy hc (wtL D ν i j M a))
        (dpSummand sy hc i a ((M • D.α i + D.α j) + ν) (wtL D ν i j M a) (wt_left ν ha) mL pL)) *
      MulOpposite.op (K₀Ring.mk (B := SKM.UDot D Sc sy hc) (a := weight Sc sy hc (wtL D ν i j M a))
        (b := weight Sc sy hc (wtR D ν i M a))
        (dpSummand sy hc j 1 (wtL D ν i j M a) (wtR D ν i M a) rfl 0 0)) *
      MulOpposite.op (K₀Ring.mk (B := SKM.UDot D Sc sy hc) (a := weight Sc sy hc (wtR D ν i M a))
        (b := weight Sc sy hc ν) (dpSummand sy hc i (M - a) (wtR D ν i M a) ν rfl mR pR)) := by
  rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, SKM.Summands.mk_raw_mul_mk_raw,
    SKM.Summands.mk_raw_mul_mk_raw]
  congr 2
  rw [hm, hp]
  have hJ : dpProj sy hc j 1 (wtL D ν i j M a) (wtR D ν i M a) rfl = 𝟙 _ :=
    (alpha D Sc _).map_id _
  exact raw_congr (wordHom_eq_comp sy hc ν ha)
    ((alpha_eIdem_heq sy hc ν ha).trans (by rw [hJ]; rfl)) _ _ _ _ _ _ _ _

end SerreComplex

end OddMath.QuiverHecke
