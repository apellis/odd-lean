/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.EvenDividedPower
import OddMath.QuiverHecke.SerreComplex
import OddMath.QuiverHecke.SignedNilHeckeExamples

/-!
# The divided-power projectors as Demazure products

Brundan–Ellis, arXiv:1701.04133v2, §11, before Lemma 11.1: the divided-power idempotent
`1_{i^{(r)}}` of `r` strands of colour `i` is the longest Demazure product `D_{w_0}` of the
elements `D_j = -ε T_j X_{j+1}` (`ε = (-1)^{|i|}`, after the odd sign correction of ERRATA
[BE2] 7), with `X` and `T` the dots and crossings of the word `i^r`.

The categorical divided powers of Lemma 11.5 are defined with the projectors
`evenCornerProjector` (the image of the nilHecke idempotent `demIdem`) and `oddCornerProjector`
(the image of the odd nilHecke projector `oppositeProjector`); the Serre complex of
Proposition 11.2 uses the Demazure products `SignedNilHecke.idem` of the dots `dotE` and
crossings `crossE` of a word. Here the two are identified:

* `evenCornerProjector_eq_idem`, `oddCornerProjector_eq_idem`: the projectors are
  `idem ε 0 r (dotE i^r) (crossE i^r) 0 r`;
* `SignedNilHecke.map_idem`: a ring homomorphism carrying the dots and crossings of a block to
  those of a block at offset `s` carries its Demazure product to the shifted one.

On the way, the same-colour maps send the nilHecke dots and crossings to `dotE` and `crossE`
(`evenCorner_x`, `evenCorner_ψ`, `oddCorner_x`, `oddCorner_ψ`).
-/

noncomputable section

namespace OddMath.QuiverHecke.SignedNilHecke

open Categorification.KLR.KL2.NH
open Categorification.NilHecke (w0Word lt_of_mem_w0Word)

variable {B B' : Type*} [Ring B] [Ring B']

variable {F : Type*} [FunLike F B B'] [RingHomClass F B B']

theorem map_wp (φ : F) (D : ℕ → B) (ρ : List ℕ) :
    φ (wp D ρ) = wp (fun j => φ (D j)) ρ := by
  simp [wp, map_list_prod, List.map_map, Function.comp_def]

/-- A ring homomorphism carrying the dots and crossings of the block `[0, n)` to those of the
block `[s, s + n)` carries the Demazure product of the first to that of the second. -/
theorem map_idem (φ : F) (ε : ℤˣ) {s n : ℕ} {X T : ℕ → B} {X' T' : ℕ → B'}
    (hX : ∀ a, a < n → φ (X a) = X' (s + a)) (hT : ∀ j, j + 1 < n → φ (T j) = T' (s + j)) :
    φ (idem ε 0 n X T 0 n) = idem ε s n X' T' s n := by
  rw [idem, idem, Wb, Wb, map_wp, wp, wp, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have h₀ := lt_of_mem_w0Word hj
  simp only [Function.comp_apply, zero_add]
  rw [dem_of (Nat.zero_le _) (by omega), dem_of (by omega) (by omega), map_neg, map_zsmul,
    map_mul, hT _ h₀, hX _ h₀, add_assoc]

end OddMath.QuiverHecke.SignedNilHecke

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams SignedNilHecke

universe u v w

theorem diag_conj {S : Signature} {R : Type*} [CommRing R] (P : Presentation S R)
    {a a' b b' : Obj S} (ha : a = a') (hb : b = b') (d : a ⟶ b) (d' : a' ⟶ b')
    (h : Diagram.layers d = Diagram.layers d') :
    eqToHom (congrArg P.obj ha).symm ≫ P.diag d ≫ eqToHom (congrArg P.obj hb) = P.diag d' := by
  subst ha hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact P.diag_eq_of_layers_eq h

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

theorem replicate_eq_dot (i : I) {n a : ℕ} (ha : a < n) :
    List.replicate n i = List.replicate a i ++ [i] ++ List.replicate (n - a - 1) i := by
  rw [List.append_assoc, List.singleton_append, ← List.replicate_succ, ← List.replicate_add]
  congr 1; omega

theorem replicate_eq_cross (i : I) {n a : ℕ} (ha : a + 1 < n) :
    List.replicate n i = List.replicate a i ++ [i, i] ++ List.replicate (n - a - 2) i := by
  rw [List.append_assoc, show [i, i] = List.replicate 2 i from rfl, ← List.replicate_add,
    ← List.replicate_add]
  congr 1; omega

theorem drop_replicate_succ (i : I) {n a : ℕ} (ha : a < n) :
    (List.replicate n i).drop a = i :: List.replicate (n - a - 1) i := by
  rw [List.drop_replicate, ← List.replicate_succ]; congr 1; omega

/-! ### The same-colour maps on generators -/

theorem evenCorner_x (i : I) (hi : D.parity i = 0) {n a : ℕ} (ha : a < n) :
    evenCorner D Sc i hi n (Categorification.NilHecke.Diagram.x k n a) =
      dotE D Sc (List.replicate n i) a := by
  rw [Categorification.NilHecke.Diagram.x_def k ha, dotE,
    genE_eq D Sc (sChain_dot _ _ i (replicate_eq_dot i ha) (List.length_replicate ..))]
  change eqToHom _ ≫ (evenFunctor D Sc i hi).map _ ≫ eqToHom _ = _
  unfold evenFunctor
  rw [SigMap.lift_diag, Diagram.weight_one, one_smul, cl]
  refine diag_conj _ ?_ ?_ _ _ ?_
  · change (⟨(), (List.replicate n ()).map fun _ => i⟩ : Obj (sig D)) = _
    simp only [List.map_replicate]; rfl
  · change (⟨(), (List.replicate n ()).map fun _ => i⟩ : Obj (sig D)) = _
    simp only [List.map_replicate]; rfl
  · simp only [LayerMap.layers_map, SigMap.toLayerMap_layer,
      Categorification.NilHecke.Diagram.layers_dlay, layers_mkD, pl, PG.ld,
      drop_replicate_succ i ha, layList, List.map_cons, List.map_nil, List.append_nil]
    simp [SigMap.layer, Categorification.NilHecke.Diagram.lay, lay, evenColour,
      List.take_replicate, Categorification.NilHecke.Diagram.Gen.arity]
    omega

theorem evenCorner_ψ (i : I) (hi : D.parity i = 0) {n a : ℕ} (ha : a + 1 < n) :
    evenCorner D Sc i hi n (Categorification.NilHecke.Diagram.ψ k n a) =
      crossE D Sc (List.replicate n i) a := by
  rw [Categorification.NilHecke.Diagram.ψ_def k ha, crossE,
    genE_eq D Sc (sChain_cross _ _ i (replicate_eq_cross i ha) (List.length_replicate ..))]
  change eqToHom _ ≫ (evenFunctor D Sc i hi).map _ ≫ eqToHom _ = _
  unfold evenFunctor
  rw [SigMap.lift_diag, Diagram.weight_one, one_smul, cl]
  refine diag_conj _ ?_ ?_ _ _ ?_
  · change (⟨(), (List.replicate n ()).map fun _ => i⟩ : Obj (sig D)) = _
    simp only [List.map_replicate]; rfl
  · change (⟨(), (List.replicate n ()).map fun _ => i⟩ : Obj (sig D)) = _
    simp only [List.map_replicate]; rfl
  · have hd : (List.replicate n i).drop a = i :: i :: List.replicate (n - a - 2) i := by
      rw [List.drop_replicate, ← List.replicate_succ, ← List.replicate_succ]; congr 1; omega
    simp only [LayerMap.layers_map, SigMap.toLayerMap_layer,
      Categorification.NilHecke.Diagram.layers_dlay, layers_mkD, pl, PG.ld, hd, layList,
      List.map_cons, List.map_nil, List.append_nil]
    simp [SigMap.layer, Categorification.NilHecke.Diagram.lay, lay, evenColour,
      List.take_replicate, Categorification.NilHecke.Diagram.Gen.arity]
    omega

theorem oddCorner_x (i : I) (hi : D.parity i = 1) {n a : ℕ} (ha : a < n) :
    oddCorner D Sc i hi n (Diagrams.OddNilHecke.x k n a) =
      dotE D Sc (List.replicate n i) a := by
  rw [Diagrams.OddNilHecke.x_def k ha, dotE,
    genE_eq D Sc (sChain_dot _ _ i (replicate_eq_dot i ha) (List.length_replicate ..))]
  change eqToHom _ ≫ (oddFunctor D Sc i hi).map _ ≫ eqToHom _ = _
  unfold oddFunctor
  rw [SigMap.lift_diag, Diagram.weight_one, one_smul, cl]
  refine diag_conj _ ?_ ?_ _ _ ?_
  · change (⟨(), (List.replicate n ()).map fun _ => i⟩ : Obj (sig D)) = _
    simp only [List.map_replicate]; rfl
  · change (⟨(), (List.replicate n ()).map fun _ => i⟩ : Obj (sig D)) = _
    simp only [List.map_replicate]; rfl
  · simp only [LayerMap.layers_map, SigMap.toLayerMap_layer,
      Diagrams.OddNilHecke.layers_dlay, layers_mkD, pl, PG.ld,
      drop_replicate_succ i ha, layList, List.map_cons, List.map_nil, List.append_nil]
    simp [SigMap.layer, Diagrams.OddNilHecke.lay, lay, oddColour,
      List.take_replicate, Diagrams.OddNilHecke.Gen.arity]
    omega

theorem oddCorner_ψ (i : I) (hi : D.parity i = 1) {n a : ℕ} (ha : a + 1 < n) :
    oddCorner D Sc i hi n (Diagrams.OddNilHecke.ψ k n a) =
      crossE D Sc (List.replicate n i) a := by
  rw [Diagrams.OddNilHecke.ψ_def k ha, crossE,
    genE_eq D Sc (sChain_cross _ _ i (replicate_eq_cross i ha) (List.length_replicate ..))]
  change eqToHom _ ≫ (oddFunctor D Sc i hi).map _ ≫ eqToHom _ = _
  unfold oddFunctor
  rw [SigMap.lift_diag, Diagram.weight_one, one_smul, cl]
  refine diag_conj _ ?_ ?_ _ _ ?_
  · change (⟨(), (List.replicate n ()).map fun _ => i⟩ : Obj (sig D)) = _
    simp only [List.map_replicate]; rfl
  · change (⟨(), (List.replicate n ()).map fun _ => i⟩ : Obj (sig D)) = _
    simp only [List.map_replicate]; rfl
  · have hd : (List.replicate n i).drop a = i :: i :: List.replicate (n - a - 2) i := by
      rw [List.drop_replicate, ← List.replicate_succ, ← List.replicate_succ]; congr 1; omega
    simp only [LayerMap.layers_map, SigMap.toLayerMap_layer,
      Diagrams.OddNilHecke.layers_dlay, layers_mkD, pl, PG.ld, hd, layList,
      List.map_cons, List.map_nil, List.append_nil]
    simp [SigMap.layer, Diagrams.OddNilHecke.lay, lay, oddColour,
      List.take_replicate, Diagrams.OddNilHecke.Gen.arity]
    omega


/-! ### The projectors -/

open Categorification.NilHecke in
theorem evenCornerProjector_eq_idem (i : I) (hi : D.parity i = 0) (r : ℕ) :
    evenCornerProjector D Sc i hi r =
      idem 1 0 r (dotE D Sc (List.replicate r i)) (crossE D Sc (List.replicate r i)) 0 r := by
  have hN : (⟨demIdem ℤ r, demIdem_mem⟩ : nilHecke ℤ r) =
      idem 1 0 r (fun a => ⟨xv ℤ r a, xv_mem a⟩) (fun j => ⟨dd ℤ r j, dd_mem j⟩) 0 r := by
    apply Subtype.ext
    change demIdem ℤ r = _
    rw [← SignedNilHecke.idem_nilHecke]
    let φ : @RingHom (nilHecke ℤ r) (Module.End ℤ (MvPolynomial (Fin r) ℤ))
        Ring.toSemiring.toNonAssocSemiring Ring.toSemiring.toNonAssocSemiring :=
      { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
        map_add' := fun _ _ => rfl }
    exact (map_idem φ 1 (s := 0) (fun a _ => by simp [φ]) (fun j _ => by simp [φ])).symm
  rw [evenCornerProjector, hN]
  refine map_idem (evenNilHecke D Sc i hi r) 1 (fun a ha => ?_) (fun j hj => ?_)
  · have : (⟨xv ℤ r a, xv_mem a⟩ : nilHecke ℤ r) = ⟨mulX ℤ r ⟨a, ha⟩, mulX_mem _⟩ :=
      Subtype.ext (xv_of_lt ha)
    rw [zero_add, this, evenNilHecke_mulX]
    exact evenCorner_x D Sc i hi ha
  · rw [zero_add, evenNilHecke_dd]
    exact evenCorner_ψ D Sc i hi hj

theorem coxeterWord_eq_reverse (m : ℕ) :
    Frontier.LongestDivided.coxeterWord m = (Categorification.NilHecke.w0Word m).reverse := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Frontier.LongestDivided.coxeterWord, Categorification.NilHecke.w0Word_succ, ih,
      List.reverse_append]

theorem map_val_wordIn (n : ℕ) :
    (Frontier.LongestDivided.wordIn n (n + 2) le_rfl).map Fin.val =
      Frontier.LongestDivided.coxeterWord (n + 2) := by
  simp [Frontier.LongestDivided.wordIn, List.map_pmap]

theorem oddNilHecke_unsignedProduct (i : I) (hi : D.parity i = 1) (n : ℕ)
    (w : Frontier.NilCoxeterWords.Word n) :
    oddNilHecke D Sc i hi n (SKM.DividedPowerIdempotents.unsignedProduct w) =
      Categorification.KLR.KL2.NH.wp
        (dem (zunit (D.parity i)) 0 (n + 2) (dotE D Sc (List.replicate (n + 2) i))
          (crossE D Sc (List.replicate (n + 2) i))) (w.map fun a => n - a.val) := by
  induction w with
  | nil => exact map_one _
  | cons a w ih =>
    rw [SKM.DividedPowerIdempotents.unsignedProduct, map_mul, ih, List.map_cons,
      Categorification.KLR.KL2.NH.wp_cons, hi]
    congr 1
    have ha := a.isLt
    rw [dem_of (Nat.zero_le _) (by omega), SKM.DividedPowerIdempotents.unsignedGenerator,
      SKM.DividedPowerIdempotents.sourceCrossing, SKM.DividedPowerIdempotents.sourceDot, map_mul]
    change oddCorner D Sc i hi (n + 2) (Diagrams.OddNilHecke.toDiagramsOver k n _) *
      oddCorner D Sc i hi (n + 2) (Diagrams.OddNilHecke.toDiagramsOver k n _) = _
    rw [Diagrams.OddNilHecke.toDiagramsOver_crossing, Diagrams.OddNilHecke.toDiagramsOver_dot,
      oddCorner_ψ D Sc i hi (by simp), oddCorner_x D Sc i hi (by simp; omega)]
    have h₁ : (a.rev : ℕ) = n - a := by simp [Fin.val_rev]
    have h₂ : (a.castSucc.rev : ℕ) = n - a + 1 := by simp [Fin.val_rev]; omega
    rw [h₁, h₂, show zunit (1 : ZMod 2) = -1 from rfl]
    simp

theorem oddCornerProjector_eq_idem (i : I) (hi : D.parity i = 1) (r : ℕ) :
    DividedPowerModules.oddCornerProjector D Sc i hi r =
      idem (zunit (D.parity i)) 0 r (dotE D Sc (List.replicate r i))
        (crossE D Sc (List.replicate r i)) 0 r := by
  match r with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
    have hF : IsSignedNilHeckeFamily (zunit (D.parity i)) 0 (n + 2)
        (dotE D Sc (List.replicate (n + 2) i)) (crossE D Sc (List.replicate (n + 2) i)) :=
      SerreComplex.family_of_eq [] [] i (n + 2) 0 (by simp) rfl
    rw [DividedPowerModules.oddCornerProjector, SKM.DividedPowerIdempotents.oppositeProjector_eq_unsignedProduct,
      oddNilHecke_unsignedProduct, idem, ← Categorification.KLR.KL2.NH.wp_w0Word_mirror
        hF.isBraidFamily_dem]
    congr 1
    have h := congrArg (List.map fun j => n - j) (map_val_wordIn n)
    rw [List.map_map, coxeterWord_eq_reverse, List.map_reverse] at h
    rw [List.map_reverse, show (fun a : Fin (n + 1) => n - (a : ℕ)) = (fun j => n - j) ∘ Fin.val
      from rfl, h, List.reverse_reverse]
    congr 1
    funext j; omega

end OddMath.QuiverHecke
