import OddMath.Frontier.EQLimaHypercube
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Ellis–Qi, Appendix A: a box complex is a direct sum of hypercube complexes

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.1.1–A.1.3, A.2, A.3.  In each of the complexes of Appendix A (`OΛ`, `OΛ_n`, `U_n`,
`V_{a,b}`) the paper argues that the complex "is a direct sum of subcomplexes, each isomorphic to
(a shift of) a hypercube complex": a basis vector lies in the hypercube of its *initial vector*,
obtained by taking the balls out of all its urns, and the urns of that hypercube are the addable
boxes of the initial vector.

This file proves this for an arbitrary `EQLima.BoxSystem` `S` with arbitrary unit coefficients `c`:

* `Init S`: the *initial* shapes, those without removable boxes; `base S p` is the initial shape
  of `p` (all removable boxes removed), and `fill S q T` adds a set `T ⊆ A q` of addable boxes;
* `decomp S : P ≃ Σ q : Init S, Finset (A q)`: every shape is uniquely an initial shape `q` together
  with the set of filled urns among the addable boxes of `q` (`decomp_symm_apply`);
* `delta_ofPiece`: on the shapes of the piece of `q`, the differential is the differential of the
  hypercube `Y_{A q}` (`EQLima.hypercube`), with coefficients `hyperCoeff`;
* `decompEquiv`, `decompEquiv_delta` (**the hypercube decomposition**): a linear isomorphism
  `(P →₀ k) ≅ ⨁_{q ∈ Init S} (Y_{A q} as a module)` intertwining `δ` with the direct sum of the
  hypercube differentials; `hyper_delta_sq` shows each summand is a complex when `δ² = 0`;
* `crit_iff_init`: the critical shapes are the initial shapes without addable boxes, i.e. the
  hypercubes of dimension `0`; hence (`EQLima.BoxSystem.homologyBasis`) the cohomology has a basis
  indexed by the `0`-dimensional hypercubes, and the complex is contractible when every summand
  has at least one urn (`critSet_eq_empty`).
-/

namespace OddMath.Frontier.EQApp

open Finset OddMath.Frontier.EQLima

noncomputable section

variable {P B : Type*} [DecidableEq B] (S : BoxSystem P B)

/-! ### Removing and adding lists of boxes -/

/-- Remove the boxes of a list, in order. -/
def remList : P → List B → P
  | p, [] => p
  | p, b :: l => remList (S.rem p b) l

/-- Add the boxes of a list, in order. -/
def addList : P → List B → P
  | p, [] => p
  | p, b :: l => addList (S.add p b) l

theorem remList_spec : ∀ (l : List B) (p : P), l.Nodup → (∀ b ∈ l, b ∈ S.R p) →
    S.cells (remList S p l) = S.cells p \ l.toFinset ∧
    S.A (remList S p l) = S.A p ∪ l.toFinset ∧
    S.R (remList S p l) = S.R p \ l.toFinset
  | [], p, _, _ => by simp [remList]
  | b :: l, p, hnd, hR => by
    have hb : b ∈ S.R p := hR b (List.mem_cons_self ..)
    have hbl : b ∉ l := (List.nodup_cons.mp hnd).1
    have hR' : ∀ b' ∈ l, b' ∈ S.R (S.rem p b) := by
      intro b' hb'
      rw [S.R_rem hb]
      exact Finset.mem_erase.mpr ⟨fun e => hbl (e ▸ hb'), hR b' (List.mem_cons_of_mem _ hb')⟩
    obtain ⟨h1, h2, h3⟩ := remList_spec l (S.rem p b) (List.nodup_cons.mp hnd).2 hR'
    simp only [remList, List.toFinset_cons]
    rw [h1, h2, h3, S.cells_rem hb, S.A_rem hb, S.R_rem hb]
    refine ⟨?_, ?_, ?_⟩
    · ext x; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
    · ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    · ext x; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto

theorem addList_spec : ∀ (l : List B) (p : P), l.Nodup → (∀ b ∈ l, b ∈ S.A p) →
    S.cells (addList S p l) = S.cells p ∪ l.toFinset ∧
    S.A (addList S p l) = S.A p \ l.toFinset ∧
    S.R (addList S p l) = S.R p ∪ l.toFinset
  | [], p, _, _ => by simp [addList]
  | b :: l, p, hnd, hA => by
    have hb : b ∈ S.A p := hA b (List.mem_cons_self ..)
    have hbl : b ∉ l := (List.nodup_cons.mp hnd).1
    have hA' : ∀ b' ∈ l, b' ∈ S.A (S.add p b) := by
      intro b' hb'
      rw [S.A_add hb]
      exact Finset.mem_erase.mpr ⟨fun e => hbl (e ▸ hb'), hA b' (List.mem_cons_of_mem _ hb')⟩
    obtain ⟨h1, h2, h3⟩ := addList_spec l (S.add p b) (List.nodup_cons.mp hnd).2 hA'
    simp only [addList, List.toFinset_cons]
    rw [h1, h2, h3, S.cells_add hb, S.A_add hb, S.R_add hb]
    refine ⟨?_, ?_, ?_⟩
    · ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    · ext x; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
    · ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto

/-! ### Initial shapes -/

/-- The *initial vector* of a shape: all removable boxes (balls) taken out. -/
def base (p : P) : P := remList S p (S.R p).toList

theorem cells_base (p : P) : S.cells (base S p) = S.cells p \ S.R p := by
  have := (remList_spec S (S.R p).toList p (Finset.nodup_toList _)
    (fun b hb => Finset.mem_toList.mp hb)).1
  rwa [Finset.toList_toFinset] at this

theorem A_base (p : P) : S.A (base S p) = S.A p ∪ S.R p := by
  have := (remList_spec S (S.R p).toList p (Finset.nodup_toList _)
    (fun b hb => Finset.mem_toList.mp hb)).2.1
  rwa [Finset.toList_toFinset] at this

theorem R_base (p : P) : S.R (base S p) = ∅ := by
  have := (remList_spec S (S.R p).toList p (Finset.nodup_toList _)
    (fun b hb => Finset.mem_toList.mp hb)).2.2
  rwa [Finset.toList_toFinset, Finset.sdiff_self] at this

/-- Fill the urns `T` (a set of addable boxes) of a shape. -/
def fill (q : P) (T : Finset B) : P := addList S q T.toList

theorem fill_spec (q : P) {T : Finset B} (hT : T ⊆ S.A q) :
    S.cells (fill S q T) = S.cells q ∪ T ∧ S.A (fill S q T) = S.A q \ T ∧
      S.R (fill S q T) = S.R q ∪ T := by
  have := addList_spec S T.toList q (Finset.nodup_toList _)
    (fun b hb => hT (Finset.mem_toList.mp hb))
  rwa [Finset.toList_toFinset] at this

/-- The initial shapes: those without removable boxes ("all urns empty"). -/
abbrev Init : Type _ := {q : P // S.R q = ∅}

/-- The urns of the hypercube of an initial shape: its addable boxes. -/
abbrev Urn (q : Init S) : Type _ := {b : B // b ∈ S.A q.1}

/-- The pieces: an initial shape together with a set of filled urns. -/
abbrev Piece : Type _ := Σ q : Init S, Finset (Urn S q)

/-- The shape of a piece. -/
def ofPiece (x : Piece S) : P := fill S x.1.1 (x.2.map (Function.Embedding.subtype _))

/-- The piece of a shape: its initial vector and its filled urns. -/
def toPiece (p : P) : Piece S :=
  ⟨⟨base S p, R_base S p⟩, (S.R p).subtype (· ∈ S.A (base S p))⟩

theorem map_subtype_subset_A (q : Init S) (T : Finset (Urn S q)) :
    T.map (Function.Embedding.subtype _) ⊆ S.A q.1 := by
  intro b hb
  obtain ⟨⟨b', hb'⟩, -, rfl⟩ := Finset.mem_map.mp hb
  exact hb'

theorem ofPiece_spec (x : Piece S) :
    S.cells (ofPiece S x) = S.cells x.1.1 ∪ x.2.map (Function.Embedding.subtype _) ∧
    S.A (ofPiece S x) = S.A x.1.1 \ x.2.map (Function.Embedding.subtype _) ∧
    S.R (ofPiece S x) = x.2.map (Function.Embedding.subtype _) := by
  obtain ⟨h1, h2, h3⟩ := fill_spec S x.1.1 (map_subtype_subset_A S x.1 x.2)
  refine ⟨h1, h2, ?_⟩
  rw [ofPiece, h3, x.1.2, Finset.empty_union]

theorem R_subset_A_base (p : P) : S.R p ⊆ S.A (base S p) := by
  rw [A_base]; exact Finset.subset_union_right

theorem map_toPiece (p : P) :
    (toPiece S p).2.map (Function.Embedding.subtype _) = S.R p :=
  Finset.subtype_map_of_mem (fun _ h => R_subset_A_base S p h)

theorem ofPiece_toPiece (p : P) : ofPiece S (toPiece S p) = p := by
  apply S.cells_injective
  rw [(ofPiece_spec S _).1, map_toPiece]
  change S.cells (base S p) ∪ S.R p = S.cells p
  rw [cells_base, Finset.sdiff_union_of_subset (fun _ h => S.mem_cells_of_mem_R h)]

theorem piece_ext {q q' : Init S} (h : q = q') {T : Finset (Urn S q)} {T' : Finset (Urn S q')}
    (hT : T.map (Function.Embedding.subtype _) = T'.map (Function.Embedding.subtype _)) :
    (⟨q, T⟩ : Piece S) = ⟨q', T'⟩ := by
  subst h
  rw [Finset.map_inj.mp hT]

theorem base_ofPiece (x : Piece S) : base S (ofPiece S x) = x.1.1 := by
  apply S.cells_injective
  obtain ⟨h1, -, h3⟩ := ofPiece_spec S x
  rw [cells_base, h1, h3, Finset.union_sdiff_right]
  refine Finset.sdiff_eq_self_of_disjoint ?_
  rw [Finset.disjoint_left]
  intro b hb hb'
  exact S.notMem_cells_of_mem_A (map_subtype_subset_A S x.1 x.2 hb') hb

theorem toPiece_ofPiece (x : Piece S) : toPiece S (ofPiece S x) = x := by
  obtain ⟨q, T⟩ := x
  exact piece_ext S (Subtype.ext (base_ofPiece S ⟨q, T⟩))
    ((map_toPiece S (ofPiece S ⟨q, T⟩)).trans (ofPiece_spec S ⟨q, T⟩).2.2)

/-- **Decomposition of the shapes**: every shape is uniquely an initial shape `q` together with a
set of filled urns among the addable boxes of `q`. -/
def decomp : P ≃ Piece S where
  toFun := toPiece S
  invFun := ofPiece S
  left_inv := ofPiece_toPiece S
  right_inv := toPiece_ofPiece S

theorem decomp_symm_apply (x : Piece S) : (decomp S).symm x = ofPiece S x := rfl

theorem decomp_apply_fst (p : P) : ((decomp S p).1 : P) = base S p := rfl

theorem ofPiece_injective (q : Init S) : Function.Injective fun T : Finset (Urn S q) =>
    ofPiece S ⟨q, T⟩ :=
  fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp ((decomp S).symm.injective h)).2

theorem A_ofPiece (q : Init S) (T : Finset (Urn S q)) :
    S.A (ofPiece S ⟨q, T⟩) = (Finset.univ \ T).map (Function.Embedding.subtype _) := by
  rw [(ofPiece_spec S _).2.1]
  ext b
  simp only [Finset.mem_sdiff, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨hb, hbT⟩
    exact ⟨⟨b, hb⟩, fun h => hbT ⟨⟨b, hb⟩, h, rfl⟩, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨β.2, ?_⟩
    rintro ⟨β', hβ', e⟩
    exact hβ (Subtype.ext e ▸ hβ')

theorem add_ofPiece (q : Init S) (T : Finset (Urn S q)) {β : Urn S q} (hβ : β ∉ T) :
    S.add (ofPiece S ⟨q, T⟩) β.1 = ofPiece S ⟨q, insert β T⟩ := by
  have hA : β.1 ∈ S.A (ofPiece S ⟨q, T⟩) := by
    rw [A_ofPiece]
    exact Finset.mem_map_of_mem _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hβ⟩)
  apply S.cells_injective
  rw [S.cells_add hA, (ofPiece_spec S _).1, (ofPiece_spec S _).1, Finset.map_insert]
  simp only [Function.Embedding.coe_subtype]
  ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto

/-! ### The differential on a piece is a hypercube differential -/

section Complex

variable {k : Type*} [CommRing k] (c : P → B → kˣ)

/-- The coefficients of the hypercube of an initial shape `q`. -/
def hyperCoeff (q : Init S) (T : Finset (Urn S q)) (β : Urn S q) : kˣ :=
  c (ofPiece S ⟨q, T⟩) β.1

/-- The hypercube differential of the summand of an initial shape `q`. -/
noncomputable def hyperDelta (q : Init S) :
    (Finset (Urn S q) →₀ k) →ₗ[k] (Finset (Urn S q) →₀ k) :=
  (hypercube (Urn S q)).delta (hyperCoeff S c q)

/-- The embedding of the hypercube of `q` into the whole complex. -/
noncomputable def pieceMap (q : Init S) : (Finset (Urn S q) →₀ k) →ₗ[k] (P →₀ k) :=
  Finsupp.lmapDomain k k fun T => ofPiece S ⟨q, T⟩

theorem pieceMap_injective (q : Init S) : Function.Injective (pieceMap S (k := k) q) :=
  Finsupp.mapDomain_injective (ofPiece_injective S q)

/-- On the shapes of the piece of `q`, `δ` is the hypercube differential of `Y_{A q}`. -/
theorem delta_ofPiece (q : Init S) (T : Finset (Urn S q)) :
    S.delta c (Finsupp.single (ofPiece S ⟨q, T⟩) 1) =
      pieceMap S q (hyperDelta S c q (Finsupp.single T 1)) := by
  rw [hyperDelta, BoxSystem.delta_single, BoxSystem.delta_single, map_sum, A_ofPiece,
    Finset.sum_map]
  refine Finset.sum_congr rfl fun β hβ => ?_
  have hβT : β ∉ T := (Finset.mem_sdiff.mp hβ).2
  rw [map_smul, pieceMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  change _ = ((c (ofPiece S ⟨q, T⟩) β.1 : kˣ) : k) • _
  rw [Function.Embedding.coe_subtype, add_ofPiece S q T hβT]
  rfl

theorem delta_pieceMap (q : Init S) (y : Finset (Urn S q) →₀ k) :
    S.delta c (pieceMap S q y) = pieceMap S q (hyperDelta S c q y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single T a =>
    rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, map_smul, map_smul,
      map_smul, pieceMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, delta_ofPiece]
    rfl

/-- Each hypercube summand is a complex when `δ² = 0`. -/
theorem hyper_delta_sq (hc : S.SquareCond c) (q : Init S) :
    hyperDelta S c q ∘ₗ hyperDelta S c q = 0 := by
  refine LinearMap.ext fun y => pieceMap_injective S q ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply, map_zero]
  rw [← delta_pieceMap, ← delta_pieceMap, S.delta_sq_eq_zero_of_squareCond hc]

/-- The linear isomorphism `(P →₀ k) ≅ ⨁_{q ∈ Init S} (Finset (A q) →₀ k)`. -/
noncomputable def decompEquiv :
    (P →₀ k) ≃ₗ[k] Π₀ q : Init S, (Finset (Urn S q) →₀ k) :=
  (Finsupp.domLCongr (decomp S)).trans (sigmaFinsuppLequivDFinsupp k)

theorem decompEquiv_pieceMap [DecidableEq (Init S)] (q : Init S) (y : Finset (Urn S q) →₀ k) :
    decompEquiv S (pieceMap S q y) =
      DFinsupp.single (β := fun q : Init S => Finset (Urn S q) →₀ k) q y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    exact (DFinsupp.single_add (β := fun q : Init S => Finset (Urn S q) →₀ k) q x y).symm
  | single T a =>
    rw [pieceMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, decompEquiv,
      LinearEquiv.trans_apply, Finsupp.domLCongr_single]
    change sigmaFinsuppEquivDFinsupp (Finsupp.single (decomp S (ofPiece S ⟨q, T⟩)) a) = _
    rw [← decomp_symm_apply, Equiv.apply_symm_apply, sigmaFinsuppEquivDFinsupp_single]

/-- **The hypercube decomposition** (Ellis–Qi, Appendix A.1.1, A.2, A.3): under `decompEquiv`,
the box differential `δ` becomes the direct sum over the initial shapes `q` of the hypercube
differentials of `Y_{A q}`. -/
theorem decompEquiv_delta (x : P →₀ k) :
    decompEquiv S (S.delta c x) =
      DFinsupp.mapRange.linearMap (fun q => hyperDelta S c q) (decompEquiv S x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single p a =>
    obtain ⟨⟨q, T⟩, rfl⟩ := (decomp S).symm.surjective p
    rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, map_smul, map_smul,
      map_smul, decomp_symm_apply, delta_ofPiece]
    have h1 : Finsupp.single (ofPiece S ⟨q, T⟩) (1 : k) = pieceMap S q (Finsupp.single T 1) := by
      rw [pieceMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [h1, decompEquiv_pieceMap, decompEquiv_pieceMap, DFinsupp.mapRange.linearMap_apply]
    congr 1
    ext q' : 1
    rw [DFinsupp.mapRange_apply]
    by_cases hq : q = q'
    · subst hq
      simp only [DFinsupp.single_eq_same]
    · rw [DFinsupp.single_eq_of_ne (Ne.symm hq), DFinsupp.single_eq_of_ne (Ne.symm hq), map_zero]

/-- The same statement as an identity of linear maps. -/
theorem decompEquiv_comp_delta :
    (decompEquiv S).toLinearMap ∘ₗ S.delta c =
      DFinsupp.mapRange.linearMap (fun q => hyperDelta S c q) ∘ₗ (decompEquiv S).toLinearMap :=
  LinearMap.ext fun x => decompEquiv_delta S c x

end Complex

/-! ### Critical shapes are the `0`-dimensional hypercubes -/

theorem crit_iff_init (p : P) : S.Crit p ↔ S.R p = ∅ ∧ S.A p = ∅ := by
  rw [BoxSystem.crit_iff, and_comm]

/-- The urns of a shape are the addable boxes of its initial vector. -/
theorem U_eq_A_base (p : P) : S.U p = S.A (base S p) := by
  rw [A_base]; rfl

/-- If every initial shape has an addable box (every hypercube summand has an urn), there are no
critical shapes, so the box complex is contractible (`EQLima.BoxSystem.homotopy_spec`). -/
theorem critSet_eq_empty (h : ∀ q : P, S.R q = ∅ → (S.A q).Nonempty) : S.critSet = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  rw [BoxSystem.critSet, Set.mem_ofPred_eq, crit_iff_init] at hp
  obtain ⟨b, hb⟩ := h p hp.1
  rw [hp.2] at hb
  simp at hb

end

end OddMath.Frontier.EQApp
