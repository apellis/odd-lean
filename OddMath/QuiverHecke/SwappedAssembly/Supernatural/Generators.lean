/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Cross
import OddMath.QuiverHecke.SwappedAssembly.Inversion
import OddMath.QuiverHecke.SwappedAssembly.Interchange

/-! # Supernaturality of the swapped generator images

The generator images `swappedGens c L` of the swapped Hom construction for Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5 and (2.6), are supernatural
entry by entry (`GeneratorsSupernatural`), the hypothesis of the super interchange law
`interchangeLaw`.

* The entries of a chain of layers are supernatural of the total parity of its generators
  (`compList_supernatural`), when the generator images are.
* The upward generators are supernatural (`upwardGens_supernatural`); hence so are the entries
  of the sideways crossing `σ`, of parity `pᵢ pⱼ` (`sigmaEntry_supernatural`).
* For distinct colours, when the matrix of `σ` is a permutation matrix with invertible entries
  (`SigmaPermutation`), the leftward crossing is supernatural (`lcrossNeImage_supernatural`):
  its entries are zero or inverses of supernatural isomorphisms.
* The equal-colour leftward crossing and the `♦`-cups and caps are data; their supernaturality
  inside the windows is the hypothesis `LeftwardData.IsSupernatural`.

Main declaration: `ProbeReservoir.swappedGens_supernatural`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-- The Hom-sector functor of one strand is a superfunctor. -/
private instance step_isSuperfunctor' (l : Letter I) (side : Bool) (s : Sector I)
    (hv : StepValid l side s) : IsSuperfunctor k (P.step l side s hv) := by
  obtain ⟨_ | _, i⟩ := l <;> cases side <;>
    (dsimp only [step, homContentPreE, homContentPreF, homContentPostE, homContentPostF];
      infer_instance)

/-- The Hom-sector functor of a path is a superfunctor. -/
private instance pathFunctor_isSuperfunctor' :
    {w : List (Col I X)} → {s t : Sector I} → (p : SPath w s t) →
      IsSuperfunctor k (P.pathFunctor p)
  | _, _, _, .nil _ => ⟨fun hf => hf⟩
  | _, _, _, .cons c side s hv p => by
    have := pathFunctor_isSuperfunctor' p
    exact ⟨fun hf => IsSuperfunctor.map_mem (F := P.step c.l side s hv)
      (IsSuperfunctor.map_mem (F := P.pathFunctor p) hf)⟩

/-! ## Chains of layers -/

/-- An entry of a layer at a decomposition of its top path is supernatural of the parity of
the generator of the layer. -/
theorem compLayerAt_supernatural {gens : P.Generators} (hs : GeneratorsSupernatural gens)
    (L : Layer (SKM.sig D)) {s t : Sector I} (p : SPath L.dom.word s t)
    (e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right s t) :
    IsSupernatural k (L.gen.1.parity D) (fun Z => compLayerAt gens L p e Z) := by
  classical
  unfold compLayerAt
  refine IsSupernatural.sum _ fun pg _ => ?_
  by_cases h : p = SPath.Dec.path (m := (SKM.sig D).dom L.gen) ⟨e.1, e.2.1, pg, e.2.2.2⟩
  · subst h
    simp only [dite_true, eqToHom_refl, Category.id_comp]
    have hx := ((hs L.gen pg e.2.2.1).whiskerLeft (P.pathFunctor e.2.2.2)).whiskerRight
      (P.pathFunctor e.2.1)
    exact IsSupernatural.of_eq_conj
      (by rw [SPath.Dec.path, pathFunctor_append, pathFunctor_append]; rfl)
      (by rw [SPath.Dec.path, pathFunctor_append, pathFunctor_append]; rfl) hx _
      (fun Z => P.pathFunctor_append_append_obj e.2.1 pg e.2.2.2 Z)
      (fun Z => (P.pathFunctor_append_append_obj e.2.1 e.2.2.1 e.2.2.2 Z).symm)
      fun Z => rfl
  · simp only [h, dite_false]
    exact isSupernatural_zero _

/-- An entry of a layer is supernatural of the parity of the generator of the layer. -/
theorem compLayer_supernatural {gens : P.Generators} (hs : GeneratorsSupernatural gens)
    (L : Layer (SKM.sig D)) {s t : Sector I} (p : SPath L.dom.word s t)
    (q : SPath L.cod.word s t) :
    IsSupernatural k (L.gen.1.parity D) (fun Z => compLayer gens L p q Z) := by
  unfold compLayer
  exact IsSupernatural.of_parity_eq ((compLayerAt_supernatural hs L p _).comp
    (isSupernatural_eqToHom (congrArg P.pathFunctor (SPath.path_decOf _ _ q)) _)) (add_zero _)

/-- **The entries of a chain of layers are supernatural**, of the total parity of the
generators of its layers, when the generator images are. -/
theorem compList_supernatural {gens : P.Generators} (hs : GeneratorsSupernatural gens) :
    ∀ (ls : List (Layer (SKM.sig D))) {a b : Obj (SKM.sig D)} (h : Chain a ls b)
      {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t),
      IsSupernatural k (ls.map fun L => L.gen.1.parity D).sum
        (fun Z => compList gens ls h p q Z)
  | [], a, b, h, s, t, p, q => by
    classical
    cases h
    by_cases hq : p = q
    · subst hq
      have e : ∀ Z, compList gens [] (rfl : Chain a [] a) p p Z = eqToHom rfl := fun Z => by
        rw [compList_nil]; simp
      simp only [e, List.map_nil, List.sum_nil]
      exact isSupernatural_eqToHom rfl _
    · have e : ∀ Z, compList gens [] (rfl : Chain a [] a) p q Z = 0 := fun Z => by
        rw [compList_nil]; simp [hq]
      simp only [e]
      exact isSupernatural_zero _
  | L :: ls, a, b, h, s, t, p, q => by
    classical
    obtain ⟨hv, rfl, hc⟩ := h
    let := Fintype.ofFinite (SPath L.cod.word s t)
    have e : ∀ Z, compList gens (L :: ls) ⟨hv, rfl, hc⟩ p q Z =
        ∑ pm, compLayer gens L p pm Z ≫ compList gens ls hc pm q Z := fun Z => by
      rw [compList_cons]; congr
    simp only [e, List.map_cons, List.sum_cons]
    exact IsSupernatural.sum _ fun pm _ =>
      (compLayer_supernatural hs L p pm).comp (compList_supernatural hs ls hc pm q)

/-! ## The upward generators and the sideways crossing -/

/-- **The upward generator images are supernatural** when the coefficient `a` of the
equal-colour mixed block is. -/
theorem upwardGens_supernatural (c : P.CrossCoeff) (hc : c.IsSupernatural) :
    GeneratorsSupernatural (P.upwardGens c) := by
  rintro ⟨g, ν⟩ t s p p'
  cases g with
  | dot i => exact P.dotImage_supernatural i ν p p'
  | cross i j => exact P.crossImage_supernatural c hc i j ν p p'
  | cup i => exact P.cupImage_supernatural i ν p p'
  | cap i => exact P.capImage_supernatural i ν p p'
  | lcross i j => exact isSupernatural_zero _
  | dcup i n => exact isSupernatural_zero _
  | dcap i n => exact isSupernatural_zero _

/-- **The entries of the sideways crossing `σ` are supernatural**, of parity `pᵢ pⱼ`. -/
theorem sigmaEntry_supernatural (c : P.CrossCoeff) (hc : c.IsSupernatural) (i j : I) (ν : X)
    {t s : Sector I} (p : SPath (wd D ν [up j, dn i]) t s)
    (q : SPath (wd D ν [dn i, up j]) t s) :
    IsSupernatural k (D.parity i * D.parity j) (fun Z => P.sigmaEntry c i j ν p q Z) := by
  unfold sigmaEntry
  refine IsSupernatural.of_parity_eq
    (compList_supernatural (upwardGens_supernatural c hc) (SKM.layList D ν (SKM.sigmaL i j))
      ((SKM.sChain_sigmaL i j).chain D ν) p q) ?_
  simp [SKM.layList, SKM.sigmaL, SKM.lay, SKM.Shape.parity]

/-- **The leftward crossing for distinct colours is supernatural**, of parity `pᵢ pⱼ`, when the
matrix of the sideways crossing is a permutation matrix with invertible entries. -/
theorem lcrossNeImage_supernatural (c : P.CrossCoeff) (hc : c.IsSupernatural) (i j : I)
    (ν : X) (hσ : P.SigmaPermutation c i j ν) {t s : Sector I}
    (p : SPath (wd D ν [dn i, up j]) t s) (p' : SPath (wd D ν [up j, dn i]) t s) :
    IsSupernatural k (D.parity i * D.parity j) (fun Z => P.lcrossNeImage c i j ν p p' Z) := by
  classical
  obtain ⟨f, h0, hiso⟩ := hσ t s
  by_cases hp : p = f p'
  · subst hp
    have e : ∀ Z, P.lcrossNeImage c i j ν (f p') p' Z =
        (@asIso _ _ _ _ _ (hiso p' Z)).inv := fun Z => by
      simp only [lcrossNeImage, hiso p' Z, dite_true, asIso_inv]
    simp only [e]
    exact isSupernatural_iso_inv _ (sigmaEntry_supernatural c hc i j ν p' (f p'))
  · have e : ∀ Z, P.lcrossNeImage c i j ν p p' Z = 0 := fun Z => by
      unfold lcrossNeImage
      split
      · exact inv_eq_zero_of_eq_zero _ _ (h0 p' p Z hp)
      · rfl
    simp only [e]
    exact isSupernatural_zero _

end ProbeReservoir

/-- Supernaturality of the equal-colour leftward data: the equal-colour leftward crossing has
parity `pᵢ²`, and the `♦`-cup and cap with label `n` have parity `pᵢ n` inside their windows
`n < ⟨hᵢ, ν⟩` and `n < -⟨hᵢ, ν⟩`. -/
structure ProbeReservoir.LeftwardData.IsSupernatural {P : ProbeReservoir k B D Sc}
    (L : P.LeftwardData) : Prop where
  lcrossSame : ∀ (i : I) (ν : X) {t s : Sector I} (p : SPath (wd D ν [dn i, up i]) t s)
    (p' : SPath (wd D ν [up i, dn i]) t s),
    StringDiagrams.Supercategory.IsSupernatural k (D.parity i * D.parity i)
      (fun Z => L.lcrossSame i ν p p' Z)
  dcup : ∀ (i : I) (n : ℕ) (ν : X), (n : ℤ) < D.h i ν → ∀ {t s : Sector I}
    (p : SPath (wd D ν (SKM.Shape.dcup i n).dom) t s)
    (p' : SPath (wd D ν (SKM.Shape.dcup i n).cod) t s),
    StringDiagrams.Supercategory.IsSupernatural k (D.parity i * n) (fun Z => L.dcup i n ν p p' Z)
  dcap : ∀ (i : I) (n : ℕ) (ν : X), (n : ℤ) < -D.h i ν → ∀ {t s : Sector I}
    (p : SPath (wd D ν (SKM.Shape.dcap i n).dom) t s)
    (p' : SPath (wd D ν (SKM.Shape.dcap i n).cod) t s),
    StringDiagrams.Supercategory.IsSupernatural k (D.parity i * n) (fun Z => L.dcap i n ν p p' Z)

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- **The swapped generator images are supernatural** (`GeneratorsSupernatural`), when the
coefficient `a` of the equal-colour mixed block is supernatural, the matrix of the sideways
crossing for distinct colours is a permutation matrix with invertible entries, and the
equal-colour leftward data are supernatural inside their windows. -/
theorem swappedGens_supernatural (c : P.CrossCoeff) (L : P.LeftwardData)
    (hc : c.IsSupernatural) (hσ : ∀ i j : I, i ≠ j → ∀ ν : X, P.SigmaPermutation c i j ν)
    (hL : L.IsSupernatural) : GeneratorsSupernatural (P.swappedGens c L) := by
  rintro ⟨g, ν⟩ t s p p'
  cases g with
  | dot i => exact P.dotImage_supernatural i ν p p'
  | cross i j => exact P.crossImage_supernatural c hc i j ν p p'
  | cup i => exact P.cupImage_supernatural i ν p p'
  | cap i => exact P.capImage_supernatural i ν p p'
  | lcross i j =>
    by_cases h : i = j
    · subst h
      have e : ∀ Z, (P.swappedGens c L).image (.lcross i i, ν) p p' Z =
          L.lcrossSame i ν p p' Z := fun Z => P.swappedGens_lcross_self c L i ν p p' Z
      simp only [e]
      exact hL.lcrossSame i ν p p'
    · have e : ∀ Z, (P.swappedGens c L).image (.lcross i j, ν) p p' Z =
          P.lcrossNeImage c i j ν p p' Z := fun Z => P.swappedGens_lcross_of_ne c L h ν p p' Z
      simp only [e]
      exact lcrossNeImage_supernatural c hc i j ν (hσ i j h ν) p p'
  | dcup i n =>
    by_cases h : D.h i ν ≤ n
    · have e : ∀ Z, (P.swappedGens c L).image (.dcup i n, ν) p p' Z = 0 := fun Z => by
        simp [Generators.image, swappedGens, h]
      simp only [e]
      exact isSupernatural_zero _
    · have e : ∀ Z, (P.swappedGens c L).image (.dcup i n, ν) p p' Z = L.dcup i n ν p p' Z :=
        fun Z => P.swappedGens_dcup_of_lt c L i n ν (not_le.mp h) p p' Z
      simp only [e]
      exact hL.dcup i n ν (not_le.mp h) p p'
  | dcap i n =>
    by_cases h : -D.h i ν ≤ n
    · have e : ∀ Z, (P.swappedGens c L).image (.dcap i n, ν) p p' Z = 0 := fun Z => by
        simp [Generators.image, swappedGens, h]
      simp only [e]
      exact isSupernatural_zero _
    · have e : ∀ Z, (P.swappedGens c L).image (.dcap i n, ν) p p' Z = L.dcap i n ν p p' Z :=
        fun Z => P.swappedGens_dcap_of_lt c L i n ν (not_le.mp h) p p' Z
      simp only [e]
      exact hL.dcap i n ν (not_le.mp h) p p'

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
