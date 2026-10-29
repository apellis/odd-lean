/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Generators.Leftward

/-! # The generator images of the swapped action

The images of all generators of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5 and (2.6), in the swapped Hom construction
(`docs/Nondegeneracy/SwappedActionAssembly.md`): `swappedGens c L` has the upward generators
of `upwardGens c`, the leftward crossing `lcrossNeImage` for distinct colours, and the
equal-colour leftward crossing and `♦`-cups and caps of the data `L`.

`compList_congr`: the entries of a chain of layers only depend on the images of the
generators in its layers. Hence the entries of `σ = sigmaL i j` for `swappedGens c L` are
those for `upwardGens c` (`compList_sigmaL_swappedGens`).
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u uB v w

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

open Classical in
/-- **The generator images of the swapped action**, for a coefficient `c` of the equal-colour
mixed block of the upward crossing and the equal-colour leftward data `L`. -/
def swappedGens (c : P.CrossCoeff) (L : P.LeftwardData) : P.Generators where
  dot := P.dotImage
  cross := P.crossImage c
  cup := P.cupImage
  cap := P.capImage
  lcross i j ν :=
    if h : i = j then by subst h; exact L.lcrossSame i ν else P.lcrossNeImage c i j ν
  dcup := L.dcup
  dcap := L.dcap

theorem swappedGens_lcross_of_ne (c : P.CrossCoeff) (L : P.LeftwardData) {i j : I}
    (h : i ≠ j) (ν : X) {t s : Sector I} (p : SPath (wd D ν [dn i, up j]) t s)
    (p' : SPath (wd D ν [up j, dn i]) t s) (Z : P.H s) :
    (P.swappedGens c L).lcross i j ν p p' Z = P.lcrossNeImage c i j ν p p' Z := by
  simp [swappedGens, h]

theorem swappedGens_lcross_self (c : P.CrossCoeff) (L : P.LeftwardData) (i : I) (ν : X)
    {t s : Sector I} (p : SPath (wd D ν [dn i, up i]) t s)
    (p' : SPath (wd D ν [up i, dn i]) t s) (Z : P.H s) :
    (P.swappedGens c L).lcross i i ν p p' Z = L.lcrossSame i ν p p' Z := by
  simp [swappedGens]

variable {P}

/-- The entries of a chain of layers only depend on the images of the generators in its
layers. -/
theorem compList_congr (gens gens' : P.Generators) (ls : List (Layer (SKM.sig D)))
    (hls : ∀ L ∈ ls, ∀ {t s : Sector I} (p : SPath (wd D L.gen.2 L.gen.1.dom) t s)
      (p' : SPath (wd D L.gen.2 L.gen.1.cod) t s) (Z : P.H s),
      gens.image L.gen p p' Z = gens'.image L.gen p p' Z) {a b : Obj (SKM.sig D)}
    (h : Chain a ls b) {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t)
    (Z : P.H t) : compList gens ls h p q Z = compList gens' ls h p q Z := by
  induction ls generalizing a s with
  | nil => rfl
  | cons L ls ih =>
    have hL := @hls L List.mem_cons_self
    have hr : ∀ L' ∈ ls, ∀ {t s : Sector I} (p : SPath (wd D L'.gen.2 L'.gen.1.dom) t s)
        (p' : SPath (wd D L'.gen.2 L'.gen.1.cod) t s) (Z : P.H s),
        gens.image L'.gen p p' Z = gens'.image L'.gen p p' Z :=
      fun L' hL' => hls L' (List.mem_cons_of_mem _ hL')
    simp only [compList, compLayer, compLayerAt, hL, ih hr]

/-- The entries of the sideways crossing for the swapped generators are those for the
upward generators. -/
theorem compList_sigmaL_swappedGens (c : P.CrossCoeff) (L : P.LeftwardData) (i j : I)
    (ν : X) {t s : Sector I} (p : SPath (wd D ν [up j, dn i]) t s)
    (q : SPath (wd D ν [dn i, up j]) t s) (Z : P.H s) :
    compList (P.swappedGens c L) (SKM.layList D ν (SKM.sigmaL i j))
        ((SKM.sChain_sigmaL i j).chain D ν) p q Z =
      P.sigmaEntry c i j ν p q Z := by
  refine compList_congr _ _ _ ?_ ((SKM.sChain_sigmaL i j).chain D ν) p q Z
  intro L' hL'
  simp only [SKM.layList, SKM.sigmaL, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hL'
  rcases hL' with rfl | rfl | rfl <;> intros <;> rfl

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
