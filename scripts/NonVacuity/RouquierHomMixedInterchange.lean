import OddMath.SKM.RouquierHomMixedInterchange

/-! Odd rank-one consumers of the prescribed content-shifted J.
The factor families are inputs; this does not construct a detector or
claim the finite expansion of the rational coefficient. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomMixedInterchange

private def oddDatum : Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two

variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  (T W : RouquierFamily (k := k) (B := B) oddDatum)
  (β : Unit →₀ ℕ) (Z : homWeightSector T.obj W.obj (-2) 0)

private theorem edge : -(0 : ℤ) + oddDatum.α () = -(-2) := rfl
private theorem postEdge : (0 : ℤ) + oddDatum.α () = 2 := rfl

/-- The actual pre dot anticommutes through J. -/
example :
    T.dot () edge ▷ (homContentPostE T.obj W () β (-2) postEdge).obj Z ≫
        (homContentMixedInterchange T W () β edge postEdge Z).hom =
      -((homContentMixedInterchange T W () β edge postEdge Z).hom ≫
        (homContentPostE T.obj W () (β + Finsupp.single () 1) 0 postEdge).map
          (T.dot () edge ▷ Z)) := by
  have h := homContentMixedInterchange_pre T W () β edge postEdge Z
  simp only [oddDatum, koszulSign_one_one, neg_one_smul] at h
  exact h

/-- The actual reservoir post dot has the same minus sign. -/
example :
    (homContentPreE T W.obj () 2 edge).map (homContentPostDot T.obj W () β (-2) postEdge Z) ≫
        (homContentMixedInterchange T W () β edge postEdge Z).hom =
      -((homContentMixedInterchange T W () β edge postEdge Z).hom ≫
        homContentPostDot T.obj W () (β + Finsupp.single () 1) 0 postEdge (T.E () edge ≫ Z)) := by
  have h := homContentMixedInterchange_post T W () β edge postEdge Z
  simp only [oddDatum, koszulSign_one_one, neg_one_smul] at h
  exact h

/-- The pre and post dots anticommute on the same AB object. -/
example :
    (homContentPostE T.obj W () (β + Finsupp.single () 1) 0 postEdge).map (T.dot () edge ▷ Z) ≫
        homContentPostDot T.obj W () (β + Finsupp.single () 1) 0 postEdge (T.E () edge ≫ Z) =
      -(homContentPostDot T.obj W () (β + Finsupp.single () 1) 0 postEdge (T.E () edge ≫ Z) ≫
        (homContentPostE T.obj W () (β + Finsupp.single () 1) 0 postEdge).map (T.dot () edge ▷ Z)) := by
  have h := homContentMixedDot_exchange T W () β edge postEdge Z
  simp only [oddDatum, koszulSign_one_one, neg_one_smul] at h
  exact h

example := homContentMixedInterchange_mem T W () β edge postEdge Z
example := homContentMixedInterchange_pre_square T W () β edge postEdge Z
example := homContentMixedInterchange_post_square T W () β edge postEdge Z

/-- The two content parities really differ, including a nonzero content. -/
example : homContentShift oddDatum () 0 = 0 := by decide
example : homContentShift oddDatum () (Finsupp.single () 1) = 1 := by
  simp [homContentShift, oddDatum]

example (a : End ((homContentPostE T.obj W () (β + Finsupp.single () 1) 0 postEdge).obj
    ((homContentPreE T W.obj () 0 edge).obj Z))) :
    homContentMixedSwap T W () β edge postEdge Z a ≫
      (homContentMixedInterchange T W () β edge postEdge Z).hom = -(a ≫ a) :=
  (homContentMixedSwap_products T W () β edge postEdge Z a).1

#print axioms homMixedInterchange_mem
#print axioms homMixedInterchange_products
#print axioms homMixedInterchange_pre
#print axioms homMixedInterchange_post
#print axioms homMixedInterchange_dot_exchange
#print axioms homContentMixedInterchange_mem
#print axioms homContentMixedInterchange_pre
#print axioms homContentMixedInterchange_post
#print axioms homContentMixedDot_exchange
#print axioms homContentMixedInterchange_pre_square
#print axioms homContentMixedInterchange_post_square
#print axioms homContentMixedSwap_products
end NonVacuity.RouquierHomMixedInterchange
