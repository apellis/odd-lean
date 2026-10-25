import OddMath.SKM.SourceAdaptedChoices
import OddMath.SKM.SourceAdaptedDistinctChoices

open OddMath.SKM
#print axioms exists_source_same_colour_adapted_equiv
#print axioms exists_source_adapted_distinct_colour_choices
#check exists_source_same_colour_adapted_choices (I := Fin 2) [] [] [] false 0
#check exists_source_same_colour_adapted_equiv (I := Fin 2) [] [] [] true 0
#check exists_source_adapted_distinct_colour_choices (I := Fin 2)
  [(false, 0), (true, 1)] [] [] (false, 0) (true, 1) (by decide)
