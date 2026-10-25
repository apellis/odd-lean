#!/usr/bin/env python3
"""Local algebraic shadow of a third-colour bubble/crossing diamond.

No bubble functor/action is constructed. This tests the even polynomial
transport identity underlying the already proved connected slide formula.
"""
from cyclotomic_score_audit import Reducer


def run():
    checks = 0
    mixed, same = Reducer(True), Reducer(False)
    for a in range(5):
        for b in range(5):
            monomial = ("x",)*(2*a)+("y",)*(2*b)
            swapped = ("x",)*(2*b)+("y",)*(2*a)
            # Distinct colours transport each strand's factor to its new
            # position; the factors may have entirely different coefficients.
            assert mixed.polynomial([(1,("t",)+monomial),
                                     (-1,swapped+("t",))]) == {}
            # For a same-colour crossing the two slide factors agree; their
            # product is symmetric in x²,y², killing the divided difference.
            symmetric = [monomial,swapped] if a != b else [monomial]
            assert same.polynomial([(1,("t",)+w) for w in symmetric]+
                                   [(-1,w+("t",)) for w in symmetric]) == {}
            checks += 2
    # An unsymmetrized factor does have the expected odd nilHecke residual.
    residual = same.polynomial([(1,tuple("txx")),(-1,tuple("yyt"))])
    assert residual == {("x",):1,("y",):-1}
    assert same.polynomial([(1,tuple("tdexxyy")),
                            (-1,tuple("dexxyyt"))]) == {}
    print(f"PASS {checks} polynomial transport/centrality checks; "
          "nonzero one-factor residual and independent exterior-pair controls")


if __name__ == "__main__":
    run()
