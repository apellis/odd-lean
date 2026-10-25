#!/usr/bin/env python3
"""Connected two-odd-colour upward local test, not a categorical action.

Cartan off-diagonal -2, Q(x,y)=x²+y². Two copies of the existing
degree-two exterior reservoir, with word-parity shift on the reversed word.
Checks dot/crossing/quadratic relations and retains δ_i δ_j. No braid,
adjunction, mixed EF inversion, or bubble evaluation is asserted.
"""
import sympy as s


def run():
    one=s.eye(2); zero=s.zeros(2); d=s.Matrix([[0,0],[1,0]])
    p=s.diag(1,-1)
    delta=s.kronecker_product(p,d)
    x=s.BlockMatrix([[zero,zero],[one,-d]]).as_explicit()
    parity=s.kronecker_product(p,p)
    assert x*x+x*delta == s.zeros(4)
    assert x**3 == s.zeros(4) and x*x != s.zeros(4)
    assert delta*x+x*delta == s.zeros(4)
    X=s.kronecker_product(x,s.eye(4))
    Y=s.kronecker_product(parity,x)
    D=s.kronecker_product(delta,s.eye(4))
    E=s.kronecker_product(parity,delta)
    P=s.kronecker_product(parity,parity)
    ps=[0,1,1,0]
    S=s.zeros(16)
    for a in range(4):
        for b in range(4):
            S[4*b+a,4*a+b]=(-1)**(ps[a]*ps[b])
    J=P*S
    Q=X*X+Y*Y
    forward=J
    backward=Q*J
    z=s.zeros(16)
    assert X*Y+Y*X == z
    assert D*E+E*D == z and D*D == E*E == z
    assert D*E != z
    # Target order is j,i: colour-specific coefficient D becomes E there.
    for crossing in (forward,backward):
        assert crossing*X+Y*crossing == z
        assert crossing*Y+X*crossing == z
        assert crossing*D+E*crossing == z
        assert crossing*E+D*crossing == z
        # Opposite word summands have parities P and -P.
        assert (-P)*crossing+crossing*P == z
    assert backward*forward == Q and forward*backward == Q
    assert Q**3 == z and Q**2 != z
    # Plain disconnected transport would violate this connected relation.
    assert J*J == s.eye(16) and J*J != Q
    # Independent exterior product is transported with the two odd signs;
    # coefficient order reverses because the target word is j,i.
    assert forward*(D*E) == (E*D)*forward
    # This cutoff is NOT a joint PBW/coefficient detector: the nonzero
    # mixed exterior product is killed by the reverse crossing.
    assert Q*D*E == z and backward*D*E == z
    print(f"PASS connected Q=x²+y²: forward rank {forward.rank()}, "
          f"backward rank {backward.rank()}, Q rank {Q.rank()}")
    print(f"PASS exterior product rank {(D*E).rank()}, Q nilpotence index 3; "
          "odd shifted parity, dot/coefficient transport, quadratic relations")
    print("PASS disconnected-crossing negative control; no full action claim")
    print("LIMIT: reverse crossing times δ_i δ_j vanishes at this cutoff")


if __name__ == "__main__":
    run()
