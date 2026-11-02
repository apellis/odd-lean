# An occupied exterior-coefficient principal cap

The consumer `scripts/NonVacuity/SwappedOddCapExterior.lean` checks the
height-zero odd cap calculation at N=P=2 with a nonzero exterior coefficient.
It supports research issue #345 and
[InverseCapMoments](InverseCapMoments.md), rather than constructing the
full factor or swapped action.

Take the coefficient superspace with basis (1,delta), where delta is odd
and delta²=0. The word superspace has basis (1,delta,t,delta t), with even
part spanned by 1 and delta t. Its unsigned reservoir relation is

    t²+delta t=0.

In functional order, the signed probe and reservoir dots send

    x:(1,delta,t,delta t) -> (t,-delta t,-1,delta),
    y:(1,delta,t,delta t) -> (t,-delta t,delta t,0).

Thus x²=-1; y² is nonzero, so replacing the signed dot by an unsigned
nilpotent would lose information. Let u insert the coefficient module,
and let ell(t)=1, ell(delta t)=-delta, ell(1)=ell(delta)=0. Set v=ell.
The even map s defined by

    s(1)=-1+delta t, s(delta)=-delta,
    s(t)=t,         s(delta t)=delta t

is its own inverse. Every input of `principal_inverse_cap` is proved:

    y s+s x=u v,
    ell u=0,  ell y u=1,
    g(x)=0,   g(T)=T²+1.

The source and target exterior multipliers are nonzero square-zero odd
maps. Both dots and ell anticommute with the appropriate exterior
multiplier; u and s commute with it. These equations verify the required
superlinearity against the exterior generator. The dots and ell are odd,
while u and s are even in the displayed superspaces.

The generic principal-cap theorem consequently gives

    v s^-1=ell g(y).

The consumer also checks the first moments directly:

    K_1=-delta, K_2=1, K_3=-delta.

In particular the first odd moment retains the predicted
`(-1)^(N+1)delta` sign on a nonzero exterior direction. This is stronger
than a scalar specialization killing delta, but it remains one occupied
model. It proves no general bubble series or action attachment. The
consumer passes scoped Lean checking with warnings as errors; full CI is
the integration gate.
