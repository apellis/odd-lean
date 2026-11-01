# Dotted cap sign normalization

Status: full build with warnings as errors, global axiom audit and concrete consumers passed before research integration in #803.

ELVCapSignNormalization defines the prescribed cap scalar e_n and proves its exponent is exactly n(n+1)/2. It proves e_n sgn(n) (T composed with sgn(1))^n = T^n for an odd operator on a superspace. The concrete induction dot supplies the odd-operator hypothesis in the categorical cap-row comparison; this is an intermediate linear-algebra identity, not a matrix or action theorem.

The remaining concrete comparison uses canonical odd J, T_shift J = -J T_unshift, X = T_shift sgn_source(1), and the actual even counit square. These imply XJ = J(T_unshift sgn_unshift(1)); iteration and even counit sign-commutation reduce the prescribed cap row to this identity. No arbitrary-J premise will be introduced into the concrete result.
