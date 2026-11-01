# Ordinary-right covariance of the actual mate coefficient kernel

`ELVMateKernelNaturality.actualMateKernel` is a natural map from the concrete ordinary-right IndResKernel.kernel to the actual upper Hom inductionKernel. Its components are the fixed typed matrixMateComponent followed by the canonical co-Yoneda comparison; the source carrier comparison is a literal reflexive linear equivalence.

`actualMateKernelComponent_precompose` proves covariance for every old source arrow a, including inhomogeneous arrows: source b ↦ a composed with b becomes left composition by append(a) on the output. The ordered mate tensor formula twists only the first factor g; the full coefficient b remains untwisted. This is the ordinary-right convention required for the explicit kernel tensor, rather than a conclusion about only even module maps.

Verification: producer and concrete mixed-parity/mixed-endpoint consumer passed strict local checks, with all 19 owned declarations including private/generated audited. Full branch CI is pending. The branch starts from the full current research tree and adds only missing exact checked prerequisite producers, consumers and topic notes from 881, 883 and 886; existing research files are retained.

Remaining scope: dot/counit power row covariance, the finite normalized matrix coefficient map and its parity, and tensor realization of the whole arbitrary-module inverse. This first-entry naturality result alone does not assert the completed matrix or action.

The kernel-object endpoint alias actualMateKernelLinear and its separate raw linear-map equality keep application proofs in the exact ModuleCat kernel objects. This changes no signed map or covariance statement; both the producer and paired consumer were rechecked after the encoding change.


The stored matrixMateRow now receives a separately named oldSourceKernelLinear with its exact module endpoint. The component is constructed after both old endpoints are in word coordinates, and its boxed getter exposes only the composition of those two named linear maps. This preserves the original source-equivalence API and the ordered signed mate formula. The revised endpoint encoding and its concrete row consumer await strict checking.
