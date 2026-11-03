# Nondegeneracy source history

The branch follows [FieldScopeBoundary](FieldScopeBoundary.md): symmetrizable
homogeneous parameters first, inhomogeneous parameters second; no
nonsymmetrizable proof is pursued. The endpoint is the odd analog of the cited
even benchmark, with a checked all-even specialization and 2 invertible.
Historical proposals below do not enlarge that scope.

The primary branch is `research/odd-nondegeneracy`. Its consolidation retains
every retired topic head below as a reachable ancestor, including superseded
proofs and unfinished attempts. No source can be lost by deleting these branch
refs. Use `git show <commit>:<path>` or the commit link to inspect an attempt.

This index records provenance, not completed results. Active mathematical scope
and verification are in [STATUS](STATUS.md); the four current unfinished repair
restart points and next dependencies are in [HANDOFF](HANDOFF.md). Historical
notes and PR descriptions do not override those files. Integration selected the
checked successor sources rather than replacing them with older versions.

| Retired topic | Preserved commit |
| --- | --- |
| `research/raw-even-mate` | [2925c6f92a](https://github.com/apellis/odd-lean/commit/2925c6f92aa8ae1bdfd3289efbd9a478c6f302ec) |
| `research/distinct-mate` | [3e53f42238](https://github.com/apellis/odd-lean/commit/3e53f4223816ac1847c2aa5657ffcc0bc7821aaf) |
| `research/weight-crossing-assembly` | [7804284a57](https://github.com/apellis/odd-lean/commit/7804284a57a7fbcc6e9d59f7ff68bd52ee92e4d4) |
| `research/weighted-append-transport` | [7bf6ea3513](https://github.com/apellis/odd-lean/commit/7bf6ea3513a02f488cae55cd5abfeab8c27f3172) |
| `research/induction-transform-square` | [445e087cf7](https://github.com/apellis/odd-lean/commit/445e087cf78704846bd8ec693fc04e45d1c7d1f0) |
| `research/unit-coefficient-rows` | [adf2ebd8ce](https://github.com/apellis/odd-lean/commit/adf2ebd8cea3ee626ddb73563d9788f604c05094) |
| `research/scalar-append-transport` | [4495bdff24](https://github.com/apellis/odd-lean/commit/4495bdff24bd18d9901cd22ca68799d8af0d36ae) |
| `research/content-append-dot` | [29e4f0553d](https://github.com/apellis/odd-lean/commit/29e4f0553d6ab6adda3f38b17e99fad87ca6c8f4) |
| `-append-left` | [f8fb8e92c6](https://github.com/apellis/odd-lean/commit/f8fb8e92c628c4704dacd65fbdf1ee3a2b6ce6d0) |
| `-cap-family-coordinates` | [b1fbed5b3b](https://github.com/apellis/odd-lean/commit/b1fbed5b3b5f638aba4e0119b28ebc3038f27494) |
| `-coend-ordinary-PBW-1030` | [773b5fd07f](https://github.com/apellis/odd-lean/commit/773b5fd07f0a48b350580d0b1f1d056bdf8e8d0c) |
| `-coend-snake-1030` | [85be14a564](https://github.com/apellis/odd-lean/commit/85be14a5640f66fbedca350d42df44a22f552ae1) |
| `-columns-row-word-integration-1030` | [e0be3b7469](https://github.com/apellis/odd-lean/commit/e0be3b7469728d22ebf1b7218047693011900b6b) |
| `-content-assoc-map-ext-1030` | [ea8654c51a](https://github.com/apellis/odd-lean/commit/ea8654c51a8f93021f234df05683ea0c61cb96e4) |
| `-content-extension-append` | [31a3dd05f6](https://github.com/apellis/odd-lean/commit/31a3dd05f6267ac76d4a3a66065f0dd5f40a600e) |
| `-content-extension-unit` | [18536af1c9](https://github.com/apellis/odd-lean/commit/18536af1c90020ae734aea9b9237e2a1441969ff) |
| `-content-matrix-components` | [d632a72e59](https://github.com/apellis/odd-lean/commit/d632a72e5952a7e26a55fe52108617d2dc33fe4b) |
| `-content-matrix-height` | [28a494efbc](https://github.com/apellis/odd-lean/commit/28a494efbc4bc4dfdb8210275e2ddfebedc0c952) |
| `-content-unit-append-integration` | [5795962dbc](https://github.com/apellis/odd-lean/commit/5795962dbce6a33909510b18060fe30205b22f85) |
| `-cyclotomic-snake-1030` | [d2e672725d](https://github.com/apellis/odd-lean/commit/d2e672725d79f1d068e3b303b0e8c68c73c6176c) |
| `-distinct-unit-corners` | [e7750d90a2](https://github.com/apellis/odd-lean/commit/e7750d90a240438878f5cdd6946e64cba8dea826) |
| `-even-boundary-row-1030` | [eadd735a74](https://github.com/apellis/odd-lean/commit/eadd735a74b9c60e5316c2fcfde451f014874b77) |
| `-even-crossing-kernel` | [185b67b2c7](https://github.com/apellis/odd-lean/commit/185b67b2c7667fe40209f89c3ca874efb94e83c2) |
| `-even-input-matrix` | [43a1aab2b7](https://github.com/apellis/odd-lean/commit/43a1aab2b78e163e7003ec080d7717f2a85f6ed2) |
| `-even-positive-crossing` | [10600959d3](https://github.com/apellis/odd-lean/commit/10600959d39f5da623de1d96e2f19abdf4c75659) |
| `-even-row-division` | [d1bb531819](https://github.com/apellis/odd-lean/commit/d1bb53181923503af82faa4733a44e38d24fe05c) |
| `-even-unit-positive-inverse` | [17c1830cb9](https://github.com/apellis/odd-lean/commit/17c1830cb9e158c224b18409f90807460b2b6c0a) |
| `-finite-colour-naturality` | [337de2adfb](https://github.com/apellis/odd-lean/commit/337de2adfbbc7f110774f2f9a3f2d8ec6eba0135) |
| `-finite-matrix-components` | [8b1212f673](https://github.com/apellis/odd-lean/commit/8b1212f673b2810d91a25721d0b487d1ae4db52f) |
| `-graded-kernel-equivalence` | [1728052d1d](https://github.com/apellis/odd-lean/commit/1728052d1d58bc087279841561ba82ffce81ba48) |
| `-kernel-grading-integration` | [c4f031bcbf](https://github.com/apellis/odd-lean/commit/c4f031bcbf9628b7219cc7b069346581048c3a00) |
| `-kernel-off-content-matrices` | [8d6930d46e](https://github.com/apellis/odd-lean/commit/8d6930d46ea346b61ba5437c57cf460083934d0f) |
| `-kernel-tensor-grading` | [b69595bb6a](https://github.com/apellis/odd-lean/commit/b69595bb6a0d28b56afc8a6bb78b2e87742df63c) |
| `-low-polynomial-coordinates` | [a04c558d87](https://github.com/apellis/odd-lean/commit/a04c558d878b9474c343b57c79e1cb511e089ff4) |
| `-positive-crossing` | [2253447ef6](https://github.com/apellis/odd-lean/commit/2253447ef61ab0e4ff74201e331c2665a67fdea9) |
| `-prescribed-target-matrix-1030` | [74803502cc](https://github.com/apellis/odd-lean/commit/74803502cc144d7de3f566e93a4e1fd512f9b254) |
| `-probe-append-specialization` | [774785c7d2](https://github.com/apellis/odd-lean/commit/774785c7d25c3e63db78a5964f6fedb772518dea) |
| `-probe-entry-parity` | [c525a41bc9](https://github.com/apellis/odd-lean/commit/c525a41bc94d87ced82c24883826c58020bbb01e) |
| `-probe-old-dot-unit` | [ddbc657d76](https://github.com/apellis/odd-lean/commit/ddbc657d762523b8755a9cfdfe5fc86b1a1bd07d) |
| `-probe-polynomial-parity` | [e8ff334927](https://github.com/apellis/odd-lean/commit/e8ff334927112c648cfd83fef7ee0f91d38c7542) |
| `-representable-braid-1030` | [6df6aab80d](https://github.com/apellis/odd-lean/commit/6df6aab80ddee660aa232d9ee41c8d0dd219f51c) |
| `-unit-family-coordinates` | [aa8692d6f8](https://github.com/apellis/odd-lean/commit/aa8692d6f87b897115d9b538e8cfc09c9feb8643) |
| `-vacuum-word-pairing-1030` | [544e156ccf](https://github.com/apellis/odd-lean/commit/544e156ccfae0cfe2bd3edf07d267e20989faef3) |
| `-weight-rouquier-kernels` | [88810be279](https://github.com/apellis/odd-lean/commit/88810be279f763cae411d17a2ae452e71255789f) |
| `-whiskered-braid-composition-1030` | [a8af0c729a](https://github.com/apellis/odd-lean/commit/a8af0c729a7f0817c351db34c746f3ee5b90216a) |
| `-wip/accepted-braid-r34` | [933f574391](https://github.com/apellis/odd-lean/commit/933f57439157cbe6ba9f29ad48e4cffb28f7cb8f) |
| `-wip/accepted-braids-r41` | [adc09e4452](https://github.com/apellis/odd-lean/commit/adc09e445225576cefc4b20fe72bf6d83b027ff7) |
| `-wip/accepted-iji-r40` | [5acc39242d](https://github.com/apellis/odd-lean/commit/5acc39242d8e77e00f1e21b7daf0ee97d6837c12) |
| `-wip/accepted-inverse-r36` | [6780903eb3](https://github.com/apellis/odd-lean/commit/6780903eb3889410619be86cb09c821a59df9c8b) |
| `-wip/accepted-inversion-r37` | [8b21a5e11c](https://github.com/apellis/odd-lean/commit/8b21a5e11cb004ef13331d16f632cd26bf195837) |
| `-wip/accepted-paired-r38` | [24cd37606d](https://github.com/apellis/odd-lean/commit/24cd37606d4a472e87cd25a6fa92c1caa4a632ba) |
| `-wip/accepted-probe-mixed-r39` | [9f73c799c2](https://github.com/apellis/odd-lean/commit/9f73c799c23ce4d17eeab28028b5c7e473d9f396) |
| `-wip/accepted-transport-r42` | [2c2f26565e](https://github.com/apellis/odd-lean/commit/2c2f26565e1ee30bde2f04e59f428b8bb0d10b9a) |
| `-wip/action` | [4956bb8ee4](https://github.com/apellis/odd-lean/commit/4956bb8ee474b03093d452c20e0cf1e774c68620) |
| `-wip/action-r4-salvage` | [979813c2cc](https://github.com/apellis/odd-lean/commit/979813c2cc4c6bca9eaffedbc1cedd02d1c06b9b) |
| `-wip/actual-cap-input` | [c27846cdda](https://github.com/apellis/odd-lean/commit/c27846cdda2e834ff5bf7cc82e3d8fb94dfcf79d) |
| `-wip/actual-cap-parity` | [c1643d2289](https://github.com/apellis/odd-lean/commit/c1643d22898a49a672b18fb4c89e58b41a3fd5c1) |
| `-wip/append-balance` | [09d41c792a](https://github.com/apellis/odd-lean/commit/09d41c792a7e4d8e63ff58d17d2d4c4ff3617576) |
| `-wip/append-quotient-generators` | [e388f5a218](https://github.com/apellis/odd-lean/commit/e388f5a2186d526efa72f6586b22d3c82b106e64) |
| `-wip/braid-normalization-r33` | [36a19d24f5](https://github.com/apellis/odd-lean/commit/36a19d24f55778ac196275bfc09b40ea845e2d4f) |
| `-wip/cancellation-review-r9` | [2326be6752](https://github.com/apellis/odd-lean/commit/2326be6752b8a0988fe129865a6a1209cd500679) |
| `-wip/canonical-source-equivalence` | [a7c643adc5](https://github.com/apellis/odd-lean/commit/a7c643adc5df240476936d78219ebe811bb764e0) |
| `-wip/cap-input-pivots` | [a1c8428faa](https://github.com/apellis/odd-lean/commit/a1c8428faafa70545411d53d05c7618317eba8ad) |
| `-wip/cap-kernel-naturality` | [90602d4601](https://github.com/apellis/odd-lean/commit/90602d460142610411e0259219ddcb313234758a) |
| `-wip/cap-representative-powers` | [8661f4991f](https://github.com/apellis/odd-lean/commit/8661f4991f8b2f1d26adf59a3254c35dddcb67e9) |
| `-wip/cap-swap-r13` | [6e46abfde9](https://github.com/apellis/odd-lean/commit/6e46abfde956753b03f42158b8a3d9dc5f74cbdc) |
| `-wip/central-feedback-r30` | [d658727672](https://github.com/apellis/odd-lean/commit/d6587276724195731cf007c99b754d941f091dec) |
| `-wip/checkpoint-20261027` | [22c0d052a3](https://github.com/apellis/odd-lean/commit/22c0d052a31eb1607f84f139e7490d34fbcdbedb) |
| `-wip/consequences` | [ef78ea002c](https://github.com/apellis/odd-lean/commit/ef78ea002c7e9381cede2faffa88adf23c6274b4) |
| `-wip/content-append-tensor` | [70bdb23ad2](https://github.com/apellis/odd-lean/commit/70bdb23ad2bafbbb06cefc8aab5b749f84b23f47) |
| `-wip/content-dot-transforms` | [f954aac008](https://github.com/apellis/odd-lean/commit/f954aac008cd7d19d8fa8443b737e9bcc7ed00a6) |
| `-wip/content-inner-unit` | [71ebe44541](https://github.com/apellis/odd-lean/commit/71ebe445416e3633d6d0d9dbf8be20677eb2a129) |
| `-wip/content-natural-braid` | [542ed4f7aa](https://github.com/apellis/odd-lean/commit/542ed4f7aa7eaaf93a2310e209aa69917a2006fa) |
| `-wip/content-relations` | [6f7a7bde30](https://github.com/apellis/odd-lean/commit/6f7a7bde307297c757eab991ba49efb1721b05ab) |
| `-wip/content-restriction-extension` | [14a112d6d1](https://github.com/apellis/odd-lean/commit/14a112d6d1e9244f4216c116f09d04d63bd44b1e) |
| `-wip/content-restriction-tensor` | [96a98ec56a](https://github.com/apellis/odd-lean/commit/96a98ec56afb412d6fbff14af4b93c18c942993b) |
| `-wip/crossing-normalization-r32` | [814c6ecf00](https://github.com/apellis/odd-lean/commit/814c6ecf00ebe8882122756e81c715a12c49f16b) |
| `-wip/deformed-top-row-r48` | [bd43599c2d](https://github.com/apellis/odd-lean/commit/bd43599c2d3d59040d143a81ed7dd84a0faa694f) |
| `-wip/detecting-family-r50` | [45de687c46](https://github.com/apellis/odd-lean/commit/45de687c4676c16034133256755866ab222314cb) |
| `-wip/detection` | [1ef68d42a5](https://github.com/apellis/odd-lean/commit/1ef68d42a59acc69bf090f1160a1be32d645b493) |
| `-wip/elv-factor` | [a7f3fcad1a](https://github.com/apellis/odd-lean/commit/a7f3fcad1abed3671aa27951efbfc5a2f463f7ea) |
| `-wip/elv-weight-denominator-units` | [91749cf2e7](https://github.com/apellis/odd-lean/commit/91749cf2e7d7f97d05b50e17769aa10987f582ff) |
| `-wip/elv-weight-pair-induction` | [ba814a346e](https://github.com/apellis/odd-lean/commit/ba814a346e4e97573551c8a0d082e7da5b9f4168) |
| `-wip/even-boundary-recurrence` | [72d06e6d9c](https://github.com/apellis/odd-lean/commit/72d06e6d9c94688e83ed51bd6b1de6e19cad4033) |
| `-wip/even-input-operators` | [309af54e20](https://github.com/apellis/odd-lean/commit/309af54e206a0bb86483e799f44eb8d9d22fa002) |
| `-wip/even-input-pivots` | [c751285aa9](https://github.com/apellis/odd-lean/commit/c751285aa9d46c18d25575b7380686522ceb4e3c) |
| `-wip/even-polynomial-boundary` | [e9f8b425ee](https://github.com/apellis/odd-lean/commit/e9f8b425ee61c20f2086e0ecd47df06ebc2d5032) |
| `-wip/even-prescribed-mixed-mate` | [36f1a8c68a](https://github.com/apellis/odd-lean/commit/36f1a8c68a4bbcde622ae55529bbfa2607db8228) |
| `-wip/finite-colour-naturality` | [9fdb77ff5b](https://github.com/apellis/odd-lean/commit/9fdb77ff5b6a0f307cabc244e0e31897d99706c6) |
| `-wip/finite-derivation` | [d1d61a4a07](https://github.com/apellis/odd-lean/commit/d1d61a4a07a48449eda40f8b7fc62af43f6d53a5) |
| `-wip/finite-kernel-grading` | [17e33d18ef](https://github.com/apellis/odd-lean/commit/17e33d18efd3ba0c275e4737787fd88296d777a0) |
| `-wip/finite-presentation-equality` | [098e5f4e9f](https://github.com/apellis/odd-lean/commit/098e5f4e9fd737468674721daf852a2abaa699ff) |
| `-wip/full-elv-action-r17` | [4a63ee95f0](https://github.com/apellis/odd-lean/commit/4a63ee95f006989e7281da4f02a60bdabf0b7cd6) |
| `-wip/fused-feedback-r23` | [ff3c0ca948](https://github.com/apellis/odd-lean/commit/ff3c0ca9483254afaa5c3aa3eb963e5ce7e21b4a) |
| `-wip/fused-window-r8` | [9029e6cefa](https://github.com/apellis/odd-lean/commit/9029e6cefa101d5bc73dcf7f4a1c036c6981a273) |
| `-wip/global` | [c4a89f7da3](https://github.com/apellis/odd-lean/commit/c4a89f7da34799657b977fe3e21691e121c1ad10) |
| `-wip/global-r4-salvage` | [f4ca5962bf](https://github.com/apellis/odd-lean/commit/f4ca5962bffbc13adf89248f063d1942ff705cc6) |
| `-wip/graded-action-r20` | [2f3c80c7b3](https://github.com/apellis/odd-lean/commit/2f3c80c7b357f017ae5c07b09cb9f3dd80ad427c) |
| `-wip/halfturn-ideal` | [1d86f50296](https://github.com/apellis/odd-lean/commit/1d86f50296169d34d9f932ed1fb3a7c2d7b27824) |
| `-wip/hom-transport-r24` | [3096be8bb0](https://github.com/apellis/odd-lean/commit/3096be8bb0cdaae94d015747e515f0ccacd23235) |
| `-wip/iji-reservoir` | [2cbb3e6fd6](https://github.com/apellis/odd-lean/commit/2cbb3e6fd6ac0994a5c8c0a2ef23c706e6f0f864) |
| `-wip/ind-res-kernel` | [9ec29d10c2](https://github.com/apellis/odd-lean/commit/9ec29d10c230648e5c41eadf629cd1b54b9cf843) |
| `-wip/ind-res-kernel-grading` | [f4a86123ab](https://github.com/apellis/odd-lean/commit/f4a86123ab6bd63e3df767e97c131450e3327116) |
| `-wip/ind-res-kernel-naturality` | [c1ac5b8ed7](https://github.com/apellis/odd-lean/commit/c1ac5b8ed700a69d2971902ef330c7423592dff7) |
| `-wip/induction-parity-comparison` | [0f09488874](https://github.com/apellis/odd-lean/commit/0f09488874e5f97d3790e92dbce94b930fd77d27) |
| `-wip/induction-unit-naturality` | [496d71addc](https://github.com/apellis/odd-lean/commit/496d71addc079958f78155c542e20f08039d30f7) |
| `-wip/induction-unit-tensors` | [2224374d1f](https://github.com/apellis/odd-lean/commit/2224374d1facd76783c97a53eed3964cf13e4c6d) |
| `-wip/intertwiner-right-dot` | [f6927afd6b](https://github.com/apellis/odd-lean/commit/f6927afd6bddafe20bd220d08ee3ef70963958f4) |
| `-wip/inverse-square-normalization` | [728d468d9f](https://github.com/apellis/odd-lean/commit/728d468d9f1eae99894f70334d25a1e25706aebb) |
| `-wip/kernel-matrix-evaluation` | [e977703414](https://github.com/apellis/odd-lean/commit/e977703414c9c167451a5000f5fb1c3300f00f7c) |
| `-wip/kernel-matrix-inversion` | [7447b6f129](https://github.com/apellis/odd-lean/commit/7447b6f12930f69a149c740743b72b60e4c2b935) |
| `-wip/leftward-inverse` | [a32d2da14e](https://github.com/apellis/odd-lean/commit/a32d2da14e4759e9bdc2b7f7a5190fac4d9823ee) |
| `-wip/local-g-signs` | [daaf35e10c](https://github.com/apellis/odd-lean/commit/daaf35e10c070b719d96cc387f90a71862cfc5cf) |
| `-wip/mackey-boundary-r13` | [1f3453bb03](https://github.com/apellis/odd-lean/commit/1f3453bb03ae8a55c73a58bae02bfc8ad1a2265c) |
| `-wip/mate-kernel-endpoints` | [3969abc443](https://github.com/apellis/odd-lean/commit/3969abc443e30d96093d51852cf5edfca45741ec) |
| `-wip/mate-kernel-naturality` | [9e0438d217](https://github.com/apellis/odd-lean/commit/9e0438d217c0f6b20246c8c69ae98ebc9b5d37b6) |
| `-wip/matrix-comparison-r15` | [ffc9830e18](https://github.com/apellis/odd-lean/commit/ffc9830e1810cbefbefd5306de958f0105f825ff) |
| `-wip/mixed-braid-r18` | [a398dd95b2](https://github.com/apellis/odd-lean/commit/a398dd95b2c2c2d67e606bfa936dbaf24097487c) |
| `-wip/mixed-braid-typed-rewrite` | [db76f25287](https://github.com/apellis/odd-lean/commit/db76f252871681b5f3a1e34b0b129333685c3e10) |
| `-wip/mixed-coefficient-parity` | [33be34fa6d](https://github.com/apellis/odd-lean/commit/33be34fa6d87616773d89b405fff24980ca3073d) |
| `-wip/mixed-colour-braid-r38` | [ed4b47fce1](https://github.com/apellis/odd-lean/commit/ed4b47fce18e2f640db7649a2d5ff613ea72f09f) |
| `-wip/mixed-completion-r39` | [f96a54dbe5](https://github.com/apellis/odd-lean/commit/f96a54dbe58daf89905d2a0d712d65cc7a2feb5b) |
| `-wip/mixed-mate-r10` | [e74478eda3](https://github.com/apellis/odd-lean/commit/e74478eda3ff816a4bcd12fc4d58fcc5b4b1fdec) |
| `-wip/mixed-mate-r11` | [fab2bb84d6](https://github.com/apellis/odd-lean/commit/fab2bb84d64e937f22f5dbb46e448f3eb6949725) |
| `-wip/mixed-relations-r40` | [fb4bb92752](https://github.com/apellis/odd-lean/commit/fb4bb92752e22d956988ab418d8bfb8cc05221fb) |
| `-wip/module-matrix-inverse` | [afde522abb](https://github.com/apellis/odd-lean/commit/afde522abbf2f5296c685fa44d4b034a5604cc6a) |
| `-wip/negative-crossing` | [48b5818e2e](https://github.com/apellis/odd-lean/commit/48b5818e2e267e125b8677092532f871c1d8e937) |
| `-wip/norm-division` | [23bf2376d3](https://github.com/apellis/odd-lean/commit/23bf2376d345cb46e2c7dc503dfac63c5b0a4a17) |
| `-wip/odd-mixed-coefficient-identities` | [4dcbecd6a4](https://github.com/apellis/odd-lean/commit/4dcbecd6a416e137682d8f17d91e44ee4f964a2a) |
| `-wip/off-content-zero` | [f070115d40](https://github.com/apellis/odd-lean/commit/f070115d40c65bb3735e206d0b937cf21e4a1460) |
| `-wip/offdiagonal-actual-cap-pivots` | [48783d4c65](https://github.com/apellis/odd-lean/commit/48783d4c657fb2357d9a542f7b5d37f37ab98d1d) |
| `-wip/offdiagonal-boundary` | [b34e7af566](https://github.com/apellis/odd-lean/commit/b34e7af5664c160a7a751991e0b08957e311a9cd) |
| `-wip/offdiagonal-boundary-leading` | [df2487682d](https://github.com/apellis/odd-lean/commit/df2487682ddf1c9ffa542edaca7d025a4705ea67) |
| `-wip/offdiagonal-boundary-snake` | [f268a18627](https://github.com/apellis/odd-lean/commit/f268a1862704c1aa3feb83433da69379634cc6ef) |
| `-wip/offdiagonal-corrected-coordinates` | [66624cd7fc](https://github.com/apellis/odd-lean/commit/66624cd7fc2d0d7cb3e393acdc886419781c7f84) |
| `-wip/offdiagonal-long-transport` | [1bb0227472](https://github.com/apellis/odd-lean/commit/1bb022747280787e690c5d6a458bc4f106870c7d) |
| `-wip/offdiagonal-negative-crossing` | [af54a29c87](https://github.com/apellis/odd-lean/commit/af54a29c876812ecc51a3ff3de393cb58dc6a051) |
| `-wip/offdiagonal-positive-crossing` | [083aafb432](https://github.com/apellis/odd-lean/commit/083aafb432086dd4fffa5897e5ac307e984cc7ad) |
| `-wip/offdiagonal-rho-extraction` | [95ac22408e](https://github.com/apellis/odd-lean/commit/95ac22408e1791c2eee687ccc4898ba09dde0ece) |
| `-wip/offdiagonal-row-splitting` | [d7dab6280b](https://github.com/apellis/odd-lean/commit/d7dab6280b0a6c9aa5668c9e8626b499900c404d) |
| `-wip/old-append-superfunctor` | [be1900486c](https://github.com/apellis/odd-lean/commit/be1900486c34367d428e9197062ce24c310f6f3a) |
| `-wip/paired-j-r37` | [e9bdb0bb34](https://github.com/apellis/odd-lean/commit/e9bdb0bb346d356236e3bd81deb052100d8c88c8) |
| `-wip/pitchfork-r7` | [8c7858fe49](https://github.com/apellis/odd-lean/commit/8c7858fe49c933a796963376ca2141b948c6f242) |
| `-wip/pitchfork-r8` | [70dfd7c8ee](https://github.com/apellis/odd-lean/commit/70dfd7c8eea212299e689b28394e444cd0ece6ca) |
| `-wip/pitchfork-r9` | [9cead45182](https://github.com/apellis/odd-lean/commit/9cead4518207e7d859b237b72ae796b14e0ad461) |
| `-wip/prescribed-mixed-mate` | [4195f61652](https://github.com/apellis/odd-lean/commit/4195f616528e79c69ce8eb7670adf6d9f90dec91) |
| `-wip/principal-hom-r27` | [05432d95f4](https://github.com/apellis/odd-lean/commit/05432d95f46cdaada487813fb3e02a961ca96571) |
| `-wip/probe-append-tensors` | [c0fae06d8b](https://github.com/apellis/odd-lean/commit/c0fae06d8b36dd37306d2691a9160ad98d3b4661) |
| `-wip/probe-realization-r38` | [e24a4ec9bd](https://github.com/apellis/odd-lean/commit/e24a4ec9bd2a3a2a4a6378e31ab94f6cb6e5b63a) |
| `-wip/probe-sector-r31` | [6c7b838639](https://github.com/apellis/odd-lean/commit/6c7b838639175a113eed7bb3036d6afb984f9c18) |
| `-wip/probe-window-inverse-r35` | [d0b142c271](https://github.com/apellis/odd-lean/commit/d0b142c2718cda826ab6b32480b78202850917a2) |
| `-wip/raw-even-mixed-mate` | [183eff509f](https://github.com/apellis/odd-lean/commit/183eff509f33368faba816fb5432fae44606dbde) |
| `-wip/raw-mixed-coefficients` | [5caf1033e1](https://github.com/apellis/odd-lean/commit/5caf1033e11f31cf5b8c16ae7d8e5674461b7655) |
| `-wip/raw-odd-mixed-mate` | [a85d3f126d](https://github.com/apellis/odd-lean/commit/a85d3f126d822ac4101337fee1c814c305739ada) |
| `-wip/recovery-build-policy` | [7f71f044f5](https://github.com/apellis/odd-lean/commit/7f71f044f5d181b0ff09d976a46df84e40f831d6) |
| `-wip/recovery-cache-footprint` | [7738a9ed51](https://github.com/apellis/odd-lean/commit/7738a9ed51894a55567a8908517554ce36320b20) |
| `-wip/recovery-even-mate-linux` | [2d91f33ec3](https://github.com/apellis/odd-lean/commit/2d91f33ec39f83c3d3620d0289e8e9c5cd9e0132) |
| `-wip/recovery-module-matrix-linux` | [88dd731f29](https://github.com/apellis/odd-lean/commit/88dd731f29ab17042e455edce268ef0e56a849e9) |
| `-wip/recovery-probe-append-linux` | [7440ac59fc](https://github.com/apellis/odd-lean/commit/7440ac59fc65cd9b33b1ee036839e30b4838ca97) |
| `-wip/recovery-weighted-append-linux` | [198f6d1f89](https://github.com/apellis/odd-lean/commit/198f6d1f89da28073ce5dcc85ad79e331d08a086) |
| `-wip/reduction` | [d5f84d17ef](https://github.com/apellis/odd-lean/commit/d5f84d17ef7c3dce06839a4835dcb7c03af10669) |
| `-wip/reservoir-bound-r22` | [548c7a5f35](https://github.com/apellis/odd-lean/commit/548c7a5f359812c35bbabec0e31d77656cf57824) |
| `-wip/reservoir-grading` | [23ff64e81f](https://github.com/apellis/odd-lean/commit/23ff64e81fce899f66341715fc7fb1f9166b7f95) |
| `-wip/residual-r8` | [d6cb48206b](https://github.com/apellis/odd-lean/commit/d6cb48206b603af9ba232dba7ae95f6fc6fdd6bf) |
| `-wip/residual-windows-r34` | [e430ea08e5](https://github.com/apellis/odd-lean/commit/e430ea08e55d540a337ad4ad52dee911f2488756) |
| `-wip/reversed-reservoir-r26` | [cf66e26450](https://github.com/apellis/odd-lean/commit/cf66e264501f0ef19db5f5488726bceff93a9616) |
| `-wip/risk-reduction` | [ab1824df2b](https://github.com/apellis/odd-lean/commit/ab1824df2bea989963ca2601211f69bb6a1e9e3a) |
| `-wip/rouq-sig-contents` | [d883f3e106](https://github.com/apellis/odd-lean/commit/d883f3e106007cce4e9c976e41ff2b519f63eaa6) |
| `-wip/rouquier-map-r12` | [6e4146e43c](https://github.com/apellis/odd-lean/commit/6e4146e43c919efcedab2c1f7f0e202b94b3fc26) |
| `-wip/same-colour-braid-r36` | [97f177b46e](https://github.com/apellis/odd-lean/commit/97f177b46ef7554caffcf9030b243524ddf03031) |
| `-wip/same-colour-inversion-r36` | [eef5de4262](https://github.com/apellis/odd-lean/commit/eef5de4262f2e0df0fb838b4125ba054972e949a) |
| `-wip/shifted-cap-rows` | [87f6f2fe64](https://github.com/apellis/odd-lean/commit/87f6f2fe64f20dbc37ad743491e02b17100d684c) |
| `-wip/shifted-coefficient-comparison` | [575917b3e0](https://github.com/apellis/odd-lean/commit/575917b3e07d6436f3485f24e85f9002599eea6d) |
| `-wip/shifted-coefficient-module` | [40f6023fc1](https://github.com/apellis/odd-lean/commit/40f6023fc1c90d0a69dd23823201679b593fb83d) |
| `-wip/shifted-swapping-r29` | [48d33f745f](https://github.com/apellis/odd-lean/commit/48d33f745ff436d0c0868b06240f347e1217ee1e) |
| `-wip/sigma-mixed-entry` | [471497f7b7](https://github.com/apellis/odd-lean/commit/471497f7b76a81fe4ca0eb3e210d547a122820ca) |
| `-wip/sigma-rr` | [bf7c19063a](https://github.com/apellis/odd-lean/commit/bf7c19063a90683bdff4cb0347a529c76d4d4866) |
| `-wip/signed-f-r17` | [389ac07bd4](https://github.com/apellis/odd-lean/commit/389ac07bd4e26221293bd99714244a31e29def3c) |
| `-wip/signed-last-boundary-separation` | [88535f8b2c](https://github.com/apellis/odd-lean/commit/88535f8b2c88190d155606d9abf621969b92b483) |
| `-wip/square-resolution-r11` | [f03a06b943](https://github.com/apellis/odd-lean/commit/f03a06b943cd5de0a95ef8b699832f0b52c93fe3) |
| `-wip/streamG-r6-multicolour` | [7870f9f386](https://github.com/apellis/odd-lean/commit/7870f9f386515158b1a33a1333709727a4fe5587) |
| `-wip/super-sector-r34` | [699bdbd8ed](https://github.com/apellis/odd-lean/commit/699bdbd8ede7e62ab873a31d75b0e8d8f35d8138) |
| `-wip/swapped-action` | [e368751ab4](https://github.com/apellis/odd-lean/commit/e368751ab47d66dcb3fe23d7d29757f43adb5ea4) |
| `-wip/swapped-action-assembly-r44` | [29ecf648cc](https://github.com/apellis/odd-lean/commit/29ecf648cc946aa7f76a088eaba166f6158f2cd2) |
| `-wip/swapped-action-complete-r47` | [f907d24e3d](https://github.com/apellis/odd-lean/commit/f907d24e3d393604dcd39dc406f5be75ebf1f7b2) |
| `-wip/swapped-bubbles-nonpositive-r44` | [b12c885016](https://github.com/apellis/odd-lean/commit/b12c885016d753e33aac6a55f019790118a59afc) |
| `-wip/swapped-cross` | [24bf144f1e](https://github.com/apellis/odd-lean/commit/24bf144f1e2a6c2bffcd5d368efa4c918057a730) |
| `-wip/swapped-distinct-mixed-r45` | [45c696059c](https://github.com/apellis/odd-lean/commit/45c696059cbd08ee25f1d5350e95c206ba2b1d67) |
| `-wip/swapped-distinct-pre-r45` | [24a64a501c](https://github.com/apellis/odd-lean/commit/24a64a501c258e3d776f538e649967341c85db84) |
| `-wip/swapped-generators-supernatural` | [d5a7f1eff5](https://github.com/apellis/odd-lean/commit/d5a7f1eff5a6e8832a9acd521ac03a2730555c38) |
| `-wip/swapped-hom-inversion-r42` | [6f348ac314](https://github.com/apellis/odd-lean/commit/6f348ac31483097b677fef1a47d49715464c356e) |
| `-wip/swapped-inversion` | [1297b89b12](https://github.com/apellis/odd-lean/commit/1297b89b12ee33ecadb3e3151f70d58b4e54ad38) |
| `-wip/swapped-quad` | [e3930b889c](https://github.com/apellis/odd-lean/commit/e3930b889c28dbc821cd5eff0048b351623f23d7) |
| `-wip/swapped-slide-ne` | [0080234fcf](https://github.com/apellis/odd-lean/commit/0080234fcf61efe701a0a9f20a93b928bb97ff0f) |
| `-wip/swapped-vacuum-bubbles-r43` | [ad115fe349](https://github.com/apellis/odd-lean/commit/ad115fe349651e6e4c7e4e56238b2eeb130b457b) |
| `-wip/swapping-invertible` | [3a33cb8132](https://github.com/apellis/odd-lean/commit/3a33cb81328a8c7104c680ae057d63422084fc0b) |
| `-wip/sym-coefficient-separation` | [2e817ff9c3](https://github.com/apellis/odd-lean/commit/2e817ff9c3f7cb04d10b4f86fa4772085031610c) |
| `-wip/vacuum-comparison-r40` | [0ff8a97949](https://github.com/apellis/odd-lean/commit/0ff8a979490399ff6104caf5fbcf52a69914a0c1) |
| `-wip/vacuum-coordinates-r42` | [42b2179893](https://github.com/apellis/odd-lean/commit/42b21798936dfd3ea1bd0ecd5752a1c41cbe91b3) |
| `-wip/vacuum-recovery` | [b6dd210527](https://github.com/apellis/odd-lean/commit/b6dd210527615921f5d0ff985f8cff0812547afc) |
| `-wip/vacuum-transport-r41` | [92669e8f1b](https://github.com/apellis/odd-lean/commit/92669e8f1baff31eb45bab135ce4af835d88e87b) |
| `-wip/weighted-append-induction` | [4bd7ed2762](https://github.com/apellis/odd-lean/commit/4bd7ed2762d7b4c9d2e05f3fe06bbadaebe3c31c) |
| `-wip/weighted-append-parity` | [e3dc8f44f3](https://github.com/apellis/odd-lean/commit/e3dc8f44f3322743d765248efe310f86568b4f89) |
| `-wip/weighted-append-units` | [4a54cfe833](https://github.com/apellis/odd-lean/commit/4a54cfe833b27bea1efb04ec26269712f810227e) |
| `-wip/whisker` | [986f266ca1](https://github.com/apellis/odd-lean/commit/986f266ca12b4f5952b3315a05d747b3f2cecdfe) |
| `-wip/whole-corrected-content-braid` | [854456133f](https://github.com/apellis/odd-lean/commit/854456133fcb51a79b25f6c02d2579a99f647cec) |
| `-wip/written-proof-r52` | [74642e640b](https://github.com/apellis/odd-lean/commit/74642e640ba66747b7ecbc512c34e6e782e75048) |

## Additional unfinished conversion variants

These local variants are also retained in reachable history. They are unverified
and do not supersede the four main restart points in HANDOFF.

| Attempt | Preserved commit | Source |
| --- | --- | --- |
| matrix row conversion | [4dc49448a6](https://github.com/apellis/odd-lean/commit/4dc49448a663188557d7af04ed76a36c9f58e8c5) | `OddMath/QuiverHecke/CyclotomicAction/ELVKernelMatrixCoordinates.lean` |
| weighted append conversion | [bc47db64e0](https://github.com/apellis/odd-lean/commit/bc47db64e065ba3019e398ae2ed4fa7c5abcad01) | `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedAppendUnits.lean` |

## Earlier branches without the research prefix

These older nondegeneracy topic heads were already ancestors of the primary
research branch and have also been retired. Branch inventories must check topic
and ancestry, rather than relying only on a branch-name prefix.

| Retired topic | Preserved commit |
| --- | --- |
| `mixed-mate-r12` | [5eb39999ad](https://github.com/apellis/odd-lean/commit/5eb39999ade91cdf9ba6d2c3459c9ad2b4cd2c25) |
| `nonvacuum-block-inversion` | [192af291c9](https://github.com/apellis/odd-lean/commit/192af291c917faf9de11d821b637c616eba8cc4b) |

## Proposed comparison source trees

These trees retain proposed arguments outside the checked library. Their
research-parent copies preserve the exact source without making any open
proof integration head a history ancestor. Scope at each snapshot is in
HANDOFF; later checked successors do not turn these variants into evidence.

| Proposed argument | Preserved tree commit |
| --- | --- |
| Arbitrary-module distinct mate identity | [a9c1dbe593](https://github.com/apellis/odd-lean/commit/a9c1dbe5935a884e944e6865bb759099933eb32c) |
| Chosen content E/F charts | [d4b6bf2096](https://github.com/apellis/odd-lean/commit/d4b6bf20961c7fb3e0b99764013c15baa4c53078) |
| Selected scalar double append | [79f6c9ea86](https://github.com/apellis/odd-lean/commit/79f6c9ea86addb31fb53f3df83197e7d4e37c2b2) |
| Selected weighted mate transport | [829dabe55c](https://github.com/apellis/odd-lean/commit/829dabe55cf56cb35c459286f9fb7fd8aa7750ca) |
| Old power-quotient vacuum | [e5b7b48a7d](https://github.com/apellis/odd-lean/commit/e5b7b48a7dce67e32b5cf4e5bac777282e7f3052) |
| Reversed quotient bounded detection | [890307122c](https://github.com/apellis/odd-lean/commit/890307122c1de62321e20eea5fc14b9edccdc645) |

## Mate and coordinate proposal source trees

These copies preserve the exact source trees with a research-only parent.
Pending proof integrations are not made ancestors of the research branch,
and no proposed source enters the checked library through this preservation.
The source notes describe the unfinished mathematical arguments.

| Proposed argument | Preserved tree commit | Original proposal commit |
| --- | --- | --- |
| Content pair crossing | [cef0b17b98](https://github.com/apellis/odd-lean/commit/cef0b17b98856f32f937b5510d70ab1c2feb546f) | `3fbe4db1fc5d7013113f2e3ca66c21caf006b9db` |
| Content self-colour mate | [fc52dfd086](https://github.com/apellis/odd-lean/commit/fc52dfd086f11fab7b527cd9a3fbce808c689ff5) | `73ccc7c454d6ef0e902c88efa4838aac1a46cc53` |
| Distinct content mate | [cffb3ae4b2](https://github.com/apellis/odd-lean/commit/cffb3ae4b2f5c9471d5e6ef53d44222f6d0f4cc0) | `ced7fe6b8234b1ee29e9417d1dbb5957594cc807` |
| Power-word coordinates | [41466e07a4](https://github.com/apellis/odd-lean/commit/41466e07a45207605231911c5f1d3f01a24021f9) | `91141513c94545c32b5fb9bcb9db4f001bc29d54` |
| Weighted matrix rows | [dca80e84a0](https://github.com/apellis/odd-lean/commit/dca80e84a05f8f0777c55dced0fd3ac6fff8bdcb) | `4dc8f9fca8eb58057f5a750aeede6b909a39246f` |

## Module-map and coordinate proposal source trees

These full source-tree copies have only the verified research parent. They
retain proposed variants without importing them or making a pending proof
integration an ancestor of a history-only merge. Scope is recorded in
HANDOFF and the source notes; later checked successors are independent.

| Proposed argument | Preserved tree commit | Original proposal commit |
| --- | --- | --- |
| Native weight crossing comparison | [78f211e13b](https://github.com/apellis/odd-lean/commit/78f211e13b210b93f7ed4c67867eac0919792e40) | `75b20b0b5014793d7c2239042ddfd9f5e36cca45` |
| Chosen power-word append and dot | [16a56e818f](https://github.com/apellis/odd-lean/commit/16a56e818f35b7cd39b0b03ae28f8dbbf8dd2ecb) | `807a911d31a89640c40fcaaf6f4a6fc64742b7b5` |
| Shifted scalar cap coordinates | [cc3d58e58a](https://github.com/apellis/odd-lean/commit/cc3d58e58afba1238660cc7672c0b10b53fd13aa) | `cedc97cc9b6341d007440f6451ea613309e541b1` |
| Native distinct-mate bundling | [a6819398d1](https://github.com/apellis/odd-lean/commit/a6819398d133a24265de16ed08f44a7224efddab) | `2555aa7c5ea38786ae67e68c380098442938f65a` |

## Factor-chart and signed-window proposal source trees

These full source-tree copies have only the verified research parent. They
retain proposed variants without importing them or making a pending proof
integration an ancestor of a history-only merge. Scope is recorded in
HANDOFF and the source notes; later checked successors are independent.

| Proposed argument | Preserved tree commit | Original proposal commit |
| --- | --- | --- |
| Deferred native content-mate comparison | [f7d588fdb6](https://github.com/apellis/odd-lean/commit/f7d588fdb66975879ff4568586b1dc3288f84d84) | `dafc0aec8479b89f8b090f46174b480b9abf680c` |
| Content dotted matrix rows | [a10a9f260d](https://github.com/apellis/odd-lean/commit/a10a9f260d0b7209a50139a3cac37ddfeaeaeeef) | `0a185108b962966ded70137e0a976b86a9806520` |
| Selected power-word pair crossing | [28e56575d8](https://github.com/apellis/odd-lean/commit/28e56575d8ae9778bd7e120b2a9b80ccadbc8625) | `947ed579e6e40e7641b0a9ab20f1f1dd6d01d758` |
| Canonical truncated-content block charts | [8e85113f3f](https://github.com/apellis/odd-lean/commit/8e85113f3f63edb2cea03919ca151fbc97cd4533) | `05fce4219e872534c7174475bcd5c783c6d17c85` |
| Weighted finite matrix inverse | [b541461adf](https://github.com/apellis/odd-lean/commit/b541461adf01e76a6de90384cd9879bdbc649955) | `51b5cf9c7df26f12d5336f05d84975c6f86c3a6d` |
| Occupied vacuum probe unit | [9aaeb5c826](https://github.com/apellis/odd-lean/commit/9aaeb5c826ebdff04b0eea92bbcf06f405434fec) | `e291c89bbbae8d50322b5d0a99b9cdc33d5a360b` |
| Selected word-pair whole-coherence variant | [d1540e8957](https://github.com/apellis/odd-lean/commit/d1540e89579b73ef34f02b5bc5a3b520291e272e) | `95e6c84c2a87a35b58663e8ae69d9847c3950312` |

## Content, crossing and finite-matrix source variants

The following exact source trees are retained without importing their
proposed declarations. New copies have only the verified research parent;
pending proof integrations are not ancestors of this history-only merge.
Earlier checked variants may have curated successors, whose current
boundaries are recorded in STATUS.

| Argument | Preserved tree commit | Source revision | Scope |
| --- | --- | --- | --- |
| Earlier coefficient-power vacuum | [bf0666174e](https://github.com/apellis/odd-lean/commit/bf0666174e082685d7f550b1c1ef3c5e276098f6) | `16af4f57532bf5428fb6fe119d8462aa34bbc43d` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier content distinct mate | [e6e83e6b2a](https://github.com/apellis/odd-lean/commit/e6e83e6b2ac62ed819b8f75e97d63a6e76ff631b) | `d8b8eaf6eb6cefb6e35b58b4c201fea128af0bc9` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier homogeneous content inverse | [97744bc30f](https://github.com/apellis/odd-lean/commit/97744bc30f7d4f52573f8db0cbf438c331e0b111) | `a635ac09e444464a3da406ed653a342f63ee2a29` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier rectangular module inverse | [3ce5c73a70](https://github.com/apellis/odd-lean/commit/3ce5c73a70c20d425fa97c94df479ec6cc3c6800) | `97dccb1f5074ee876b8a926180aa9ee7aa840e61` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier full-coefficient reversal | [3c4f5dc432](https://github.com/apellis/odd-lean/commit/3c4f5dc4323517392550ce30afec954c71da3e2a) | `2d425b9901907548cbad4361284be2000bc7ae78` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier induction grid comparison | [7611447f10](https://github.com/apellis/odd-lean/commit/7611447f10a215651a95109f422a71c89c10120f) | `98530d7938d92cda0d7e3cc31f802a5f1fd2cb1a` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier scalar ordinary mate | [2b66f27afe](https://github.com/apellis/odd-lean/commit/2b66f27afe28fad57a8959fa78a27d51cfd0981d) | `450ef8861184d889f9673fb56641a4935057a33d` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier scalar finite comparisons | [cbf61d60ae](https://github.com/apellis/odd-lean/commit/cbf61d60aefbc2209f398a0f3582f09461e532c1) | `863e24ac0637d40afb6388ef6594c0df5e19b8e0` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier truncated distinct decoder | [e7e6b85049](https://github.com/apellis/odd-lean/commit/e7e6b8504930beb2f78267c5a7f07be0c7a4a078) | `6c742cc80acef903ac0ca8d723bd48c7e1a766df` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier weight crossing components | [fa5405dcd9](https://github.com/apellis/odd-lean/commit/fa5405dcd9f3dbf5aded2a25d56a9cf48ecccfdc) | `b91425d61699cc1e59b0580520ea2f1d601d3101` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier weighted matrix chart comparison | [17ab46afaa](https://github.com/apellis/odd-lean/commit/17ab46afaab3809037140d99c2789fff55ab5dbf) | `c7a624c2d7061d2c72f08577c2efcec0a25cd4c2` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier weighted iterated induction | [ba7caeae43](https://github.com/apellis/odd-lean/commit/ba7caeae43546aa4ca3e142bd266ec236b2f2674) | `3aa737ace9a9322e50063b5ef2c78a86402e2503` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier power-word coordinates | [332f048f09](https://github.com/apellis/odd-lean/commit/332f048f0949221c74a3cd6fca500bad10865e35) | `9f59f2a9893b9d3e9627abf74f40378cdd624be1` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier source power kernel | [7ab1a95c01](https://github.com/apellis/odd-lean/commit/7ab1a95c01cccc904c1025633c8f4ccdbd4658b7) | `b736e758d8abbd878830e2edab52995ebc5de0d3` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Earlier source quotient kernel | [645e6335a6](https://github.com/apellis/odd-lean/commit/645e6335a699c7bdac51b9c8d4480a56d5363d37) | `96fa541c856f740b057799950de67fda1458a5ac` | Earlier source variant retained in history; current checked successor scope is in STATUS. |
| Selected power-word pair crossing | [8db0c869d7](https://github.com/apellis/odd-lean/commit/8db0c869d791b3587bab1c81bf9e8729cc68fbfa) | `00f357cc352a3619107ec34273b96b73cd10130a` | Closed pair and all-vector recast prefixes pass; the combined signed expression and complete consumer remain unverified. |
| Canonical truncated-content mate | [5d38b48380](https://github.com/apellis/odd-lean/commit/5d38b4838006662a575d4e798ed7c04207842357) | `d405729ef6a83ee4c56688eb8f1c3565c96a9490` | Generic source comparison passes; canonical source tensor, whole mate square and inverse remain proposed. |
| Weighted finite matrix entry comparison | [d22d9954dd](https://github.com/apellis/odd-lean/commit/d22d9954dda046fce9ecd4c6ce062a4c349e2784) | `beffca26a752b1d4fa52c8fea83879b54e71b671` | Supporting component checks pass; entry producer passes but its paired consumer and whole finite forward identification remain pending. |
| Scalar finite inverse candidates | [56c2b1f6cb](https://github.com/apellis/odd-lean/commit/56c2b1f6cbc77ce21e7919343dbfefbe908fdf10) | `5ca63614d9fa1bdef18c52724da96992ecacce6b` | Concrete global-to-relative-to-scalar inverse candidates are proposed; the first strict producer check fails and complete prescribed forward identification remains open. |

## Evaluation and original-weight mate source variants

These exact source-tree copies have only the verified research parent.
No pending proof head becomes an ancestor through this preservation, and
no unchecked declaration is imported. Scope describes each snapshot;
later checked successors are recorded separately in STATUS.

| Argument | Preserved tree commit | Source revision | Scope |
| --- | --- | --- | --- |
| Power-word signed composition | [d56d73f921](https://github.com/apellis/odd-lean/commit/d56d73f9213308b43e6f36d3663b8024b853f564) | `b107e5ac7cae3f029ce2c9e7ab97d741d2c2f937` | Whole homogeneous composition and scalar-linearity prefixes pass; complete consumer and chosen weight-action evaluation remain unverified. |
| Original-weight distinct mate | [0acc801e1f](https://github.com/apellis/odd-lean/commit/0acc801e1f1dff93fd23cf81f238715556b35ec4) | `7214cf875695c6a25d4dc6ecb7852ac15011def6` | Four-corner PiSCat component prefix passes; degree recheck, concrete consumer and prescribed original-weight inverse remain proposed. |
| Scalar unit-only finite comparison | [e5cd113828](https://github.com/apellis/odd-lean/commit/e5cd1138288ee5dcbf32214d748be23c405c9b7c) | `8c8c4e196a40b3ebe87af38e20fe6b59de3af01b` | This snapshot retains the then-unverified generic comparison and planned consumer; later checked successors are separate. |
| Probe row in native content coordinates | [49859b449f](https://github.com/apellis/odd-lean/commit/49859b449f1dc56b64cbdfaf73dc10334b081bea) | `33144e55ebd0328d04b79e1eabfd4872f5f979c6` | Whole source and consumer remain unverified at the raw-coend versus SVec-carrier specialization; the checked full-old extraction row is separate. |
| Shifted old-content matrix entries | [de01095797](https://github.com/apellis/odd-lean/commit/de0109579791da62ac09119a762f3e7362b95fba) | `fdc3d20c6508433249c10ebee71b31d8b9a5a369` | Generic decoration prefixes pass; shifted-coordinate to prescribed old-field attachment and complete consumer remain unverified. |
| Earlier checked selected pair development | [010a21c22b](https://github.com/apellis/odd-lean/commit/010a21c22bf3be67dd99f518ae644166e5b81c69) | `a86b5333b329d58a01b0033ce4911dab8cf33e12` | Earlier scoped-checked development variant; current curated successor and integration status are in STATUS. |
| Earlier checked canonical content inverse development | [a0c1689484](https://github.com/apellis/odd-lean/commit/a0c16894844fdd988ff46f16facef7df1001369d) | `bf7377a5a41c310fb90ff6e33dd525f96228af72` | Earlier scoped-checked development variant; current curated successor and integration status are in STATUS. |

## Matrix and normalized-cap development trees

Exact tree copies below have only the verified research parent. Pending
proof heads are not ancestors through these copies; unchecked source is
not imported. Later checked successors are recorded separately in STATUS.

| Argument | Preserved tree | Source revision | Scope |
| --- | --- | --- | --- |
| Original-weight chosen dot | [0b26b3c1f7](https://github.com/apellis/odd-lean/commit/0b26b3c1f7c8e1a548d46d0b0293afefde62fba8) | `28701717d3c406de7f5a4e606159def247c13178` | Producer passes; paired consumer and whole batch unverified. |
| Canonical content unit and cap fields | [5754cbac96](https://github.com/apellis/odd-lean/commit/5754cbac968d56ba037a4d3dc751bd1006fb65a2) | `525951c74a0fe5f0f069cf3caf59fd466693364c` | Unit and dot prefixes pass; all-power chain and actual field specialization unverified. |
| Native inverse coefficient caps | [ef8d91c005](https://github.com/apellis/odd-lean/commit/ef8d91c0058d8e88bb21995495267590318813d0) | `2d72ee9feb84c8f0255c10246bf82ec25a75ef49` | Bare producers pass; degree, paired consumers and scalar inverse-row binding unverified. |
| Scalar left-cap field binding | [93af40181a](https://github.com/apellis/odd-lean/commit/93af40181a8b1d62ff882d73e62054fa763bfae1) | `01ab162822ad9f1a57367555f5f228076e016448` | Literal dropped-row prefix passes; extended producer and paired consumer unverified. |
| Earlier content-dot parity helper proposal | [f8d712acf2](https://github.com/apellis/odd-lean/commit/f8d712acf2518deb563994c20cc88389ca618378) | `fbd6dbacb8b267439e983341dca90e762658f0c4` | Optional parity helper specialization unverified; checked content-dot core has a separate successor. |
| Selected content matrix development variant | [3ec1d857d1](https://github.com/apellis/odd-lean/commit/3ec1d857d135b00e02b845e5d0a25fa16cba43f7) | `3ab96677a9448899ce41f40733c38b12a26d1af3` | Checked development source variant; curated exports and verification are recorded separately in STATUS. |
| Weighted matrix functor development variant | [d65e564306](https://github.com/apellis/odd-lean/commit/d65e5643062be28b030e7cad936972385a924691) | `be4c81b89e134e77533d5d26746fea249a3902a8` | Checked development source variant; curated prescribed natural inverse is recorded separately in STATUS. |
| Weighted entry development variant | [302974da91](https://github.com/apellis/odd-lean/commit/302974da91721ba18b3bf27ce9acc774c7af688c) | `cfac1ac134170e2e00abaed7255739323240b25f` | Checked development source variant; curated component inverse is recorded separately in STATUS. |
| Scalar matrix development variant | [5ab584e0df](https://github.com/apellis/odd-lean/commit/5ab584e0df5bbe2ec6a85183418e2b5d98c80359) | `419c86c3a3bf55780cd44d9e3cc200a3b6f45b03` | Checked development source variant; curated forward-field and naturality successors are recorded separately in STATUS. |

## Signed-slide and normalized-cap source trees

Each exact tree copy has only the verified research parent. No pending proof
head becomes an ancestor through these copies; no unchecked source is imported.
Scope describes each snapshot, with checked successors recorded separately.

| Argument | Preserved tree | Source revision | Scope |
| --- | --- | --- | --- |
| Selected append unit-tail proposal | [b802409276](https://github.com/apellis/odd-lean/commit/b80240927601915814f7637597b9a5b795406259) | `49dd3234796d974e644cb858880e834d7790111e` | Weighted prefix passes; selected-content attachment and consumer unverified. |
| Canonical all-power cap proposal | [05654b5a11](https://github.com/apellis/odd-lean/commit/05654b5a11cd1106309a8fb8a458532241f35ab7) | `d432fab19b614f9f85f5e83ade24ed067136d1c9` | Generic producers pass; selected specialization and consumer unverified. |
| Native probe window proposal | [f4f667f576](https://github.com/apellis/odd-lean/commit/f4f667f57612d501bd72243fca0771ca7790f791) | `d65937ba256e7425f902ec3262b1c00268f8120e` | First native extraction producer passes; regular-ground extension and consumer unverified at this snapshot. |
| Signed weight-slide proposal | [ac485c8d27](https://github.com/apellis/odd-lean/commit/ac485c8d279988a7632aed15b26517cc44bec20c) | `9d31b051d0b61c3a766ae7f3099ab65fba7d3d5d` | Both supported producers pass; all-output/native fields and concrete consumer unfinished. |
| Weight braid components proposal | [55c80b932b](https://github.com/apellis/odd-lean/commit/55c80b932b526b3beecca9c0a2456e084a559719) | `5a0cc5e014e4248a617a7fdd85ff4259c6879be4` | Literal crossing-whisker formulas and consumer unverified; no braid claimed. |
| Earlier chosen-word development | [63ecc686ac](https://github.com/apellis/odd-lean/commit/63ecc686ac602e23c9dcbd5614289f3808a43510) | `9dbf0c1a1d0ec62c6fbbbe4e00e560d351b08bb5` | Checked topical variant; curated weight-dot successor verified in #991. |
| Earlier original-weight mate development | [85e53ce546](https://github.com/apellis/odd-lean/commit/85e53ce54667d8b46911ef798a86f1a368204d71) | `1917e6a166ae7697f6e1a3b8d0ed8502a4e9f4ec` | Checked topical variant; curated distinct inverse verified in #991. |
| Released coefficient-cap copies | [3b976c809f](https://github.com/apellis/odd-lean/commit/3b976c809f4d28faaefb67799c6ff931e797b313) | `528a11bf58e5b67df0789741f829c71baa295f3a` | Six owned file copies equal the curated #991 blobs; earlier full development tree retained as history only. |
| Scalar coefficient-window development | [a44d75451f](https://github.com/apellis/odd-lean/commit/a44d75451fd57fc44731958ab31f054b314a6451) | `08bd7aad89b0051bf5f114e80a8a0e1a8a07692e` | Checked topical producer and consumer; later integration gate is separate. |

## Action-field restart trees

Each exact tree copy has only the verified research parent; no pending proof
head becomes an ancestor through these copies. Checked successors are separate.

| Argument | Preserved tree | Source revision | Scope |
| --- | --- | --- | --- |
| Chosen word crossing | [87e8e0aa6c](https://github.com/apellis/odd-lean/commit/87e8e0aa6c064f45021b512286a1b8de2611c10d) | `6329a2e2c3a0600e6d93d0ae4ec30e884dcd3d42` | Producer prefixes pass; chosen old-word equality and complete paired batch remain unverified. |
| Canonical finite matrix charts | [11b07774d0](https://github.com/apellis/odd-lean/commit/11b07774d06cfdd523495aa08395b65f032670fc) | `6a4a7a600fa6cdaff2e12108ac7859bff71554c3` | Generic evenness passes; native parity attachments and consumer unverified. |
| Original-weight unit columns | [fe78dc3a8e](https://github.com/apellis/odd-lean/commit/fe78dc3a8eef7e652228630ea5fa616604363490) | `6b9c8dae0b4a8fe923d538bc76dbfe29a38ddc88` | Actual unit/power source and consumer unverified at this snapshot; later checked successor separate. |
| Raw shifted pre-Hom dot | [953872bb34](https://github.com/apellis/odd-lean/commit/953872bb34216c23da661c5aad2cd10bbe3e27d6) | `9a25adac792b4442153eb3f07bc095e066ae9314` | Raw Koszul-sign producer passes; paired consumer unverified at snapshot. |
| Content induction braid | [11da074226](https://github.com/apellis/odd-lean/commit/11da074226aa4927c606ee647eb128dd574cd70f) | `05f2db5ada7a79d727384cbf801c8b341ec89f2f` | Direct content braid source and consumer unverified at snapshot. |
| Distinct weight slides | [e9bb2e7a72](https://github.com/apellis/odd-lean/commit/e9bb2e7a721b2644eb56b1fa4f5bef3509f33e82) | `1bd55960d578a026ee512cf192a0f172609236ae` | Selected chart/dot squares pass; supported equations, native fields and consumer unfinished. |
| Literal power/weighted cap | [d0ac06491a](https://github.com/apellis/odd-lean/commit/d0ac06491a549e0cd1b77ba9ce3e9fe50faa6d1e) | `692e1c2740434211a9796723a2ba4d1ca450ebdf` | Checked topical source and occupied consumer; full integration gate and final chosen weight-cap attachment separate. |

## Local-inverse and crossing restart trees

Each exact tree copy has only the verified research parent; no pending proof
head becomes an ancestor through these copies. Checked successors are separate.

| Argument | Preserved tree | Source revision | Scope |
| --- | --- | --- | --- |
| Chosen whole-word crossing | [86120217f2](https://github.com/apellis/odd-lean/commit/86120217f2902f47356964da7c639850ca1ba0d7) | `c08b71a0847041a66c81b82c32b7615b9f8feb61` | Native unit-image join fails default kernel normalization; complete paired crossing remains unverified. Normalized crossing successors are separately checked. |
| Canonical principal content square | [14bca9c8ee](https://github.com/apellis/odd-lean/commit/14bca9c8ee9d816b7c5e70761f963a649e732954) | `f919a42df347e22871c4635a2335bebef1d298c9` | Proposed raw-to-native principal evaluation join and consumer remain unverified; cap extraction is separate. |
| Canonical absent-colour inverse | [229e677ff5](https://github.com/apellis/odd-lean/commit/229e677ff5f0a45e89c40419d8a8d66925934b1e) | `a9bdf1edd062248b20a97dd810db38022d5a1985` | Unit-column and absent-colour inverse producers and consumers pass strict checks; full integration and natural-family assembly remain separate. |
| Probe coefficient-row uniqueness | [f515dd83a7](https://github.com/apellis/odd-lean/commit/f515dd83a7e1300be3a70e0d929b8470d064bfab) | `402fbf170ede80959966c9c8a6732e2e28e566bf` | Checked scalar-evaluation uniqueness includes the occupied F(E T0) module; concrete old probe local adjunction still to construct. |
| Triple positioned dots | [ca89ee7221](https://github.com/apellis/odd-lean/commit/ca89ee7221c69c588b74abea9bff97645784fa89) | `5b31f0e6c6685d47dbb995fc856449687e0062b8` | All three literal positioned-dot components and paired consumer pass strict checks; C3 dot squares and corrected native polynomial remain open. |
| Weighted polynomial cap | [aa78b6d857](https://github.com/apellis/odd-lean/commit/aa78b6d857b6eae810495e5db0cd9944e230fa9f) | `c7c0e568ca8ac62e861c97f3ba95dbb7e7787bf6` | Actual polynomial module-cap core passes producer checking; full closure and occupied consumer remain unverified at this snapshot. |

## Released coefficient and braid source variants

These exact tree copies have only the verified research parent. The checked
library is unchanged; proposed auxiliary probes remain outside its imports.

| Argument | Preserved tree | Source revision | Scope |
| --- | --- | --- | --- |
| Cap family development | [6c1684f1e0](https://github.com/apellis/odd-lean/commit/6c1684f1e059542a666cfa36bc72d5dd5d89947e) | `f4aecd998474841e4331bc900ac07121aacbe9db` | Checked topical variant; curated theorem and integration boundaries are recorded in STATUS. |
| Native cap window development | [57cba88697](https://github.com/apellis/odd-lean/commit/57cba886977a4a69adb81cb6a1d5fc9802d12df5) | `817e6cfcf711677a34ea6fdc61853e2fd2888ea0` | Checked topical variant; curated theorem and integration boundaries are recorded in STATUS. |
| Power and weighted row development | [eb64fe11f0](https://github.com/apellis/odd-lean/commit/eb64fe11f0cfea0324f9411d9eb1a493114d1a29) | `692e1c2740434211a9796723a2ba4d1ca450ebdf` | Checked topical variant; curated theorem and integration boundaries are recorded in STATUS. |
| Weighted coefficient development | [95be31df42](https://github.com/apellis/odd-lean/commit/95be31df426052d5dacd79d3e63e2b3b0f295c9f) | `0999a8bae0fbd06f4b6ef947da34d1ede80a6d82` | Checked topical variant; curated theorem and integration boundaries are recorded in STATUS. |
| Weighted moment development | [f1f3b8adbf](https://github.com/apellis/odd-lean/commit/f1f3b8adbf3e919cbf5dd2346dab35793ce41607) | `a8b6da1030f663553abc173c7797d6715627c119` | Checked topical variant; curated theorem and integration boundaries are recorded in STATUS. |
| Same-colour braid development | [bfa0314597](https://github.com/apellis/odd-lean/commit/bfa03145976776c0b6751829e6cc28c47853d009) | `6735805da35ab8539077fbec34f5c64e9ed8b076` | Checked topical variant; curated theorem and integration boundaries are recorded in STATUS. |
| Same-colour braid auxiliary probes | [886d83c0c6](https://github.com/apellis/odd-lean/commit/886d83c0c69528964406ebac5e8ac766d48da22a) | `6735805da35ab8539077fbec34f5c64e9ed8b076` | Complete source tree including three auxiliary Lean probes; probe verification is not claimed. |

## Principal and local-factor restart trees

Each exact tree copy has only the verified research parent. Proposed source
is outside the checked library; scoped checks and full integration are separate.

| Argument | Preserved tree | Source revision | Scope |
| --- | --- | --- | --- |
| Whole-word crossing unit calculation | [9a4f3b9ef2](https://github.com/apellis/odd-lean/commit/9a4f3b9ef2460f115d7a4d4efb8df512190149ec) | `05916a404a42982623a91af41d6c770a5c184a73` | Exact unit-image producer passes default kernel checking; complete paired whole-map claim is separate. |
| Whole-word crossing comparison | [2378de18b1](https://github.com/apellis/odd-lean/commit/2378de18b1da4296f7fce05330c7e446ed0bac3b) | `4e143b04f02c4b0bf56d59ab5f46a887e88911e0` | Proposed whole-map cyclicity attachment; complete source and paired consumer remain unverified at this snapshot. |
| Canonical principal mate square | [63b67f26f9](https://github.com/apellis/odd-lean/commit/63b67f26f94c9b0aad5a6295f0529f6a3e26cf16) | `e1a4bb37d98120b28fe60f9c6f031130a4793b39` | Literal crossing retyping and first target join pass; raw-mate value join and paired consumer remain unverified. |
| Mixed triple correction polynomial | [f1c9d8b643](https://github.com/apellis/odd-lean/commit/f1c9d8b64319eb6c5ce955314c60b173d03f15d1) | `8318b76ad067e06420a2f98dbc6cb36735a12c62` | Indexed dot-coordinate pair passes; original-Sc polynomial producer passes, its consumer and native corrected-braid attachment remain unverified. |
| Absent-content and weight inverse families | [4aadf2ad1a](https://github.com/apellis/odd-lean/commit/4aadf2ad1a01769225042735c76b0a506fee56e9) | `b8608826bf37aa92e8d2b8f5779518e704e0d734` | Content inverse family producer and pair pass; weight inverse producer passes, paired consumer remains unverified. |
| Old probe local records | [b826b2952d](https://github.com/apellis/odd-lean/commit/b826b2952d53245551ae30196839560c123c8b6c) | `4d30d6f0034eb84204045db18a7546d4d3f9e19f` | Grid input families are separately checked; complete old boundary window, decomposition and Rouquier field factories remain unverified. |
| Local probe pre-Hom adjunction | [46db9c543d](https://github.com/apellis/odd-lean/commit/46db9c543dd11176e12ab9206b39545d1093c0df) | `6f0d300d5293fba2f1777e163cb5f1f3b9fb44a4` | Two producers and paired consumer pass; supplied adjacent local records remain explicit inputs, and full integration is separate. |
| Released old boundary drafts | [7545bf1cfa](https://github.com/apellis/odd-lean/commit/7545bf1cfa910294e3926842fe28823e1bc6b865) | `402fbf170ede80959966c9c8a6732e2e28e566bf` | Complete earlier source tree including three proposed boundary draft files; their verification is not claimed. |

## Principal, local-factor and vacuum comparison source trees

Each exact tree copy has only the verified research parent. Proposed source
is outside the checked library; scoped checks and full integration are separate.

| Argument | Preserved tree | Source revision | Scope |
| --- | --- | --- | --- |
| Recursive word-chart parity | [2aad3d79dd](https://github.com/apellis/odd-lean/commit/2aad3d79dd7e2e13488b2ae144aa02de0b145602) | `d7c4f61797cf288cff861530bc4657da0793e7e3` | Direct cyclic-parity content producer passes; complete weight parity and paired consumer are not verified at this snapshot. |
| Canonical principal mate comparison | [46a75426cc](https://github.com/apellis/odd-lean/commit/46a75426cc1c0a936eed8ee82f9300021efaada1) | `e75eac23b7797c10db2e895759eba48b7fea0cf5` | Literal crossing and endpoint fixes retained; latest folded evaluator header and paired consumer remain unverified. |
| Whole corrected mixed braid | [60753fefc8](https://github.com/apellis/odd-lean/commit/60753fefc84d8b066e9ee769b39cd468836d7123) | `bf8473ef22be7fa5762974b9b348c4d5e714c6b7` | Supported pointwise relation separately checked; whole natural-map endpoint join and paired consumer remain unverified. |
| Supported canonical local inverses | [b50ce4849e](https://github.com/apellis/odd-lean/commit/b50ce4849ef4f8089c516aa7d918f21b78866e88) | `a27134ad6685831cdd34225f8edf89f33cf8ab0e` | Proposed actual weighted-to-canonical From/To transport; principal-square dependency and complete paired consumer remain unverified. |
| Absent-weight inverse development | [d354302888](https://github.com/apellis/odd-lean/commit/d354302888069f0a8bb6bc554c7a64fef09c97a0) | `544cbd0d4cd1a62d9d9be976820626e5122bd17f` | Checked topical pointwise/family absent inverses, product/profile and cap fields; curated integration evidence remains separate. |
| Old probe boundary coefficients | [ca2f569853](https://github.com/apellis/odd-lean/commit/ca2f5698534758daf460d14b94fe56c16b379c20) | `3c6edc69f399c83fcbc3f398aeae254730773a2d` | Generic coefficient producer passes; actual old specialization, paired consumer and local record construction remain unverified. |
| Evaluated mixed bend and native row | [b2e9e556a6](https://github.com/apellis/odd-lean/commit/b2e9e556a6b8faaa53071f19164b768db8fc6e10) | `b2efd3f300fcef878bf10c5a96c7b1854560cf37` | Scoped producers and occupied consumers pass; original global-vacuum extension comparison and whole swapped action remain separate. |
| Tensor vacuum and proposed coordinates | [f07d19dfea](https://github.com/apellis/odd-lean/commit/f07d19dfea57e92771081ee4954042f3e561d325) | `c5c7d70b03621f5324978875ec4b2ea6cb00c478` | Tensor-vacuum core and occupied consumer pass; proposed whole-module scalar-coordinate extension remains unverified. |

## Principal and probe-cap source variants

Each exact tree copy has only the verified research parent. Pending proof
heads are not introduced as ancestors through these copies. No proposed
source is imported; separately checked successors retain their own scope.

| Argument | Preserved tree | Source revision | Scope |
| --- | --- | --- | --- |
| Word coefficient insertion | [7031748dc2](https://github.com/apellis/odd-lean/commit/7031748dc2e11aa2a1c5d6ae6aa151af425e8b56) | `c450056b272a5a9079133cebd1f677bccfa0b990` | Coefficient producer passes; occupied paired consumer and export remain unverified at this snapshot. |
| Canonical principal mate square | [a3974aa58a](https://github.com/apellis/odd-lean/commit/a3974aa58a48894ee66aef4a0ddd675b47a2ca61) | `49f1e817a674872bac4e1bf2b9210c77c5f6febc` | Generic square kernel and proposed consumer retained; final ordinary/native coend equality join remains unverified. |
| Supported content and weight local inverses | [aef85d4610](https://github.com/apellis/odd-lean/commit/aef85d46105f4f07c02b944235f550452635e316) | `4e20bc9ebe98a402cd82b85b00a89fd6f5422703` | Exact principal, unit and cap transport constructions retained; principal-square dependency and complete paired consumers remain unverified. |
| Old probe local record | [45c1e80b68](https://github.com/apellis/odd-lean/commit/45c1e80b6844139989568a535ecefe34c8f68060) | `33059467a41ea3de0bbaeaf64fc7c39cb3bd7aca` | Four producers pass; actual empty-content local inverse has no local-record premise. Paired occupied consumers remain unverified. |
| Old probe inverse-family variant | [5a5b9ab3e7](https://github.com/apellis/odd-lean/commit/5a5b9ab3e792d125059bf3eed1aa3de39fcc014c) | `243a19286f57c91c4dcdba2e98018275f328ebe9` | Generic inverse families and boundary variants retained before module-row API renaming; complete paired consumers and upper record remain unverified. |
| Probe local cap binding | [d7c3788c2e](https://github.com/apellis/odd-lean/commit/d7c3788c2e49e911bed0dfc608d46f6e42e1ecac) | `2cc13fab37d13fc734a47444b75c2e1fe5d0e8dd` | Producer passes: constructed old local record, regular and scalar evaluated cap identities, including F(E(T0)). Paired consumer and export remain unverified. |
| Corrected mixed braid field | [81767052fa](https://github.com/apellis/odd-lean/commit/81767052fae3eeaa110e25f1b6e7185231f49821) | `f5ec362fdb72bde950fc13b34409b9534bc3e825` | Five topical producer-consumer pairs pass strict scoped checks; exact original-parameter chosen braid field. Full integration gate remains separate. |

## Complete argument source variants

Every tree below is preserved exactly, including the mathematical source
and notes not yet integrated into the checked library. Tree-copy commits
have only the verified research parent; no pending proof head is made an
ancestor through these copies. Identical trees share a preserved commit.
The preservation itself changes only documentation in the checked tree.
Historical source trees can contain proposed or failing arguments; their
presence does not assert that the complete tree compiles.

| Source variant | Source revision | Preserved full tree |
| --- | --- | --- |
| `research/content-matrix-comparison` (branch tip) | `6dc3b556f30485665db29b0a75777d80408984b1` | [5ab5223932](https://github.com/apellis/odd-lean/commit/5ab5223932bb3a171272f4dfbc7431d26a9d3ada) |
| `research/content-principal-square` (branch tip) | `5e304448f794563ef5537d1cdb1f806c21f4f76f` | [2f5c8ebbcc](https://github.com/apellis/odd-lean/commit/2f5c8ebbcc06a40028eb511ac60410e9446111e6) |
| `research/content-supported-local-inverse` (branch tip) | `8aaead55e7117762447b95120913942a67a11d2a` | [044d8ed6f9](https://github.com/apellis/odd-lean/commit/044d8ed6f900b43bef71481ba3cc6520fcc651d3) |
| `research/elv-factor-family` (branch tip) | `804dd66d1867374289c9257a977486e43045cab8` | [b33ffd03ad](https://github.com/apellis/odd-lean/commit/b33ffd03ad0f1eb816d81b8e4f338f7dc8b860ab) |
| `research/evaluated-old-probe` (branch tip) | `b1d8f3d8284a2584b4e324e61be3bd75fb34a218` | [296411e67b](https://github.com/apellis/odd-lean/commit/296411e67bbededb7c7e31ccdd6ffdac46f4dfdf) |
| `research/module-zero-boundary` (branch tip) | `586adf8ad4255f7757a56a3458a8ffde1d057614` | [e6d7bc752c](https://github.com/apellis/odd-lean/commit/e6d7bc752c8ceb3f5b3592b3242f2439656e0a29) |
| `research/old-affine-relations` (branch tip) | `7a5029a857d7a8ac03b8d6ae4ff1f62090d4c0fa` | [d66e4b253e](https://github.com/apellis/odd-lean/commit/d66e4b253e8416004d8c61886d8b6b271ee13062) |
| `research/old-probe-local-record` (branch tip) | `e4bcb10d3c4d14ff924372ac0f1da2b82a46c1db` | [2cf3ffed79](https://github.com/apellis/odd-lean/commit/2cf3ffed792429c5f532e5d94b58da8dbd66d4aa) |
| `research/probe-canonical-content` (branch tip) | `d3f2c454a6cd7422debc1b5166d8523bec9f0dc5` | [0c33e0c227](https://github.com/apellis/odd-lean/commit/0c33e0c227ed55b8ae29ef09c4913fd44bee9056) |
| `research/probe-content-reindex` (branch tip) | `4d67b6db4b1ae8e5f70c34102a4c15fb9806ab5f` | [84f0c21f2e](https://github.com/apellis/odd-lean/commit/84f0c21f2e826b9a4c95591871eb8afddae7bce2) |
| `research/probe-factor-assembly` (branch tip) | `04e78b6125474f59469e6164b107cd9c10d29e49` | [c12b47eff8](https://github.com/apellis/odd-lean/commit/c12b47eff8b8bc4e34853e92ae90068c170366bf) |
| `research/probe-vacuum-loc-binding` (branch tip) | `c71712e411a0d33d6eafd3d722dc20f43563d728` | [e661ef0b68](https://github.com/apellis/odd-lean/commit/e661ef0b682ae0876cbc60cdd4a038c65bd4df4c) |
| `research/rouquier-multicolour` (branch tip) | `804dd66d1867374289c9257a977486e43045cab8` | [b33ffd03ad](https://github.com/apellis/odd-lean/commit/b33ffd03ad0f1eb816d81b8e4f338f7dc8b860ab) |
| `research/tensor-cap-transport` (branch tip) | `9c105a7504431a0ab882df7c74bcf08be1972ec2` | [09ef21d99c](https://github.com/apellis/odd-lean/commit/09ef21d99cd264a84ddcfaed2c074e7c64b49e2a) |
| `research/vacuum-mixed-entry` (branch tip) | `dba765139fb2fe0a55384508ff87d5b43bd1ddd3` | [170b8fe3d6](https://github.com/apellis/odd-lean/commit/170b8fe3d6a559fc17707eb207d24b49d475904d) |
| `research/vacuum-tensor-coordinates` (branch tip) | `9877e1da66c0bd159f3269d47d5b2ed23994af6f` | [9ceafbdc8c](https://github.com/apellis/odd-lean/commit/9ceafbdc8c2060e2b88ac62278d970b2de4870fb) |
| `research/weight-dot-transport` (branch tip) | `a85d1660658639a335284a99175199e9f6e44fea` | [84f1bb220a](https://github.com/apellis/odd-lean/commit/84f1bb220ae300bef1a0233a856b3fcb58d5661c) |
| `research/weight-local-inversion` (branch tip) | `f12d07a67cd88974e97c815e0430d453e0da28b6` | [1e4606bc38](https://github.com/apellis/odd-lean/commit/1e4606bc380efc250b1b77d76f2dd1422dd0b9c4) |
| `research/weight-mixed-braid` (branch tip) | `ca70d90cd523cfc690e376a8ac74ec260e9bdf28` | [3ec189f1ce](https://github.com/apellis/odd-lean/commit/3ec189f1cec29d21a1b9a93fbddf3d0fc6dfefdc) |
| `research/weight-mixed-braid-relation` (branch tip) | `f5ec362fdb72bde950fc13b34409b9534bc3e825` | [1090c95118](https://github.com/apellis/odd-lean/commit/1090c95118804db3fbeb62102d234e980fa070de) |
| `research/weight-multicolour-braid` (branch tip) | `8e577d90469885f9d943e0daf9b2e8db860bf6ae` | [8b646cbc0e](https://github.com/apellis/odd-lean/commit/8b646cbc0e3592a62de3cbadea7f6847ca88260e) |
| `research/weight-rouquier-local` (branch tip) | `650b9ebba2f1781ad8649943d9f986c6e9c1f27a` | [14018b14a4](https://github.com/apellis/odd-lean/commit/14018b14a40bc6ea06e6fc18a27a9640cd946a83) |
| `research/weighted-polynomial-caps` (branch tip) | `57a61e0bfd4092e5fa9f503ec4ef63c53e086f15` | [1eef38b5c1](https://github.com/apellis/odd-lean/commit/1eef38b5c16cc6335e2cfa8603e64174ad8ebbe6) |
| `research/word-chart-parity` (branch tip) | `d64a73f87fbeafd2402e2231021df6d38ff36324` | [58fa205b6d](https://github.com/apellis/odd-lean/commit/58fa205b6d18a487d5a637a840710861919c793c) |
| `research/word-coefficients` (branch tip) | `d143a004bc056b37f85c584d45abc46427de7cd9` | [f2bfddc748](https://github.com/apellis/odd-lean/commit/f2bfddc74820ae174ee63106f0c0cd4bd3631e5c) |
| `research/word-cross-evaluation` (branch tip) | `d2ea8420278b5b2e2900a40b900b8ea5d1e2f7eb` | [e19975dc1e](https://github.com/apellis/odd-lean/commit/e19975dc1e8a03991ec469e3576a4d2c9137b248) |
| `research/word-evaluation` (branch tip) | `05c0492999b6976e9ffb8fe3e965e8062187e66e` | [d6d0f2de75](https://github.com/apellis/odd-lean/commit/d6d0f2de7506dad1c66d3273f9e5ce99bd83a568) |
| `research/word-hom-coordinates` (branch tip) | `d143a004bc056b37f85c584d45abc46427de7cd9` | [f2bfddc748](https://github.com/apellis/odd-lean/commit/f2bfddc74820ae174ee63106f0c0cd4bd3631e5c) |
| `research/word-weight-contexts` (branch tip) | `5aa89762b550c9a5350d36fb24bca2bd8cd2b2fa` | [d3411425e1](https://github.com/apellis/odd-lean/commit/d3411425e196d351f7e4fc3b49ce3cbf491dcf77) |
| `research/content-supported-local-inverse (working source)` (working source) | `8aaead55e7117762447b95120913942a67a11d2a` | [c79b2902ba](https://github.com/apellis/odd-lean/commit/c79b2902ba59bedf70d451cae0d091d0ac74ea5c) |
| `research/evaluated-old-probe (working source)` (working source) | `b1d8f3d8284a2584b4e324e61be3bd75fb34a218` | [b9d9298e04](https://github.com/apellis/odd-lean/commit/b9d9298e04ce7847dac48e8d8574b5c1123befa4) |
| `research/word-cross-evaluation (working source)` (working source) | `d2ea8420278b5b2e2900a40b900b8ea5d1e2f7eb` | [7d2cfc6f3d](https://github.com/apellis/odd-lean/commit/7d2cfc6f3dc596b53784c9433f6701da30ab4a38) |
| `research/probe-content-reindex (working source)` (working source) | `4d67b6db4b1ae8e5f70c34102a4c15fb9806ab5f` | [ef53181050](https://github.com/apellis/odd-lean/commit/ef53181050a914dcfb682c996412ae41326e85c0) |
| `research/rouquier-multicolour (working source)` (working source) | `804dd66d1867374289c9257a977486e43045cab8` | [3a6240c6bd](https://github.com/apellis/odd-lean/commit/3a6240c6bdac98cfddc4f55a2614f73b96d2f894) |
| `research/weight-mixed-braid (working source)` (working source) | `ca70d90cd523cfc690e376a8ac74ec260e9bdf28` | [f63420d8fb](https://github.com/apellis/odd-lean/commit/f63420d8fb5067d57e6ff580343efcc04eaf595b) |
| `research/word-hom-coordinates (working source)` (working source) | `d143a004bc056b37f85c584d45abc46427de7cd9` | [6d07efe699](https://github.com/apellis/odd-lean/commit/6d07efe699314d60e0bcd12b685122434e62be3b) |
| `origin/research/old-affine-relations` (remote tip) | `7a5029a857d7a8ac03b8d6ae4ff1f62090d4c0fa` | [d66e4b253e](https://github.com/apellis/odd-lean/commit/d66e4b253e8416004d8c61886d8b6b271ee13062) |
| `origin/research/old-probe-local-record` (remote tip) | `51610015cb3d4bb4c015b3527a63000c8faea227` | [4f6b4dd2a4](https://github.com/apellis/odd-lean/commit/4f6b4dd2a49bcf061070cc5925bd2f663680b28d) |
| `origin/research/probe-canonical-content` (remote tip) | `d3f2c454a6cd7422debc1b5166d8523bec9f0dc5` | [0c33e0c227](https://github.com/apellis/odd-lean/commit/0c33e0c227ed55b8ae29ef09c4913fd44bee9056) |
| `origin/research/probe-factor-assembly` (remote tip) | `0034b2d87ccd3bb826a2b008c0f43874bfc9079b` | [a9f28fc676](https://github.com/apellis/odd-lean/commit/a9f28fc676ba6600c94668e3353ccae175273a77) |
| `origin/research/weight-mixed-braid-relation` (remote tip) | `f5ec362fdb72bde950fc13b34409b9534bc3e825` | [1090c95118](https://github.com/apellis/odd-lean/commit/1090c95118804db3fbeb62102d234e980fa070de) |
| `origin/research/weight-multicolour-braid` (remote tip) | `8e577d90469885f9d943e0daf9b2e8db860bf6ae` | [8b646cbc0e](https://github.com/apellis/odd-lean/commit/8b646cbc0e3592a62de3cbadea7f6847ca88260e) |
| `origin/research/weight-rouquier-local` (remote tip) | `650b9ebba2f1781ad8649943d9f986c6e9c1f27a` | [14018b14a4](https://github.com/apellis/odd-lean/commit/14018b14a40bc6ea06e6fc18a27a9640cd946a83) |
| `origin/research/word-chart-parity` (remote tip) | `d64a73f87fbeafd2402e2231021df6d38ff36324` | [58fa205b6d](https://github.com/apellis/odd-lean/commit/58fa205b6d18a487d5a637a840710861919c793c) |
| `origin/research/word-coefficients` (remote tip) | `d143a004bc056b37f85c584d45abc46427de7cd9` | [f2bfddc748](https://github.com/apellis/odd-lean/commit/f2bfddc74820ae174ee63106f0c0cd4bd3631e5c) |
| `origin/research/word-evaluation` (remote tip) | `05c0492999b6976e9ffb8fe3e965e8062187e66e` | [d6d0f2de75](https://github.com/apellis/odd-lean/commit/d6d0f2de7506dad1c66d3273f9e5ce99bd83a568) |
| `origin/research/word-weight-contexts` (remote tip) | `5aa89762b550c9a5350d36fb24bca2bd8cd2b2fa` | [d3411425e1](https://github.com/apellis/odd-lean/commit/d3411425e196d351f7e4fc3b49ce3cbf491dcf77) |

## Probe and vacuum assembly argument tree

The complete source tree [82ddc2011b](https://github.com/apellis/odd-lean/commit/82ddc2011bb42715e1c5fb03359271160fa38a45) retains the next probe and vacuum
arguments. Its sole parent is the verified research integration of #1010.
No pending proof integration head becomes an ancestor through this copy.
The history-preservation merge changes only this inventory and HANDOFF;
no proposed source is imported into the checked library.

| Topic | Source files in the preserved tree | Scope at preservation |
| --- | --- | --- |
| Probe weight dot inverse | `ELVProbeWeightDotUnit.lean` and paired consumer | Producer passes strict checking after the syntax repair; the concrete nonzero induced-vector consumer remains pending. |
| Adjacent old local record | `ELVInductionGridRelations.lean`, `ELVInductionGridLocal.lean`, `ELVOldContentLocal.lean` and paired consumers | Restored proposal; the final whole-Pi slide lifts and complete producer/consumer checks remain pending. |
| Evaluated and weight equal crossing | `ELVProbeEvaluatedCrossing.lean`, `ELVProbeWeightCrossing.lean` and paired consumers | Proposed full-subcategory restriction and weight-coordinate lift; complete checks remain pending. |
| Reservoir path and dot attachment | `SwappedAssembly/ReservoirWordFunctor.lean`, `ReservoirVacuumDot.lean` and paired consumers | Generic word-comparison producer passes; its bare-generator reversal test does not test the full factor comparison. Complete concrete-factor consumer and vacuum-dot checks remain pending. |
| Reservoir multicolour and whole-Hom coordinates | `ELVRouquierMulticolour.lean`, `ELVPowerWordHomCoordinates.lean` and paired consumers | Restored exact topical proposals; earlier scoped evidence is recorded separately, and fresh publication checks remain pending. |

The tree also includes the separately scoped-checked probe weight
adjunction/dot, old coefficient/direct-induction braid, evaluated distinct
mate inverse and supported/absent pair-induction sources. Their integration
claims belong in STATUS and their actual proof PRs. Preserving this tree
is not evidence that the entire tree builds. Recover individual files with
`git show 82ddc2011bb42715e1c5fb03359271160fa38a45:<repository-path>`.

## Probe relations and selected vacuum attachment argument tree

The complete source tree [418df8069e](https://github.com/apellis/odd-lean/commit/418df8069eb8cbc07b48201ad4fccde9907b3f59) retains the next probe relation and
vacuum attachment arguments. Its sole parent is the verified research
integration of #1013. Pending proof integration heads are not introduced
as ancestors by this copy. The history merge changes only this inventory
and HANDOFF; proposed source is not imported into the checked library.

| Topic | Source files in the preserved tree | Scope at preservation |
| --- | --- | --- |
| Evaluated local records | `ELVProbeEvaluatedLocal.lean` | Generic inverse restriction and several literal dot/mate comparisons pass in isolation; the complete producer and concrete consumer remain unverified. |
| Representative generator comparison | `ELVProbeReindexTensors.lean` | Proposed tensor formula for the canonical append/reindex adjunction comparison; complete proof and consumer remain pending. |
| Selected reservoir word value | `ELVReservoirWordValue.lean` and paired consumer | Draft identification with the explicit regular-power empty-word family; whole check is pending and attachment to the swapped vacuum Hom input is separate. |
| Reservoir vacuum dot | `SwappedAssembly/ReservoirVacuumDot.lean` and paired consumer | Generic zero-shift helpers pass in isolation; full generator attachment and actual-factor consumer remain pending. |
| Whole-Hom word coordinates | `ELVPowerWordHomCoordinates.lean` and paired consumer | Exact restored proposal; fresh publication checks remain pending despite earlier scoped evidence. |
| Rectangular induction slides | `ELVModuleInductionSlides.lean` and paired consumer | Producer argument passes; a naming collision found by the consumer is being repaired. Fresh exact paired checks remain pending. |

The tree also contains separately scoped-checked local records, the
reservoir multicolour presentation, reservoir path functor, probe dot unit,
weight signed slides, representative adjunction comparison and content
braid. Their integration evidence belongs to their own proof PRs and
STATUS. This preservation is not evidence that the whole snapshot builds.
Recover individual files with `git show 418df8069eb8cbc07b48201ad4fccde9907b3f59:<repository-path>`.

## Canonical local and central matrix attachment argument tree

The complete source tree [6b3aef99df](https://github.com/apellis/odd-lean/commit/6b3aef99dfb2669bf55d73bf5ea6531fb39a4314) preserves the next canonical local,
multicolour polynomial and observation attachment arguments. Its sole
parent is the verified research integration of #1017. Pending proof
integration heads are not introduced as ancestors by this copy. The
history merge changes only this inventory and HANDOFF, without importing
proposed source into the checked library.

| Topic | Source files in the preserved tree | Scope at preservation |
| --- | --- | --- |
| Selected canonical generators | `ELVProbeReindexMate.lean`, `ELVProbeReindexCrossing.lean`, `ELVProbeReindexRows.lean` | Proposed exact chosen mate/crossing and dotted unit/counit compatibility. Individual prefixes have scoped evidence; complete integration and target local records remain open. |
| Independent-dot polynomials | `ELVInductionPairPolynomial.lean`, `ELVOldPairPolynomial.lean`, `ELVInductionTriplePolynomial.lean` | Proposed original-parameter pair/triple polynomial identifications; final selected whole-weight quadratic and repeated-outer braid fields remain open. |
| Contextual Hom entries | `ELVTensorHomContexts.lean` | Proposed further outer-E context attachment to the same literal Hom-entry evaluation; no complete layer evaluation is asserted. |
| Pure principal sigma entry | `SwappedAssembly/Sigma/ReservoirPrincipal.lean` and paired consumer | Proposed use of the existing finite-sum and mate formulas to identify the prescribed pure-factor principal entry; full matrix and residual closure remain open. |

The tree also contains separately scoped-checked distinct slides, selected
block quadratic, normalized nested multicolour braid, reindexed local
inverse entries, arbitrary-word tensor Hom coordinates and native reservoir
cap/unit rows. Their full verification belongs to their own integration
PR and STATUS. This preservation does not assert that the complete snapshot
builds. Recover topical files with `git show 6b3aef99dfb2669bf55d73bf5ea6531fb39a4314:<repository-path>`.

## Chosen local, mixed matrix and literal layer attachment argument tree

The complete source tree [1cc3b498df](https://github.com/apellis/odd-lean/commit/1cc3b498df47550c84691cfbe58896cc6d0aecc0) preserves the next chosen-action,
central-matrix and observation arguments. Its sole parent is the verified
research integration of #1020. Pending proof integration heads are not
introduced as ancestors by this copy. The history merge changes only
this inventory and HANDOFF, without importing proposed source into the
checked library.

| Topic | Source files in the preserved tree | Scope at preservation |
| --- | --- | --- |
| Canonical local and missing boundary | `ELVProbeAppendToMateReindex.lean`, `ELVProbeAppendUpperLoop.lean`, `ELVProbeMissingCoefficients.lean` | Proposed chosen mate/upper-loop transport and evaluated missing-colour coefficients. Prefixes and individual producers have scoped evidence; complete paired checks and selected local records remain separate. |
| Stored corrected braid | `ELVProbeStoredMixedBraid.lean` | Proposed literal stored-content corrected relation using the checked changing seven-edge grid; evaluated and weight fields remain open. |
| Supported global distinct mate | `ELVProbeWeightMixedCoordinates.lean` | Proposed supported-coordinate identification with the constructed stored-target inverse. Global `invNe` is not asserted. |
| Literal layer matrix | `SwappedAssembly/ReservoirLayerGenerators.lean` | Proposed actual layer-map comparison at zero probe content, with both contexts; no complete action observation is asserted. |
| Probe-to-reservoir bend | `SwappedAssembly/Sigma/ProbeToReservoirBend.lean` | Proposed actual mixed diagonal bend with its selected shifted caps and coefficient chart. Complete matrix and residual ideal closure remain open. |

The tree also contains separately scoped-checked stored-target distinct
mate inverses and dotted rows, nested corrected braid and seven-edge
transfer, product inverses, generic zero-loop and boundary-chart adapters,
actual reservoir principal entry, contextual half-turn generators and
the literal affine-layer quotient square. Their full verification belongs
to their own integration PR and STATUS. This preservation does not assert
that the complete snapshot builds. Recover topical files with
`git show 1cc3b498df47550c84691cfbe58896cc6d0aecc0:<repository-path>`.

## Whole-weight, central matrix and observation synthesis argument tree

The complete source tree [a15c1058b0](https://github.com/apellis/odd-lean/commit/a15c1058b0bdb96069baa88e54ca9170e0510323) preserves the proposed next attachments.
Its sole parent is the verified research integration of #1023. Pending
proof-integration heads are not introduced as ancestors. The preservation
merge changes only this inventory and HANDOFF; proposed source is not
imported into the checked library.

| Topic | Source files in the preserved tree | Scope at preservation |
| --- | --- | --- |
| Global local inverses | `ELVProbeWeightLocalMateCoordinates.lean`, `ELVProbeWeightAbsentInverse.lean`, `SKM/AugmentedInverseEvaluation.lean` | Proposed principal/absent coordinate attachment, pointwise evaluation and whole-product local inverse assembly. The complete probe family is not asserted. |
| Whole-weight braid paths | `ELVProbeWeightPathCoordinates.lean`, `ELVProbeWeightTripleCrossCoordinates.lean`, `ELVProbeWeightTripleDots.lean` | Proposed shared path, independently whiskered crossing and dot coordinates. The remaining general/corrected whole-weight braid fields are not asserted. |
| Central path matrix | `SwappedAssembly/Sigma/CentralPaths.lean` | Proposed path indices retaining absent pure corners before the whole augmented-matrix chart. Central invertibility remains open. |
| Actual reservoir component bounds | `ELVPostCoefficientEvaluation.lean` | Proposed specialization of the checked finite coefficient expansion to the literal ELV output evaluation and its constructed nilpotence bound. Complete paired verification and shifted/bent attachment remain separate. |

The tree also contains separately scoped-checked selected evaluated mate
and row squares, present-colour inverse records, whole-weight distinct
inversion and cap/unit coordinates, both pure principal entries, both
mixed bends, contextual reservoir matrices, and concrete tensor-Hom
source-layer class squares. Their verification belongs to their own
integration PRs and STATUS; this preservation does not assert that the
complete snapshot builds. Recover topical files with
`git show a15c1058b0bdb96069baa88e54ca9170e0510323:<repository-path>`.

## Supported presentation and represented degree argument tree

The complete source tree [8bb3b36820](https://github.com/apellis/odd-lean/commit/8bb3b3682097d0d065d1c95d60979f02c74a680d) preserves the next proposed attachments.
Its sole parent is the verified #1026 research integration `afd225cc`.
Pending proof-integration heads are not ancestors of this snapshot.
The preservation merge changes only this inventory and HANDOFF; its
unfinished source is not imported into the checked library.

The tree retains the chosen general/corrected braid and multicolour
package drafts, actual probe–reservoir coefficient-field draft, formal
supported-sector indexing, literal two-word reservoir dot/cross cells,
and the represented integer-grading construction. Their incomplete
verification remains explicit. The exact residual degree target is in
`ReservoirClosureDegree.md`; parity-only inverse results do not discharge it.

It also contains separately scoped-checked local probe family and inverse
records, exact-content support/closure and selected vacuum, complete
positive/negative central matrix comparisons, mixed denominator units and
matrix inverse naturality. Their verification belongs to their own
integration and STATUS. This snapshot does not claim that its complete
source tree builds. Recover individual files with
`git show 8bb3b3682097d0d065d1c95d60979f02c74a680d:<repository-path>`.
