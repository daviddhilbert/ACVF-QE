# Palomar preparation

Author and responsible maintainer: Yimu Yin.

This candidate starts from the released v1.1 source commit
478dd4bdd19c1fc1b75750b137f73d1eac5c4dfa. The existing proof expressions,
language definitions and exported theorem statements are retained.

The initial module-system migration follows Lean 4.35.0's documented recipe:
add `module`, make imports public, and expose the existing public definitions.
The verifier now recognizes public imports when computing compilation order.
Fresh compiler and headline audits are required; old release checks do not
verify this migration.

This branch is preparation, not a Palomar submission. Independent statement
packaging and the full Palomar mechanical verification remain outstanding.

The independent package now compares four entry points: ACF, nontrivial
ordinary ACVF, trivial ordinary ACVF, and the corrected nontrivial RV theory.
The separate trivial-RV result remains in the library, outside this selection.
Comparator requires exact declaration agreement, beyond ordinary Lean
definitional equality. Finite indices in the Horner polynomial now use explicit
arithmetic proofs, and the trivial-valuation axiom uses explicit variable and
zero-term constructors. These retain the mathematical definitions and theorem
statements. Each change requires fresh compiler, type, axiom and Comparator
checks; an earlier passing run does not certify a later candidate.
