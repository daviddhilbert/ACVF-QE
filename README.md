# ACVF quantifier elimination

Lean formalization of quantifier elimination for algebraically closed fields,
ordinary algebraically closed valued fields, and the RV language used in
Yimu Yin, *Special transformations in algebraically closed valued fields*
(APAL 2010, arXiv:1006.2467).

## Theorems

- `JohnsonACF.hasQEb`: pure ACF QE through Johnson's criterion, all characteristics.
- `hasQE_ACVF_val` and `hasQEb_ACVF_val`: ordinary nontrivially valued ACVF QE
  in the ring language with valuation comparison, through Will Johnson's argument.
- `SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination`:
  `HasQE Axioms.ACVF` in the tagged two-sorted RV encoding, with no additional
  mathematical hypotheses. Inputs and outputs are well-sorted, with arbitrary
  parameters and a uniform quantifier-free equivalent over all models.

The RV language names inversion, including inverse of zero equal to zero.
Mathlib's valuation order is opposite to the paper's value-group order;
the bridges account for that reversal explicitly.

## Build and audit

Install elan, then run from this directory:

```sh
lake exe cache get
lake build
lake env python3 scripts/verify.py
```

Lean is pinned to 4.33.1 and Mathlib to its matching release commit.
`import ACVFQE` exposes the three developments. Proof modules currently retain
their short import names from the original development to preserve the checked
proofs. `scripts/verify.py` checks all shipped modules, performs a fresh combined
import and prints the headline types and axiom dependencies. Its cache and logs
are confined to `.scratch/local-qe-check`.

The shared `Proofs/Enc.lean` is preserved from the paper repository. It includes
an unrelated C-minimality placeholder; none of the QE theorems depends on it.
The exported QE audits contain only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx` or custom axioms. C-minimality is outside this
package's claims.

## Proof structure and provenance

The ACF and ordinary valued-field proofs use prime models, amalgamation,
one-variable existential closure, and compactness. The RV proof constructs
compatible residue and VF embeddings and applies a proved countable-language
saturated-model criterion. Downward Lowenheim--Skolem and a saturated
nonprincipal ultrapower supply the required models. No CH is assumed, and
the final theorem has no restriction to countable models or parameter sets.

Sources were extracted from `daviddhilbert/special-transformations` with the
author's authorization. `SOURCE-MANIFEST.json` records original paths and exact
source hashes; unrelated experimental snapshots are omitted. The paper-specific
namespaces are retained to identify the exact statement proved.

`CountableSaturatedExtension.lean` adapts Elliot Glazer's `definable-saturated`,
commit `e683bba9e758323b43dd1d6206ed2f6fc9510f06`, found through Palomar entry
PALOMAR-2026-09-19-000005 v1. The adaptation is licensed under Apache-2.0;
see `vendor/definable-saturated/` for its LICENSE, NOTICE and provenance.
Other project code retains the source repository's MIT license.

The development includes agent-assisted formalization. Verification establishes
the stated Lean theorems and their dependencies; the README identifies the
precise language and theorems to support mathematical review.
