# ACVF quantifier elimination

The Palomar submission selects ACF, ordinary nontrivial ACVF, and nontrivial
ACVF in the corrected RV language. Trivial valuation results remain in the
released development but are excluded from this submission. `Challenge`,
`Solution`, and `comparator.json` identify the three compared entry points.
No novelty of the classical QE theorems is claimed. The formalization supplies
foundations for further formalized model theory and VF/RV geometry; no search
establishing novelty of the formalization is claimed.

The ordinary valued-field argument adapts Chapter 2 of William Andrew
Johnson's [*Fun with Fields* (Berkeley dissertation, 2016)](https://math.berkeley.edu/~willij/drafts/will-thesis.pdf).
The ACF development applies the generic criterion to field inputs. The RV
theorem supplies the paper's corrected-language foundation and uses the
ordinary valued-field development.

Lean formalization of quantifier elimination for algebraically closed fields,
ordinary algebraically closed valued fields, and the corrected RV language for
Yimu Yin, *Special transformations in algebraically closed valued fields*
(APAL 2010, arXiv:1006.2467).

## Lean blueprint

[Read the blueprint](https://daviddhilbert.github.io/ACVF-QE/)
· [Theorem dependency graph](https://daviddhilbert.github.io/ACVF-QE/dependency-graph.svg)
· [Blueprint source and build instructions](blueprint/README.md)

The blueprint links the ACF, ordinary valued-field, and RV arguments to their
checked Lean declarations and keeps the trivial and nontrivial valuation cases separate.

## Theorems

- `JohnsonACF.hasQEb`: pure ACF QE through Johnson's criterion, all characteristics.
- `hasQE_ACVF_val` and `hasQEb_ACVF_val`: ordinary nontrivially valued ACVF QE
  in the ring language with valuation comparison, through Will Johnson's argument.
- `ValPM.hasQE_ACVF_trivial_val` and `ValPM.hasQEb_ACVF_trivial_val`:
  ordinary trivially valued ACVF QE in the same language. The defining
  axiom reduces valuation comparison to two zero tests.
- `SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination`:
  `HasQE Axioms.ACVF` in the tagged two-sorted encoding with named RV inversion,
  for nontrivially valued models. Inputs and outputs are well-sorted, with
  arbitrary parameters and a uniform quantifier-free equivalent over models
  in that case. The intended theorem has a separate trivially valued case.
  See [the theory errata](LANGUAGE-ERRATA.md#trivial-valuations-and-qe).
- `SpecialTransformations.TrivialRV.canonical_trivial_rv_qe`: the separate
  trivially valued case for canonical RV structures of algebraically closed
  fields, in every characteristic. The proof reduces to ring-language QE
  and translates the result back to a well-sorted RV formula.
- `SpecialTransformations.TrivialRV.hasQE`: `HasQE` for the common
  sentence theory of those canonical trivially valued models.

The paragraph immediately before Convention 2.5 explicitly omits inverse
symbols from both VF and RV. The author clarified on November 5, 2026 that
RV inversion must be named for the intended QE statement. Adding this symbol
corrects the paper's language specification; the omission was not only in the
Lean transcription. The existing implementation already uses the corrected
language, with RV inversion totalized by `0⁻¹ = 0`; no VF inverse symbol is added.
Thus the RV QE theorem concerns the corrected language, not the literal
inverse-free signature in print. See [language erratum](LANGUAGE-ERRATA.md).
For subsequent work with definable sets, inverse is already definable by
its graph. Naming it does not change definable sets or acl/dcl over the same
parameters, so the later sections require no corresponding change.
Mathlib's valuation order is opposite to the paper's value-group order;
the bridges account for that reversal explicitly.

## Build and audit

Install elan, then run from this directory:

```sh
lake exe cache get
lake build
lake env python3 scripts/verify.py
```

Lean is pinned to 4.35.0 and Mathlib to its matching release commit.
`import ACVFQE` exposes the three developments. Proof modules currently retain
their short import names from the original development to preserve the checked
proofs. `scripts/verify.py` checks all shipped modules, performs a fresh combined
import and prints the headline types and axiom dependencies. Its cache and logs
are confined to `.scratch/local-qe-check`.

The shared `Proofs/Enc.lean` retains the definitions for C-minimality.
The checked C-minimality theorem is in
[Section 3 of the paper repository](https://github.com/daviddhilbert/special-transformations/blob/e4ece39cba56540ef7f2be4fa21b365b640a8c7f/Section3/CMinimal.lean).
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
source hashes for the initial extraction; later documentation corrections may
change comments without changing the Lean declarations. Unrelated experimental
snapshots are omitted. The paper-specific namespaces are retained to identify
the exact statement proved.

`CountableSaturatedExtension.lean` adapts Elliot Glazer's `definable-saturated`,
commit `e683bba9e758323b43dd1d6206ed2f6fc9510f06`, found through Palomar entry
PALOMAR-2026-09-19-000005 v1. The adaptation is licensed under Apache-2.0;
see `vendor/definable-saturated/` for its LICENSE, NOTICE and provenance.
Other project code retains the source repository's MIT license.

The development includes agent-assisted formalization. Verification establishes
the stated Lean theorems and their dependencies; the README identifies the
precise language and theorems to support mathematical review.
