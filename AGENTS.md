# Working on ACVF QE

- Preserve the exact exported QE statements. ACF, ordinary valued-field ACVF,
  and RV-language ACVF are separate entry points; document which is changed.
- Use the pinned Lean 4.33.1 and Mathlib commit. Keep the Lake configuration
  portable; do not introduce local absolute dependency paths.
- Run `lake env python3 scripts/verify.py` for proof changes. Require exit 0
  and fresh headline signature/axiom audits. Accepted axioms are `propext`,
  `Classical.choice`, and `Quot.sound`. Explicit theorem hypotheses must also
  be inspected; a clean axiom list alone does not discharge them.
- The RV language includes inversion as a function, totalized at zero.
  The paper already stipulates the RV group structure in Definition 2.2.
  The inverse symbol was omitted from the original Lean transcription;
  restoring it corrected the transcription, not the paper. Do not describe
  inversion as an extra assumption or a deviation from the paper.
  `pK` denotes nonzero residue elements; `pInK` includes residue zero.
  Mathlib's multiplicative valuation order reverses the paper's value-group
  order. Preserve these conventions in every bridge.
- `Enc.lean` is an inherited language snapshot. Its separate C-minimality
  placeholder is outside the QE dependency chain and outside this package's
  claims. Never use it to prove a QE result.
- Search existing local and external formalizations before rebuilding a
  substantial prerequisite. Read actual statements and dependencies; port
  only with attribution and a fresh compiler/axiom check.
- Preserve the MIT license and the Apache-2.0 LICENSE/NOTICE for the adapted
  ultrapower proof. `SOURCE-MANIFEST.json` records the initial extraction;
  update provenance when new external code is introduced.
- Keep scratch work and compiler output in `.scratch/`, outside version
  control. Record verification limits honestly. This repository is independent
  of `daviddhilbert/special-transformations`.
