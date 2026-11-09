# Working on ACVF QE

- Preserve the exact exported QE statements. ACF, ordinary valued-field ACVF,
  and RV-language ACVF are separate entry points; document which is changed.
- Use the pinned Lean 4.35.0 and Mathlib commit. Keep the Lake configuration
  portable; do not introduce local absolute dependency paths.
- Run `lake env python3 scripts/verify.py` for proof changes. Require exit 0
  and fresh headline signature/axiom audits. Accepted axioms are `propext`,
  `Classical.choice`, and `Quot.sound`. Explicit theorem hypotheses must also
  be inspected; a clean axiom list alone does not discharge them.
- The RV language includes inversion as a function, totalized at zero.
  The author clarified on November 5, 2026 that the paper explicitly omits
  inverse symbols before Convention 2.5 and that RV inversion must be named
  for the intended QE statement. This corrects the paper's language
  specification; it was not only a Lean transcription error. The RV QE
  theorem uses this corrected language, while VF inversion remains unnamed.
  See `LANGUAGE-ERRATA.md`; earlier attribution claims are superseded.
  Later definable-set work needs only definability of inverse. The named
  function adds no definable sets and does not require changing downstream
  statements; distinguish this from the literal QE/term-language question.
  `pK` denotes nonzero residue elements; `pInK` includes residue zero.
  Mathlib's multiplicative valuation order reverses the paper's value-group
  order. Preserve these conventions in every bridge.
- `Enc.lean` is an inherited language snapshot and retains the definitions
  used by C-minimality. The checked C-minimality theorem belongs to
  Section 3 of the paper repository.
- Search existing local and external formalizations before rebuilding a
  substantial prerequisite. Read actual statements and dependencies; port
  only with attribution and a fresh compiler/axiom check.
- Preserve the MIT license and the Apache-2.0 LICENSE/NOTICE for the adapted
  ultrapower proof. `SOURCE-MANIFEST.json` records the initial extraction;
  update provenance when new external code is introduced.
- Keep scratch work and compiler output in `.scratch/`, outside version
  control. Record verification limits honestly. This repository is independent
  of `daviddhilbert/special-transformations`.
