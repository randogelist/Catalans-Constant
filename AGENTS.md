# Project instructions

- Run Lean compilation and proof verification only on GitHub Actions CI. Do not install or execute Lean in the local assistant workspace.
- Preserve the Catalan closure theorem and its explicit universal `ArithmeticExhaustion` premise. Do not describe a finite seed as an unconditional irrationality proof.
- Do not introduce proof placeholders, custom axioms, or `native_decide`.
- Keep the main README concise and present conditional formal closure as the main result.
- Preserve the original 24 Lean source files unless a specific repair or mathematical extension requires changes; retain the inherited native Windows `run.cmd`.
- Reuse compatible Mathlib caches and let Lake invalidate project modules when sources, dependencies, or the toolchain change.
- Current CI logs are the acceptance record. Historical package receipts are provenance only.
