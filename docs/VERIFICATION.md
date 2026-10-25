# CI verification and provenance

Lean verification runs on GitHub Actions, on `ubuntu-24.04`. It does not run in
the local assistant workspace. The workflow installs the official Lean 4.33.0
Linux release and checks its SHA256 before use. Mathlib and its transitive
dependencies are pinned by `lake-manifest.json`.

- Lean toolchain: `leanprover/lean4:v4.33.0`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d` (release `v4.33.0`).
- Lean release SHA256: `4b3fb03c29a1e0a253fb1d11f9bae3725f19a0dc6fc09b3ea16d2c9df3349e2c`.

The workflow restores compatible dependency caches, fetches the required Mathlib
artifacts, builds the project with Lake, and freshly executes
`CatalanAnchor/Audit.lean`. The audit parser requires exactly the declarations
listed there and rejects any axiom outside `propext`, `Classical.choice`, and
`Quot.sound`. Missing, duplicate, malformed, or unexpected audit records fail CI.
An additional source scan rejects proof placeholders and trust escapes.
The allowlist is a transitive dependency check for the 88 listed declarations;
it is not a claim that every Mathlib declaration has been separately audited.

Build, axiom, source-scan, dependency, and environment logs are uploaded as a
workflow artifact. A passing run identifies its exact commit and pinned
environment. The live Actions badge is the current status; older receipts do
not establish the status of a new commit.

## Original package

Sources come from `CATALAN_CLOSURE_REDUCTION_v0_2_0.zip`, SHA256:

`a8b3065823982a7a7ff354882b1da8f5097636252a4070fa46133c1d24a9f10c`.

The 24 original Lean files and `run.cmd` are preserved byte for byte. The
original README is retained as [PACKAGE_README.md](PACKAGE_README.md).
`AXIOM_AUDIT.txt`, `VALIDATION.txt`, and `SHA256SUMS.txt` are original historical
package records, not logs from this repository's new CI run. The checksum list
refers to the original layout, where the package README was at the root.

The original record does not identify the precise historical Mathlib commit.
The pinned compatible release above is therefore verified anew by hosted CI.
The original Windows runner remains available for the user's established
offline setup; it is not the GitHub Actions entry point.
