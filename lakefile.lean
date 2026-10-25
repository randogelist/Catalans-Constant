import Lake
open Lake DSL

package catalanClosure where
  version := v!"0.2.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "db584cd6d46c92f209a44c0f1c829460d327499d"

lean_lib GPBKQRXY where
  globs := #[`GPBKQRXY.+]

@[default_target]
lean_lib CatalanAnchor

@[default_target]
lean_lib Main
