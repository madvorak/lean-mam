import Lake
open Lake DSL

package «lean-mam» where
  moreServerArgs := #["-DautoImplicit=false"]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib all where
  moreLeanArgs := #["-DautoImplicit=false"]
  globs := #[.submodules `mam]
