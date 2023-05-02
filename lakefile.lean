import Lake
open Lake DSL

package «lean-mam» where
  moreServerArgs := #["-DautoImplicit=false"]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

lean_lib «mam/Cislo1»
lean_lib «mam/Cislo2»
lean_lib «mam/Cislo3»
lean_lib «mam/Cislo4»
lean_lib «mam/Cislo5»

@[default_target]
lean_lib all where
  moreLeanArgs := #["-DautoImplicit=false"]
  globs := #[.submodules `mam]
