import Lake
open Lake DSL

package «lean-mam» {
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

lean_lib «mam/Cislo1»
lean_lib «mam/Cislo2»
lean_lib «mam/Cislo3»
lean_lib «mam/Cislo4»
lean_lib «mam/Cislo5»

@[default_target]
lean_lib all where
  globs := #[.submodules `mam]
