import Lake
open Lake DSL

package «lean-mam» {
}

require std from git "https://github.com/leanprover/std4" @ "main"
require mathlib4 from git "https://github.com/leanprover-community/mathlib4" @ "master"

lean_lib «src/Cislo1»
lean_lib «src/Cislo2»
lean_lib «src/Cislo3»

@[default_target]
lean_lib all where
  globs := #[.submodules `src]
