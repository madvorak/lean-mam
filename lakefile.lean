import Lake
open Lake DSL

package «lean-mam» {
}

@[default_target]
lean_exe «lean-mam» {
  root := `Main
}

require std from git "https://github.com/leanprover/std4" @ "main"
require mathlib4 from git "https://github.com/leanprover-community/mathlib4" @ "master"

lean_lib Cislo1
lean_lib Cislo2
lean_lib Cislo3
