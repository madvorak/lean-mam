import Lake
open Lake DSL

package «lean-mam» {
}

@[default_target]
lean_exe «lean-mam» {
  root := `Main
}

lean_lib Cislo1
lean_lib Cislo2
