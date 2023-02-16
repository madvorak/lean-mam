import Lake
open Lake DSL

package «lean-mam» {
  -- add package configuration options here
}

@[default_target]
lean_exe «lean-mam» {
  root := `Main
}

lean_lib Cislo1
lean_lib Cislo2
