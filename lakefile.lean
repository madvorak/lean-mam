import Lake
open Lake DSL

package «lean-mam» {
  -- add package configuration options here
}

lean_lib «LeanMam» {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean-mam» {
  root := `Main
}
