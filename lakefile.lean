import Lake
open Lake DSL

package «pre-4» {
  -- add package configuration options here
}

lean_lib «Pre4» {
  -- add library configuration options here
}

@[default_target]
lean_exe «pre-4» {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
