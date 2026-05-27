import Lake
open Lake DSL

package «entropic_test» where
  -- add package configuration options here

lean_lib «EntropicTest» where
  -- add library configuration options here

@[default_target]
lean_exe «entropic_test» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
