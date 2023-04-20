import Lake
open Lake DSL

package «hello_mathlib4» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «HelloMathlib4» {
  -- add any library configuration options here
}
