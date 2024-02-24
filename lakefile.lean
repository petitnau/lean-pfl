import Lake
open Lake DSL

package «dice-lean» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require assertCmd from git
  "https://github.com/pnwamk/lean4-assert-command.git"

@[default_target]
lean_lib Dice {
  -- add any library configuration options here
}
