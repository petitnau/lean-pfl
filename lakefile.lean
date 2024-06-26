import Lake
open Lake DSL

package «dice-lean» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"


-- require LeanCopilot from git
--   "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.2.2"


@[default_target]
lean_lib Dice {
  -- moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
  -- add any library configuration options here
}

lean_lib Data {}
lean_lib Math {}
