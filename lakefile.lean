import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

package «bc-lean» where
  -- Default targets are set via `@[default_target]` on declarations below
  restoreAllArtifacts := true

@[default_target]
lean_lib Bc where
  -- Compile all modules under the `Bc` namespace
  globs := #[.submodules `Bc]

@[default_target]
lean_exe «bc-parse-test» where
  root := `Bc.ParseTestMain

@[default_target]
lean_exe «bc-lean» where
  root := `Main
