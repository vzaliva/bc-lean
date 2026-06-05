import Lake
open Lake DSL

-- No external dependencies: the project uses only the Lean toolchain's `Std`
-- (e.g. `Std.Data.TreeMap`, `Std.Internal.Parsec` in the XML bridge) and core
-- tactics, so it needs neither mathlib nor batteries.
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
