import Lake
open Lake DSL

package «matrix_sieve» where
  -- Configuration settings

require mathlib from git
  "https://github.com" @ "v4.7.0"

@[default_target]
lean_lib «Sieve» where
  -- Library configuration
