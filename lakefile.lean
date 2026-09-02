import Lake
open Lake DSL

package «clrs-lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`doc.verso, true⟩
  ]
  moreLeanArgs := #[
    "-Dwarn.sorry=false"
  ]

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

require verso from git
  "https://github.com/leanprover/verso" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0-rc1"

@[default_target]
lean_lib «CLRSLean» where
  srcDir := "src"
