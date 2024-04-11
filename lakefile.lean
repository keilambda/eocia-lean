import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "v4.7.0"

package «eocia-lean» where
  -- add package configuration options here

lean_lib «EociaLean» where
  -- add library configuration options here

@[default_target]
lean_exe «eocia-lean» where
  root := `Main
