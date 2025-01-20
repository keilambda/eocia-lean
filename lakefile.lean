import Lake
open Lake DSL

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.16.0-rc2"

package «eocia-lean» where
  -- add package configuration options here

lean_lib «EociaLean» where
  -- add library configuration options here

@[default_target]
lean_exe «eocia-lean» where
  root := `Main
