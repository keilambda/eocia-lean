import Lake
open Lake DSL

package «eocia-lean» where
  -- add package configuration options here

lean_lib «EociaLean» where
  -- add library configuration options here

@[default_target]
lean_exe «eocia-lean» where
  root := `Main
