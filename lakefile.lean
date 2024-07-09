import Lake
open Lake DSL

package «TypeTheory» where
  -- add package configuration options here

lean_lib «TypeTheory» where
  -- add library configuration options here

@[default_target]
lean_exe «typetheory» where
  root := `Main
