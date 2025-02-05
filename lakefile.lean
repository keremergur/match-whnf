import Lake
open Lake DSL

require "leanprover-community" / "Qq" @ git "master"

package «match-whnf» where
  -- add package configuration options here

lean_lib «MatchWhnf» where
  -- add library configuration options here

@[default_target]
lean_exe «match-whnf» where
  root := `MatchWhnf.MatchWhnf
