import Lake
open Lake DSL

package «runwai_project» where
  -- Settings applied to both builds and interactive editing
  --leanOptions := #[
  --  ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  --]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «Runwai» where
lean_lib «Test» where

@[default_target]
lean_exe «runwai» where
  root := `Main
  supportInterpreter := true
  --supportInterpreter := true
  --moreLinkArgs := #["-fuse-ld=lld", "-rdynamic"]
  -- add any library configuration options here
