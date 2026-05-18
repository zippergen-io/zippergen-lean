import Lake
open Lake DSL

package «CPLMonitor» where

lean_lib «CPLMonitor» where
  srcDir := "."
  globs := #[.submodules `CPLMonitor]

