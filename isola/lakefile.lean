-- Lake build file for MSC Agent Coordination Formalization
-- Paper: "Provable Coordination for LLM Agents via Message Sequence Charts"
--
-- Project layout:
--   MSCAgents/
--     Syntax.lean            — def:phase-syntax
--     Alphabets.lean         — def:alphabets
--     MSCConcat.lean         — def:msc-concat, rem:concat-msc
--     CanonicalMSC.lean      — def:base-msc
--     InductiveSemantics.lean — def:inductive-msc, rem:sem-complete

import Lake
open Lake DSL

package «MSCAgents» where

-- The library root is MSCAgents; Lean files live in MSCAgents/*.lean
@[default_target]
lean_lib «MSCAgents» where
  srcDir := "."
  globs := #[.submodules `MSCAgents]
