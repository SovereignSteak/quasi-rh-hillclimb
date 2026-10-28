#!/bin/bash
# usage: gen.sh <import-module> <module-prefix> -> writes a Lean file auditing every decl whose module starts with prefix
cat <<LEAN
import $1
open Lean Elab Command Meta

#eval show CommandElabM Unit from do
  let env ← getEnv
  let pre : Name := \`$2
  let std : List Name := [\`propext, \`Classical.choice, \`Quot.sound]
  let mut n := 0
  let mut bad := 0
  let mut thms := 0
  for (c, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless pre.isPrefixOf mod do continue
    n := n + 1
    if ci matches .thmInfo _ then thms := thms + 1
    let axs ← liftCoreM (Lean.collectAxioms c)
    let nonstd := axs.filter (fun a => !std.contains a)
    if !nonstd.isEmpty then
      bad := bad + 1
      logInfo m!"NONSTANDARD {c} : {nonstd.toList}"
    if ci matches .axiomInfo _ then logInfo m!"AXIOM DECLARED {c} in {mod}"
  logInfo m!"AUDIT SUMMARY prefix={pre} declarations={n} theorems={thms} nonstandard={bad}"
LEAN
