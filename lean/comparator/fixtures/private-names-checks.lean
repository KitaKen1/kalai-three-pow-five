open Lean in
run_elab do
  let a := (Lean.Name.num `KalaiReplayPrivate.KalaiFCPrefixPart8 0) ++ `Kalai5.E18low.remainingCells.match_1.eq_1
  let b := (Lean.Name.num `KalaiReplayPrivate.KalaiFCPrefixPart9 0) ++ `Kalai5.E18low.remainingCells.match_1.eq_1
  unless Lean.privateToUserName a != Lean.privateToUserName b do
    throwError "private names still collide"
  unless (← getEnv).contains a && (← getEnv).contains b do
    throwError "missing renamed declaration"
  unless KalaiProofReplayShared.replayName `_private "MathlibImported" == `_private.MathlibImported do
    throwError "imported private name changed"
  logInfo "PRIVATE_NAME_FIXTURE_PASS"
