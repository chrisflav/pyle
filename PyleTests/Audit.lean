import PyleTests.Store

/-!
# The audit log

A chain that verifies, and every way of breaking one that the chain is meant to
show: a changed field, a removed record, records in another order, a forged
`prev`.
-/

namespace PyleTests

open Pyle Pyle.Audit

/-- The encodings the hash is over. -/
def encodingTests : IO Unit := do
  group "audit: encoding"
  checkEq "numbers are 8 bytes, big-endian" (encodeNat 258).toList [0, 0, 0, 0, 0, 0, 1, 2]
  checkEq "strings carry their length" (encodeStr "ab").toList [0, 0, 0, 0, 0, 0, 0, 2, 97, 98]
  checkEq "an absent field is one zero byte" (encodeOpt none).toList [0]
  check "absent and empty differ" (encodeOpt none != encodeOpt (some ""))
  checkEq "the genesis is 32 zero bytes" genesis.toList (List.replicate 32 0)

/-- Records through the store, and tampering with them. -/
def chainTests : IO Unit := withCtx fun ctx _ => do
  group "audit: chain"
  let s := ctx.store
  let r1 : Record :=
    { event := .signIn, outcome := .failure, userName := some "alice",
      factor := some "webauthn:abc", clientAddress := "1.2.3.4",
      detail := "unknown credential" }
  let e1 ← append s 100 r1
  let e2 ← append s 101 { r1 with outcome := .success, detail := "" }
  let _ ← append s 102
    { event := .userAdded, outcome := .success, userName := some "bob", clientAddress := "cli" }
  checkEq "positions count from 1" (e1.seq, e2.seq) (1, 2)
  check "the first follows the genesis" (e1.prev == genesis)
  check "each follows the last" (e2.prev == e1.hash)
  checkEq "an intact chain verifies" (← verify s).toOption (some 3)
  checkEq "an empty chain verifies" (verifyChain []).toOption (some 0)
  let all := (← entries s).toList
  -- Change a field in the database.
  discard <| s.run fun c => Store.exec c "UPDATE audit SET outcome = ? WHERE seq = ?"
    #[.text "success", .int 1]
  check "a changed field breaks the chain at that entry"
    (match ← verify s with
     | .error e => e.startsWith "entry 1:"
     | .ok _ => false)
  -- Remove a record, reorder, forge.
  match all with
  | [a, b, c] =>
    check "a removed entry is found" (verifyChain [a, c] matches .error _)
    check "reordered entries are found" (verifyChain [b, a, c] matches .error _)
    let forged := { b with detail := "nothing to see" }
    check "a re-hashed entry no longer links to the next"
      (verifyChain [a, { forged with hash := forged.computeHash }, c] matches .error _)
    check "the untouched list verifies" (verifyChain [a, b, c] matches .ok 3)
  | _ => check "three entries were read back" false

/-- Concurrent appends do not fork the chain. -/
def concurrencyTests : IO Unit := withCtx fun ctx _ => do
  group "audit: concurrent appends"
  let tasks ← (List.range 16).mapM fun i => IO.asTask do
    discard <| append ctx.store i
      { event := .signIn, outcome := .failure, clientAddress := s!"10.0.0.{i}" }
  for t in tasks do discard <| IO.wait t
  checkEq "sixteen appends make one chain of sixteen" (← verify ctx.store).toOption (some 16)

/-- The audit log. -/
def auditTests : IO Unit := do
  encodingTests
  chainTests
  concurrencyTests

end PyleTests