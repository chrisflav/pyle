import LeanBiscuit

/-!
# Verifying a pyle access token

The access tokens pyle issues are biscuits (DESIGN.md §5.2), and a service
verifies one offline, against pyle's root public key, without calling back.
This module is what such a service needs and nothing more: it depends only on
`lean-biscuit`, so a service written in Lean can copy it as it is.

A pyle token's authority block states who the user is and how they signed in,
and carries two checks of its own:

```
user("alice");
amr("hwk"); amr("user");
auth_time(2026-10-25T10:00:00Z);
group("admin");
client("taxis");
scope("openid"); scope("groups");
check if time($t), $t < 2026-10-25T11:00:00Z;
check if audience($a), {"pyle", "taxis"}.contains($a);
```

`verify` supplies the `time` and `audience` facts those checks look for, adds
the service's own policy (by default, any token naming a user is allowed), and
runs lean-biscuit's authorizer, which also enforces every check a holder added
when attenuating the token.  Only then does it read the identity, and only from
the authority block: a fact a later block states — `user("root")` appended by
whoever holds the token — is not believed, because only the authority block is
signed by pyle's root key.

pyle rotates its root key and announces the next one before it signs with it
(`GET /biscuit/keys`), so a service is given every key that is published and
the token is accepted under any of them.
-/

namespace Pyle
namespace Token

open LeanBiscuit LeanBiscuit.Token

/-- Who a verified token speaks for, read from its authority block. -/
structure Identity where
  /-- The user's name. -/
  user : String
  /-- The authentication methods of the sign-in (RFC 8176). -/
  amr : List String
  /-- The user's groups. -/
  groups : List String
  /-- The OAuth client the token was issued to. -/
  client : Option String
  /-- When the user authenticated, in seconds since the Unix epoch. -/
  authTime : Option Nat
  /-- The OAuth scopes the token was granted. -/
  scopes : List String := []
  deriving Repr, BEq, Inhabited

/-- The strings of the facts `name("…")` in a block, read through the token's
symbol table. -/
def stringFacts (symbols : Datalog.SymbolTable) (b : Block) (name : String) : List String :=
  b.facts.filterMap fun f =>
    if symbols.get? f.predicate.name == some name then
      match f.predicate.terms with
      | [.str i] => symbols.get? i
      | _ => none
    else none

/-- The date of the fact `name(<date>)` in a block, if there is one. -/
def dateFact (symbols : Datalog.SymbolTable) (b : Block) (name : String) : Option Nat :=
  b.facts.findSome? fun f =>
    if symbols.get? f.predicate.name == some name then
      match f.predicate.terms with
      | [.date d] => some d
      | _ => none
    else none

/-- The policy used when a service gives none: allow any token that names a
user, leaving the rest to the token's own checks. -/
def defaultPolicy : String := "allow if user($u);"

/-- Verify a pyle access token for `service` at `now` (seconds since the Unix
epoch), under any of the root keys `roots`, and authorize it with `policy` —
datalog with at least one `allow if` — evaluated with the facts
`time(<now>)` and `audience(<service>)`.  The identity the authority block
states, or why the token was refused. -/
def verify (roots : List PublicKey) (service : String) (now : Nat) (token : String)
    (policy : String := defaultPolicy) : Except String Identity := do
  let token := token.trimAscii.toString
  let some biscuit := roots.findSome? fun root => (Biscuit.ofBase64 token root).toOption
    | throw "the token does not verify under any of pyle's root keys"
  let request : AuthorizerBuilder :=
    { facts := [⟨⟨"time", [.date now]⟩⟩, ⟨⟨"audience", [.str service]⟩⟩] }
  let builder ← match request.code policy with
    | .ok b => pure b
    | .error e => throw s!"the policy is not datalog: {repr e}"
  match Authorizer.authorizeToken builder biscuit with
  | .ok _ => pure ()
  | .error _ => throw "the token is not authorized"
  let some authority := biscuit.blocks.head? | throw "the token has no authority block"
  let some user := (stringFacts biscuit.symbols authority "user").head?
    | throw "the token names no user"
  return { user, amr := stringFacts biscuit.symbols authority "amr",
           groups := stringFacts biscuit.symbols authority "group",
           client := (stringFacts biscuit.symbols authority "client").head?,
           authTime := dateFact biscuit.symbols authority "auth_time",
           scopes := stringFacts biscuit.symbols authority "scope" }

end Token
end Pyle