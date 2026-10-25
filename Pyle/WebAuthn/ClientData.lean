import Pyle.Encoding.Json

/-!
# Client data

`clientDataJSON` is written by the browser, not the authenticator, and it is
the browser's testimony about the ceremony: what kind it was, which challenge
the page passed in, and the origin of the page that asked (WebAuthn §5.8.1).
The authenticator signs its hash, so the testimony cannot be altered after the
fact; the relying party's job is to read it and check that it describes the
ceremony it started.

The members WebAuthn defines are read with the strict reader of
`Pyle.Encoding.Json`, not `Lean.Json`, because these bytes arrive before any
signature over them is checked and `Lean.Json` evaluates numbers of any size.
Anything else (such as the `extraData` the W3C test vectors add, or members a
future browser adds) is ignored, as §5.8.1 requires.  `type`, `challenge` and
`origin` must be strings, and `crossOrigin` and `topOrigin`, when present, a
boolean and a string.
-/

namespace Pyle
namespace WebAuthn

open Pyle.Encoding

/-- The relying party: this deployment, as WebAuthn sees it. -/
structure RelyingParty where
  /-- The relying party id, a registrable domain such as `auth.example.org`;
  authenticators scope credentials to it. -/
  id : String
  /-- The exact origins pages may run ceremonies from, such as
  `https://auth.example.org`. -/
  origins : List String
  /-- Whether every ceremony must verify the user, not only see them. -/
  requireUserVerification : Bool := true
  /-- The top-level origins that may frame a ceremony.  pyle does not allow
  framing (DESIGN §7), so this is empty unless a deployment says otherwise; a
  ceremony from a frame is accepted only if the browser names its top-level
  origin and that origin is listed here. -/
  allowedTopOrigins : List String := []

/-- The members of `clientDataJSON` a relying party checks. -/
structure ClientData where
  /-- `"webauthn.create"` or `"webauthn.get"`. -/
  type : String
  /-- The challenge, base64url encoded. -/
  challenge : String
  /-- The origin of the page that ran the ceremony. -/
  origin : String
  /-- Whether the page was in a frame of a different origin, if the browser
  said. -/
  crossOrigin : Option Bool
  /-- The origin of the top-level page, sent only from a cross-origin
  frame. -/
  topOrigin : Option String
  deriving Repr

/-- A member's value, if the member is present.  The reader has already
refused repeated keys, so there is at most one. -/
def member (members : List (String × Json.Value)) (name : String) : Option Json.Value :=
  (members.find? (·.1 == name)).map (·.2)

/-- A string member, which must be present. -/
def stringMember (members : List (String × Json.Value)) (name : String) :
    Except String String :=
  match member members name with
  | some (.str s) => .ok s
  | some _ => .error s!"client data: {name} is not a string"
  | none => .error s!"client data: {name} is missing"

/-- Parse `clientDataJSON`. -/
def ClientData.parse (bytes : ByteArray) : Except String ClientData := do
  let members ← (Json.readObject bytes).mapError fun e => s!"client data: {e}"
  let type ← stringMember members "type"
  let challenge ← stringMember members "challenge"
  let origin ← stringMember members "origin"
  let crossOrigin ← match member members "crossOrigin" with
    | some (.bool b) => pure (some b)
    | some _ => throw "client data: crossOrigin is not a boolean"
    | none => pure none
  let topOrigin ← match member members "topOrigin" with
    | some (.str s) => pure (some s)
    | some _ => throw "client data: topOrigin is not a string"
    | none => pure none
  pure { type, challenge, origin, crossOrigin, topOrigin }

end WebAuthn
end Pyle