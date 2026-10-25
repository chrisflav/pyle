import Lean.Data.Json

/-!
# Client data

`clientDataJSON` is written by the browser, not the authenticator, and it is
the browser's testimony about the ceremony: what kind it was, which challenge
the page passed in, and the origin of the page that asked (WebAuthn §5.8.1).
The authenticator signs its hash, so the testimony cannot be altered after the
fact; the relying party's job is to read it and check that it describes the
ceremony it started.

The members WebAuthn defines are read with `Lean.Json`; anything else (such as
the `extraData` the W3C test vectors add, or members a future browser adds) is
ignored, as §5.8.1 requires.  `type`, `challenge` and `origin` must be strings,
and `crossOrigin` and `topOrigin`, when present, a boolean and a string.
-/

namespace Pyle
namespace WebAuthn

open Lean

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
  /-- Whether a ceremony may run in a frame of another origin.  pyle does not
  allow framing (DESIGN §7), so this is off unless a deployment says
  otherwise. -/
  allowCrossOrigin : Bool := false

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

/-- A string member, which must be present. -/
def stringMember (j : Json) (name : String) : Except String String :=
  match j.getObjVal? name with
  | .ok (.str s) => .ok s
  | .ok _ => .error s!"client data: {name} is not a string"
  | .error _ => .error s!"client data: {name} is missing"

/-- Parse `clientDataJSON`. -/
def ClientData.parse (bytes : ByteArray) : Except String ClientData := do
  let some text := String.fromUTF8? bytes | throw "client data: not UTF-8"
  let j ← (Json.parse text).mapError fun e => s!"client data: {e}"
  let .obj _ := j | throw "client data: not an object"
  let type ← stringMember j "type"
  let challenge ← stringMember j "challenge"
  let origin ← stringMember j "origin"
  let crossOrigin ← match j.getObjVal? "crossOrigin" with
    | .ok (.bool b) => pure (some b)
    | .ok _ => throw "client data: crossOrigin is not a boolean"
    | .error _ => pure none
  let topOrigin ← match j.getObjVal? "topOrigin" with
    | .ok (.str s) => pure (some s)
    | .ok _ => throw "client data: topOrigin is not a string"
    | .error _ => pure none
  pure { type, challenge, origin, crossOrigin, topOrigin }

end WebAuthn
end Pyle