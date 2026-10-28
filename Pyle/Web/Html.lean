import Pyle.Http.Message

/-!
# HTML

pyle's pages are a few hundred lines of plain HTML written here, with no
template engine: every value that did not come from this file goes through
`escape`, and there is no other way to put text into a page.

Every page has the same frame (`page`): the stylesheet and the script from
`/assets/`, which is all the Content Security Policy allows (`script-src
'self'`, `style-src 'self'`, no inline either), and a status line that a
screen reader announces.  What the script needs to know about the page — which
page it is, where to go afterwards — travels in `data-` attributes on `body`,
escaped like everything else.
-/

namespace Pyle
namespace Web

open Http

/-- Escape text for an HTML element or a quoted attribute value. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
    | '\'' => acc ++ "&#39;"
    | c => acc.push c

/-- An HTML reply. -/
def htmlReply (body : String) (status : Std.Http.Status := .ok) : Reply :=
  { status, body := body.toUTF8, contentType := "text/html; charset=utf-8" }

/-- A complete page: `page` names it for the script, `attrs` are further
`data-` attributes (without the prefix), and `content` is the inside of
`main`, already HTML.  `back`, if given, is a link above the heading: its
address and its text.  `aside`, if not empty, is HTML set beside the heading,
on the right.  `scripts` are further scripts of this origin, loaded after
`/assets/pyle.js`, whose functions they may use. -/
def page (pageName title : String) (attrs : List (String × String)) (content : String)
    (back : Option (String × String) := none) (aside : String := "")
    (scripts : List String := []) : String :=
  let heading := if aside.isEmpty then s!"<h1>{escape title}</h1>\n" else
    s!"<div class=\"page-head\">\n<h1>{escape title}</h1>\n{aside}\n</div>\n"
  let data := attrs.foldl (init := "") fun acc (k, v) => acc ++ s!" data-{k}=\"{escape v}\""
  let backLink := match back with
    | some (href, text) => s!"<a class=\"back\" href=\"{escape href}\">← {escape text}</a>\n"
    | none => ""
  "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" ++
  s!"<title>{escape title} · pyle</title>\n" ++
  "<link rel=\"stylesheet\" href=\"/assets/pyle.css\">\n" ++
  "<script src=\"/assets/pyle.js\" defer></script>\n" ++
  String.join (scripts.map fun s => s!"<script src=\"{escape s}\" defer></script>\n") ++
  "</head>\n" ++
  s!"<body data-page=\"{escape pageName}\"{data}>\n<main>\n{backLink}{heading}" ++
  content ++
  "\n<p id=\"status\" role=\"status\" aria-live=\"polite\"></p>\n</main>\n</body>\n</html>"

/-- A page that only says something, such as an error. -/
def messagePage (title message : String) (status : Std.Http.Status) : Reply :=
  htmlReply (page "message" title [] s!"<p>{escape message}</p>") status

/-- The date of a day number since the Unix epoch, as (year, month, day): the
proleptic Gregorian calendar, by Howard Hinnant's `civil_from_days`. -/
def civilFromDays (days : Nat) : Nat × Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400
  (if m ≤ 2 then y + 1 else y, m, d)

/-- Two digits. -/
def pad2 (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

/-- The English abbreviation of a month, 1 to 12. -/
def monthName (m : Nat) : String :=
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"].getD
    (m - 1) "?"

/-- The day of a Unix time, as `26 Oct 2026`. -/
def formatDate (t : Nat) : String :=
  let (y, m, d) := civilFromDays (t / 86400)
  s!"{d} {monthName m} {y}"

/-- A Unix time, as `26 Oct 2026, 20:41 UTC`. -/
def formatTime (t : Nat) : String :=
  let s := t % 86400
  s!"{formatDate t}, {pad2 (s / 3600)}:{pad2 (s % 3600 / 60)} UTC"

end Web
end Pyle