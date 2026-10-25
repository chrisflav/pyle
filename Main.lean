import Pyle

/-!
# The `pyle` command

The server and its administration commands.  Only `version` exists so far;
DESIGN.md §11 is the plan for the rest.
-/

def usage : String :=
  "usage: pyle <command>\n\n" ++
  "commands:\n" ++
  "  version    print the version"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["version"] =>
    IO.println "pyle 0.1.0"
    return 0
  | _ =>
    IO.eprintln usage
    return 2