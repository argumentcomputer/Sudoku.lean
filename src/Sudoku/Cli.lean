import Sudoku

open Sudoku System IO

def main (args : List String) : IO UInt32 := do
  try
    let files := args.map FilePath.mk
    let srcs ← files.mapM (λ fp => do (fp, ←IO.FS.readFile fp))

    for (fp, src) in srcs do
      println! "Parsing board {fp}"
      match Board.parseText src 3 3 with
      | Except.ok board => do
        println! "{board}"
      | Except.error e => IO.eprintln s!"Error: {e}"
    pure 0
  catch e =>
    IO.eprintln <| "Error: " ++ toString e -- avoid "uncaught exception: ..."
    pure 1

