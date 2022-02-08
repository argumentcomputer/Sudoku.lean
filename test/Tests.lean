import Sudoku

open System
open Sudoku
open Sudoku.Board

def main (args : List String) : IO UInt32 := do
  try
    let board : Board ← parseFile <| FilePath.mk "board1.txt"
    println! "Board 1:\n{board}"
    match board.isValid? with
    | Except.ok () => println! "board is valid"
    | Except.error e => println! "board not valid: {e}"
    pure 0
  catch e =>
    IO.eprintln <| "error: " ++ toString e -- avoid "uncaught exception: ..."
    pure 1

