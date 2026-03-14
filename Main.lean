import LR1Generator
import eBNFparser

def main (args : List String) : IO Unit :=
  match args with
  | [] => IO.println "There is no arguments"
  | _ => for arg in args do
          IO.println s!"引数: {arg}"
