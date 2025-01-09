import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64
import «AoC».Vec2

namespace Y2024.Day10
open Accumulation CiCL TwoDimensionalVector64 Rect Vec2 Std

structure Input where
  mapping : Rect Nat
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.mapping}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line : Parser (Array Nat) :=
  (·.map (·.toNat - '0'.toNat)) <$> many1 digit

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
      let v ← sepBy1 parse_line eol
      return Input.mk (Rect.of2DMatrix v)

end parser

namespace Part1

partial def expand
    (rect : Rect Nat)
    (visited : Rect Bool)
    (toVisit : List Dim2)
    (result : HashSet Dim2 := HashSet.empty)
    : Nat :=
  match toVisit with
  | [] => result.size
  | node :: remain =>
    if rect.get node.1 node.2 0 == 9 then expand rect visited remain (result.insert node)
      else
        let currentLevel := rect.get node.1 node.2 0
        let toVisit' := [((-1, 0) : Vec2), (1, 0), (0, -1), (0, 1)]
            |>.filterMap (fun offset ↦ rect.toIndex₂ (node.toInt64 + offset))
            |>.filter (fun p ↦ currentLevel + 1 == rect.get p.1 p.2 0)
            |>.filter (fun p ↦ !visited.get p.1 p.2 false)
        let visited' := toVisit'.foldl (fun acc p ↦ acc.set p.1 p.2 true) visited
      expand rect visited' (toVisit' ++ remain) result

def solve (input : Input) : Nat :=
  input.mapping.enum
    |>.map (fun (p, lvl) ↦ if lvl == 0 then expand input.mapping (input.mapping.map (fun _ ↦ false)) [p] else 0)
    |> sum

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 10
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2024.Day10
