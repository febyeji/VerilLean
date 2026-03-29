-- Common utility functions.

namespace VerilLean.Lib

-- Convert an option to a singleton or empty list.
def o2l : Option α → List α
  | some a => [a]
  | none => []

-- Cons an optional element onto a list.
def ocons : Option α → List α → List α
  | some a, l => a :: l
  | none, l => l

end VerilLean.Lib
