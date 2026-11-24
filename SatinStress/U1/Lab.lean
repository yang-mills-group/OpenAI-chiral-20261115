import SatinStress.U1.Orbit
import SatinStress.U1.Pairs

/-!
# Labels, external tensors and enumeration for the finite class ranks near (93).

Inputs to the polynomial rank calculation; interpreted with the momentum/Polarization
variables in another file. Homogeneous calculation through weight 5 after the flavor/color
reduction. Orders/columns corresponding to `the construction notes` (shorter-prefix
first when comparing (i,S-tuple,L'-tuple)).
-/
namespace SatinStress.U1
open List

-- setup actual moments in Chart module
abbrev Sy := Duo Axis
abbrev G4 := Duo Blade -- GG (a≤b)
abbrev G5 := Blade × Blade × Axis -- GG, derivative on 2nd leg
abbrev F3 := Axis -- axial bilinear B (all PH)
abbrev F4 := Axis × (Axis ⊕ Axis) -- PH (L' or S) (orbit indices)`
abbrev F5 := Axis × (Sy ⊕ ((Axis × Axis) ⊕ Sy)) -- PH (LL, SL or SS)
abbrev X5 := Axis × Blade -- B_i[F_a]
abbrev VSy := Axis × Sy

instance : Fintype Blade := ⟨Blade.enumerate.toFinset, fun i =>
  List.mem_toFinset.mpr (Blade.mem_enumerate i)⟩

/-- Index label, permutation/sign action, finite ordered enumeration. -/
structure Schedule (α : Type) extends Slot α where
  en : List α
  all : ∀ a, a ∈ en
  key : α → ℕ

namespace Schedule
variable {α β : Type}
-- factor β assigned code < n for lex, if that's wanted (not needed as estimate premise).
def prod (S : Schedule α) (T : Schedule β) (n : ℕ) : Schedule (α × β) where
  toSlot := S.toSlot.prod T.toSlot
  en := S.en.flatMap fun a => T.en.map fun b => (a,b)
  all ab := List.mem_flatMap.mpr ⟨_, S.all ab.1, List.mem_map.mpr ⟨ab.2,T.all _,rfl⟩⟩
  key ab := S.key ab.1 * n + T.key ab.2

def twist (S : Schedule α) : Schedule α where
  toSlot := S.toSlot.twist
  en := S.en
  all := S.all
  key := S.key

def sum (S : Schedule α) (T : Schedule β) (shift : ℕ) : Schedule (α ⊕ β) where
  toSlot := S.toSlot.sum T.toSlot
  en := S.en.map Sum.inl ++ T.en.map Sum.inr
  all x := by cases x <;> simp [S.all,T.all]
  key := Sum.elim S.key (fun y => shift + T.key y)

def duo [LinearOrder α] (S : Schedule α) (n : ℕ) : Schedule (Duo α) where
  toSlot := Duo.slot S.toSlot
  en := Duo.enumerate S.en
  all := Duo.mem_enumerate S.all
  key a := S.key a.val.1 * n + S.key a.val.2

def vector : Schedule Axis := ⟨Slot.vector,axes,mem_axes,Fin.val⟩
def void : Schedule Empty := ⟨Slot.void,[],fun x => x.elim, fun _ => 0⟩
def unit : Schedule Unit := ⟨Slot.unit,[()],fun u => by cases u; simp, fun _ => 0⟩
def blade : Schedule Blade := ⟨Blade.slot,Blade.enumerate,Blade.mem_enumerate,Blade.key⟩
def TT : Schedule Sy := vector.duo 4
def W : Schedule Axis := vector
def V : Schedule VSy := vector.prod TT 16

def g4 : Schedule G4 := blade.duo 16
def g5 : Schedule G5 := blade.prod (blade.prod vector 4) 64
def f3 : Schedule F3 := vector.twist
/-- f4 expects order `(i, a, b) = (i, [], [j])` then `(i,[j],[])`
    inside each i, determinant exponent `1 + #L'` -/
def f4 : Schedule F4 := f3.prod (vector.twist.sum vector 4) 8

/-- Lex interleaving in supplementary file: LL first (in lex Sy order), then
    for each first S-index `i`, `(i, tail absent ; L j)` precedes `(i, S j ; no L)`. -/
def shear : Schedule ((Axis × Axis) ⊕ Sy) :=
  let D := (vector.prod vector.twist 4).sum TT 16
  let f : ((Axis × Axis) ⊕ Sy) → ℕ := Sum.elim (fun ij => ij.1.val*8 + ij.2.val)
    (fun x => x.val.1.val*8 + 4 + x.val.2.val)
  { D with
    key := f
    en := D.en.insertionSort (fun a b => f a ≤ f b)
    all := fun a => (List.mem_insertionSort _).mpr (D.all a) }

def f5 : Schedule F5 := f3.prod (((vector.twist).duo 4).sum shear 16) 48
def x5 : Schedule X5 := vector.prod blade 16 -- no extra determinants (T(Color) transpose)

/-- Key for any of our T,W,V rows bounded <64. `issuers` lists the representatives
in increasing order (lexicographic by the enumeration); emits no entries failing the
parity or stabilizer test. By `span_columns` we'll prove exhaustion. -/
def frame (M : Schedule α) (O : Schedule β) := M.prod O 64
def issuers [DecidableEq α] [DecidableEq β] (M : Schedule α) (O : Schedule β) :=
  let F := M.frame O
  F.toSlot.issuing F.en F.key
end Schedule
end SatinStress.U1
