import GaugeFieldConstruction.RankClasses
/-!
# RankSupplement receipt continued — strict lex conventions & normalized orbit columns.

 Proving exact pivots on the table of *chart readings* (as complex-valued functions).
 Not modeling the Python arithmetic. The certificate in GRank, FRank, XRank works in
 injective coordinates, with proportional columns. Provide the literal dictionary.
 Use normalized sign-flip/permutation columns as in U1, S² components still encoded
 canonically (`ordered i j`, read the full array by repeating these entries).
-/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.U1.TableDictionary
open Finset Function Raw Cauchy Row Record Certificate Vouchers
open scoped BigOperators
variable {M O Z : Type*}
-- Encode Lex. Axis numbers >0 (append 0 to FINISH a variable-length tuple).
-- Concatenate fixed-length tuples. Each code is of fixed length within a class.
def axisN (i : Axis) := i.val+1
def axisCode (i : Axis) := [axisN i]
def symCode (x : Raw.Sym) := [axisN x.val.1,axisN x.val.2]
def wedgeCode (x : Raw.Wed) := [axisN x.toBlade.val.1,axisN x.toBlade.val.2]
def vsCode (x : Raw.VS) := axisN x.1::symCode x.2

def g4 (a : G4) := wedgeCode a.val.1++wedgeCode a.val.2
def g5 (a : G5) := wedgeCode a.1++wedgeCode a.2.1++axisCode a.2.2
def f4 (a : F4) := axisCode a.1 ++ a.2.elim (fun i=>[0,axisN i,0]) (fun i=>[axisN i,0,0])
def f5 (a : F5) := axisCode a.1 ++ a.2.elim (fun i=>[0]++symCode i++[0])
   (Sum.elim (fun i=>symCode i++[0,0]) (fun z=>[axisN z.1, 0, axisN z.2, 0]))
def x5 (a : X5) := axisCode a.1++wedgeCode a.2

def Lexion (A : Labels M) (r : List M) (code : M → List ℕ) : Prop :=
   r.Pairwise (fun a b=> code a < code b) ∧ ∀i∈r, ∀ p:Equiv.Perm Axis, A.move (unsigned p) i≠i → code i < code (A.move (unsigned p) i)
def lexCheck [DecidableEq M] (A : Labels M) (r : List M) (code : M → List ℕ) :=
   decide (r.Pairwise (fun a b=> code a < code b)) && r.all (fun i=> perm4.all fun p=> let j:=A.move (unsigned p) i; decide (j=i) || decide (code i < code j))
lemma receipt [DecidableEq M] (A : Labels M) (r : List M) (code) (p : lexCheck A r code=true) : Lexion A r code := by
 rw [lexCheck,Bool.and_eq_true,decide_eq_true_eq] at p
 refine ⟨p.1,fun i hi j J=>?_⟩
 simpa [J] using List.all_eq_true.mp (List.all_eq_true.mp p.2 i hi) j (mem_perm j)

abbrev ColumnOrder (A:Labels M) (B:Labels O) (x : List (M×O)) (m : M→List ℕ) (b : O→List ℕ) := Lexion (A.tensorProd B) x (fun i=>m i.1 ++ b i.2)

set_option maxHeartbeats 3000000
set_option maxRecDepth 120000
set_option synthInstance.maxSize 6500
lemma printedTg : ColumnOrder g4Act symAct g4T g4 symCode:= receipt _ _ _ (by decide +kernel)
lemma printedWg : ColumnOrder g5Act v g5W g5 axisCode:= receipt _ _ _ (by decide +kernel)
lemma printedVg : ColumnOrder g5Act vsAct g5V g5 vsCode:= receipt _ _ _ (by decide +kernel)
lemma printedTf : ColumnOrder f4Act symAct f4T f4 symCode:= receipt _ _ _ (by decide +kernel)
lemma printedWf : ColumnOrder f5Act v f5W f5 axisCode:= receipt _ _ _ (by decide +kernel)
lemma printedVf : ColumnOrder f5Act vsAct f5V f5 vsCode:= receipt _ _ _ (by decide +kernel)
lemma printedWx : ColumnOrder x5Act v x5W x5 axisCode:= receipt _ _ _ (by decide +kernel)
lemma printedVx : ColumnOrder x5Act vsAct x5V x5 vsCode:= receipt _ _ _ (by decide +kernel)
#print axioms printedVf
#print axioms printedVg
end YM.GaugeFieldConstruction.U1.TableDictionary
