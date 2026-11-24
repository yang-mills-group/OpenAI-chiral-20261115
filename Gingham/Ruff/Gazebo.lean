import Gingham.Ruff.Terrace
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

open RG Vow Hake Tenant
set_option linter.unusedSimpArgs false

open Sour Rill
attribute [local instance] Rill.boreKSpace Rill.boreXN Sour.loreM Sour.loreN
open scoped Classical

open Nacre


namespace GarlandBook

variable {p:BudgetPoint}{u:Side}{r l:ℕ}{E a c e:ℝ}
    {U':Scree.Loom N}{f h:Chin N→OP N}
    (B:GarlandBook u a c e f h)(g:Briefly p r e U')
    (G:Tagbill a E u l r p.B)
    (d:Shape)(U:UNI SpinIdx)
    (T:Plumes f h a c e)(j:JetS d.s false (detX d.s) U)

lemma surplus_split(M V:Axis → Cover→OP N):
 surplus (N:=N) u (fun i w=>M i w+V i w) = surplus u M+surplus u V:=by
 unfold surplus; rw [←sum_add_distrib];exact sum_congr rfl fun _ _=>by dsimp only; exact add_sub_add_comm _ _ _ _

include T j
lemma plumeEq(x:Orbit N):
   let y:=finale d 0
   let S:=f (profile (U' x))
   let H:=h (profile (U' x))
   let W:=block u y
   let L:=𝒪 S H W
   let A:=baldaquin d U f u e (g.roll x)
   A=B.trim g d U true x+B.trim g d U false x+B.trussEnd g d U x ∧
   L=B.fill g d U true x+B.fill g d U false x+B.fillEnd g d U x∧
   tackfee d A L=𝒜 S (tickA N) W:=by
   intro y S H W L A
   refine ⟨splitF g (B.standard d U) x,?_,?_⟩
   · rw [show L=upshot d U f h u e (g.roll x) from
       (poise_J d U (g.dye x) u T j).symm, upshot,fill,fill,fillEnd,
       ←surplus_split,←surplus_split]
     exact congrArg (surplus u) (funext (fun i=> funext fun w=> splitF g
       (B.streamer d U i w) x))
   rw [tackfee,ditch,show Matrix.trace L=0 from
     𝒪_trace (T.pure _ (g.dye x).live) ..]
   rw [neg_zero,ite_self,add_zero]
   exact poise_A d U (g.dye x) u T j

omit j T

def weight(Z:OP N)(V:OP N):FC (Single N):=
  tackfee d Z V • 1 + dg V

/-- Exp tail insertion. -/
def quarry(x:Orbit N):= weight d (B.trussEnd g d U x) (B.fillEnd g d U x)
/-- Flag insertion. -/
def alarm(x:Orbit N):= weight d (B.trim g d U false x) (B.fill g d U false x)
abbrev hitchAt(N:Side)(u:Side)(d:Shape):= block (N:=N) u (finale d 0)
/-- Raw (125)-version of lookup. No mask required on block W. -/
def villa(x:Orbit N):= facade (tickA N) (hitchAt N u d)
  (B.thread g d U x) (B.fill g d U true x)

lemma cavity (x:Orbit N)(w: Wave (Single N)):
 inner ℂ (mateK N) (acts (B.pen g d U x) w)=inner ℂ (mateK N) (acts (B.villa g d U x) w):=
  facade_reads (tickPin N) (tickB N) (hitchAt N u d) (block_comm ..) _ _ _

include T j
lemma villa_split (x:Orbit N):
 B.villa g d U x=𝒵 (f (profile (U' x))) (h (profile (U' x))) (hitchAt N u d) -
    B.alarm g d U x - B.quarry g d U x:=by
 let D := tickA N
 let W:= hitchAt N u d
 rw [←facade_eq _ _ _ D,villa,thread,facade,facade]
 obtain ⟨a,m,l⟩:=B.plumeEq g d U T j x
 unfold alarm quarry weight
 rw [←l,a,m,tack_add,tack_add,add_smul,add_smul,dg_add,dg_add]
 dsimp only [D]
 abel

#print axioms villa_split

