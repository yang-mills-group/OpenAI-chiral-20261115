import Gingham.Ruff.Verandah

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


open Buffered
open Reed (Fine think)
set_option synthInstance.maxSize 16000

structure Footlight (N:Side) where
  plot:Support (More N)
  physical: FC (Single N)
  primed: FC (Single N)
  presented : Sector (modesIn N plot) false physical
  loaded : Sector (modesIn N plot) false primed
  handoff(x:Phys N):beamZ N (acts physical x)=beamZ N (acts primed x)
namespace Footlight

def scale(A:Footlight N)(z:ℂ):Footlight N:= ⟨A.plot,z • A.physical,z • A.primed,
 A.presented.scale _, A.loaded.scale _,fun x=>by
 have v:=A.handoff x
 rw [act_smul,act_smul];unfold beamZ at *
 rw [inner_smul_right,inner_smul_right,v]⟩
def extra(S:Support (More N)) (A:FC (Single N))
 (h:Sector (modesIn N S) false A):Footlight N:=⟨S,A,A,h,h,fun _=>rfl⟩
def Space (A B:Footlight N):=Disjoint A.plot B.plot
def libretto(f:Footlight N→FC (Single N))(l: List (Footlight N)):= (l.map f).prod
lemma abridge(A:Footlight N)(l:List (Footlight N))(f:Footlight N→FC (Single N))
 (h:∀x∈l, Commute A.primed (f x)):Commute A.primed (libretto f l):=by
 induction l with
 | nil=> exact Commute.one_right ..
 | cons x xs ih=> exact
    (h x List.mem_cons_self).mul_right (ih (fun _ y=>h _ (List.mem_cons_of_mem _ y)))

lemma shift(A D:Footlight N)(s:Space A D):
 Commute A.primed D.physical ∧ Commute A.primed D.primed:=by
 have h:Disjoint (modesIn N A.plot) (modesIn N D.plot):=
   Finset.disjoint_left.mpr fun i a b=> Finset.disjoint_left.mp s
     ((modes_at ..).mp a) ((modes_at ..).mp b)
 constructor
 · exact (A.loaded.apart D.presented h).trans (one_smul ..)
 exact (A.loaded.apart D.loaded h).trans (one_smul ..)
theorem onstage (l:List (Footlight N))(h:l.Pairwise Space)(x:Phys N):
 beamZ _ (acts (libretto physical l) x)=beamZ _ (acts (libretto primed l) x):=by
 induction l generalizing x with
 | nil=> rfl
 | cons A l ih=>
    change beamZ _ (acts (A.physical*libretto physical l) x)=
     beamZ _ (acts (A.primed*libretto primed l) x)
    obtain ⟨v,w⟩:= List.pairwise_cons.mp h
    rw [act_mul,A.handoff,←act_mul,
       (abridge A l _ (fun t s=> (shift _ _ (v t s)).1)).eq,
       (abridge A l _ (fun t s=> (shift _ _ (v t s)).2)).eq,
       act_mul,act_mul,ih w]

end Footlight

namespace GarlandBook

variable {p:BudgetPoint}{u:Side}{r l:ℕ}{E a c e:ℝ}
    {U':Scree.Loom N}{f h:Chin N→OP N}
    (B:GarlandBook u a c e f h)(g:Briefly p r e U')
    (G:Tagbill a E u l r p.B)
    (d:Shape)(U:UNI SpinIdx)
    (T:Plumes f h a c e)(j:JetS d.s false (detX d.s) U)


def actor(x:Orbit N):Footlight N := ⟨Pall p d N,B.pen g d U x, B.villa g d U x,
  (B.Lawn g G d U x).1,(B.Lawn g G d U x).2, B.cavity g d U x⟩
def signedActor (word:List (Axis×ℤ))(x:Orbit N):=
 Footlight.scale (B.actor g G (maidS word) (maidU word) x)
    (effect (maidS word) 1)
lemma crew_1(word:List (Axis×ℤ))(x:Orbit N)(v:Pane N):
  (B.signedActor g G word x).physical=maiden word (B.brim g) (x.1,v):=by
 rw [heraldry B g G _ _ x rfl]
 change effect _ _ • (B.pen _ _ _ _)=_
 unfold effect ribbonSign
 split <;> simp

#print axioms Footlight.onstage
#print axioms crew_1

