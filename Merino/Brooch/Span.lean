import Merino.Brooch.Tour
import YM.CF.Roots.Hat

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Brooch
open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier
variable {N:Side}
local notation "Jk"=> Single N

open Dial Vow
open BProof RG Salt Roots


def inReach(p:BudgetPoint)(o:Site N)(s:Sweep N)(y:Spool N):Prop:=separation (node o) (boxA s y.post) ≤ p.B
def sleeve(p:BudgetPoint)(o:Site N):Support (More N):= purse (4*p.B) (node o)
lemma touches (y:Spool N)(p:BudgetPoint)(a:24*y.stepY≤p.B)(b:12≤p.B)
 {s:Sweep N}{o:Site N}(h:inReach p o s y):lashes s y p⊆sleeve p o:=by
 intro i v
 obtain ⟨j,r,rfl⟩:=mem_map.mp v
 obtain ⟨x,t,q⟩:=halo_spec.mp r
 rw [mem_singleton.mp t] at q
 refine halo_spec.mpr ⟨node o,mem_singleton_self _,?_⟩
 refine (separation_triangle _ (boxA s y.post) _).trans ?_
 rw [show (((boxA s⁻¹).symm.toEmbedding) j)= boxA s j from ?_, sitT]
 unfold inReach at h
 omega
 rw [sitU];rfl

def bra (A B:FC Jk):Prop:= acts (star A) (mateK N)=acts (star B) (mateK N)

variable {I:Type}(o:I→Site N)(l:List I)(X Y:I→FC (Single N))
lemma CommPair (p:BudgetPoint)(b:12≤p.B)(g:Apex (cape_B p.B) p.B (node∘o))
 {i j : I}{A B:FC Jk}
 (u:Fock.Sector (modes (sleeve p (o i))) false A)
 (v:Fock.Sector (modes (sleeve p (o j))) false B)
 (t:node (o i) ≠ node (o j)):Commute A B:=by
 apply Spool.Hem.commute_apart u v
 refine Finset.disjoint_left.mpr fun k a c=>?_
 obtain ⟨x,r,h⟩:=halo_spec.mp ((mem_modes ..).mp a)
 obtain ⟨y,q,s⟩:=halo_spec.mp ((mem_modes ..).mp c)
 rw [mem_singleton.mp r] at h
 rw [mem_singleton.mp q,separation_comm] at s
 have e:= g i j t
 simp only [cape_B,Function.comp_apply] at e
 have f:=separation_triangle _ _ _ |>.trans (Nat.add_le_add h s)
 have:4*p.B ≤ p.B^3:=by rw [pow_succ]; gcongr; nlinarith
 omega


def Pulse(p:BudgetPoint)(o:I→Site N)(Y:I→FC Jk):Prop:=∀ i,Fock.Sector (modes (sleeve p (o i))) false (Y i)
variable (p:BudgetPoint)(b:12≤p.B)(g:Apex (cape_B p.B) p.B (node∘o))
    (u:Pulse p o X)(v:Pulse p o Y)(w:∀i,bra (X i) (Y i))

/-- pass through arbitrary spectator (on right) -/
lemma glue {A B:FC Jk}(h:bra A B)(C:FC Jk):bra (A*C) (B*C):=by
 unfold bra at *
 rw [star_mul,star_mul,act_mul,act_mul,h]

def spare(o:I→Site N)(l:List I):Prop:=l.Pairwise (fun i j=> node (o i) ≠ node (o j))
include b g u
lemma sparks (t:spare o l):l.Pairwise (fun i j=>Commute (X i) (X j)):=List.Pairwise.imp (fun {_k _n} => CommPair o p b g (u _k) (u _n)) t
include v w
lemma cut (t:spare o l):bra (l.map X).prod (l.map Y).prod:=by
 induction l with
 | nil=> simp [bra]
 | cons i l ih=>
    obtain ⟨d,r⟩:= List.pairwise_cons.mp t
    have h:Commute (Y i) (l.map X).prod:= Commute.list_prod_right _ _ fun x a=> by
       obtain ⟨j,c,rfl⟩:=List.mem_map.mp a; exact CommPair o p b g (v i) (u j) (d j c)
    have k:Commute (Y i) (l.map Y).prod:= Commute.list_prod_right _ _ fun x a=> by
       obtain ⟨j,c,rfl⟩:=List.mem_map.mp a; exact CommPair o p b g (v i) (v j) (d j c)
    simp only [List.map_cons,List.prod_cons]
    show _=_
    rw [show _=_ from glue (w i) (l.map X).prod,h.eq,k.eq]
    exact glue (ih r) _

end YM.CF.Merino.Brooch
