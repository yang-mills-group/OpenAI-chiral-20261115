import YM.CF.Buffered.Place
import Anomaly.Contact
import Anomaly.Framing.ArcRent
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered
open Function Fock NormedSpace SU Lat Lattice Finset Cube Spire MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll Nacre
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree RG
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Sour Ione Ione.Clock Turning Hake Hive Levier Salt
variable {n:Side}

-- lift arbitrary even sector including noncreated. list proof
section
variable {N:Type*}[LinearOrder N][Fintype N]
inductive paritySale (b:Bool): FC N→Prop where
 | word(Z:List (Oboe N))(v:decide (¬Even Z.length)=b) : paritySale b (Hive.drum Z)
 | zero : paritySale b 0
 | plus {X Y : FC N}: paritySale b X → paritySale b Y → paritySale b (X+Y)
 | scale {X:FC N}(x:ℂ) : paritySale b X → paritySale b (x • X)
namespace paritySale
lemma times {a b:Bool}{X Y: FC N}(p:paritySale a X)(h:paritySale b Y): paritySale (a.xor b) (X*Y):=by
 induction p with
 | zero=> rw [zero_mul]; exact .zero
 | plus _ _ p q=> rw [add_mul]; exact .plus p q
 | scale z _ i=> rw [Algebra.smul_mul_assoc]; exact .scale z i
 | word Z v=>
   induction h with
   | word T u=>
     have p: Hive.drum Z*Hive.drum T=Hive.drum (Z++T):=by simp [Hive.drum]
     rw [p]; refine .word _ ?_; rw [←v, ←u]; by_cases p: Even Z.length <;> by_cases h: Even T.length<;>simp [List.length_append,Nat.even_add,p,h]
   | zero=> rw [mul_zero]; exact .zero
   | plus _ _ i j=>rw [mul_add]; exact .plus i j
   |scale z _ i=> rw [Algebra.mul_smul_comm]; exact .scale z i
lemma shops {b:Bool} (X:FC N) {S:Finset N} (h:Sector S b X): paritySale b X:= by
 induction h with
 |zero=>exact .zero
 |one=>exact .word [] (by simp)
 |up i g=>rw [show put i=drum [(true,i)] from (mul_one _).symm]; exact .word _ (by simp)
 |down i g=>rw [show takeF i=drum [(false,i)] from (mul_one _).symm]; exact .word _ (by simp)
 |add _ _ i j=>exact .plus i j
 |mul _ _ i j=>exact i.times j
 |scale _ z i=>exact .scale z i
lemma checked {X:FC N}{S:Finset N}(h:Sector S false X): Hive.Keys X:= by
 have he:=shops X h
 clear h; induction he with
 | word Z v=>exact Hive.Keys.roll _ (of_not_not (of_decide_eq_false v))
 | zero=>exact Hive.Keys.null
 | plus _ _ i j=> exact .plus i j
 | scale z _ i=> exact .col z i
end paritySale
end

variable (s:Sweep n) (S:Support (More n))(sx:s.charge=false)
local notation "T"=>actY s S
local notation "ΧΞ"=>γS s
-- retain the measurement's second Pane (motion uses same formula on both)
include sx
lemma Whirl_stay {u:Bool}{f:FC (Single n)} (p:Sector (modesIn n S) u f): Sector (modesIn n (actY s S)) u (Hive.teen s f):=by
 have h: twist ΧΞ (cutM (modesIn n S))=cutM (modesIn n T):=prep_moves _ _ S _ (fun i=>Finset.mem_map_equiv)
 let A:=ΧΞ; change Sector _ u (Urn.lotB s.charge (detX s.s) A f) -- charge not rewrite there
 rw [sx]; cases detX s.s; exact Heat.north_sector (modesIn n S) _ h p; exact theta_carries A p h

lemma whirl_fine {u:Bool}{f:FC (Single n)}(p : Fine (Tset n) (modesIn n S) u f) : Fine (Tset n) (modesIn n (actY s S)) u (Hive.teen s f) :=by
 let V:=spinU s.charge s.s; let A:= ΧΞ; have h: twist A (cutM (modesIn n S))=cutM (modesIn n T):=prep_moves _ _ S _ (fun i=>Finset.mem_map_equiv)
 have hp:sings s.charge A (cutM (Tset n))=swapX (detX s.s) (cutM (Tset n)):=tickR (castX s) (xtra s.charge) V (spinZ ..) n
 change Fine _ _ _ (Urn.lotB s.charge (detX s.s) A _); rw [sx] at hp ⊢; cases e:detX s.s <;> rw [e] at hp
 · change twist A (cutM (Tset n))=cutM (Tset n) at hp
   have hn: twist A (cutM (Tset n)ᶜ)=cutM (Tset n)ᶜ:=by rw [dim_cut,map_sub,map_one,hp]
   have he(x:Ket (Single n))(p q:Finset (Single n))(t:withinM p x)(d: twist A (cutM p)=cutM q):withinM q (acts A.val x):=by unfold withinM; rw [←d, ←Fock.swivel,t]
   change Fine _ _ _ (twist (quantU A) f)
   induction p with
   | empty=> rw [map_zero]; exact .empty _
   | one=> rw [map_one]; exact .one
   | seed i hi=>
      by_cases ht:i∈Tset n
      · rw [show (think _).term i=put i from if_pos ht,←create_put,twist_create]; exact fine_create _ (he _ _ _ (within_basis _ _ ht) hp) (he _ _ _ (within_basis _ _ hi) h)
      rw [show (think _).term i= -takeF i from if_neg ht,map_neg,← remove_take,twist_remove]
      exact fine_neg (fine_remove _ (he _ _ _ (within_basis _ _ (mem_compl.mpr ht)) hn) (he _ _ _ (within_basis _ _ hi) h))
   | add _ _ h k=> rw [map_add]; exact h.add k
   | grow _ _ h k=> rw [map_mul]; exact h.grow k
   | scale _ _ h=> rw [twist_scalar]; exact h.scale _
 exact p.arrive h (by change twist A (cutM (Tset n))=1-cutM (Tset n) at hp; rw [dim_cut, map_sub,map_one,hp,sub_sub_cancel]) -- tune
omit sx
end YM.CF.Buffered
