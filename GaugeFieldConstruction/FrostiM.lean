import GaugeFieldConstruction.Polenta
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
variable {I α F E:Type}[Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
lemma c_eq (i k:List I)(p:i.Perm k)(x:Key I):carR x i=carR x k:= List.Perm.prod_eq (p.map x)
section
variable (s T:List I)(M:E)
local notation "X" i:max => arc0 i M
private lemma launch (f:List I)(x:Key I)(e:x∈hill I):lance (fun _=> (0:E)) f x=0:=by
 induction f with
 | nil=> rfl
 | cons i f ih=>
    have hx:Set.EqOn (cutI (fun _=>(0:E)) i) (fun _=>0) (hill I):= fun z v=>(mitt (zeroR _) v i).deriv.symm.trans (deriv_const ..)
    exact (lace_C f hx e).trans ih
private lemma levers (x:Key I)(i:I)(j:ℂ)(h:i∉s): carR (update x i j) s=carR x s:=by
 induction s with
 | nil=> rfl
 | cons k l ih=> change update x i j k * carR (update x i j) l= _; rw [update_of_ne (fun (v:k=i)=>h (by simp [v])),ih (fun t=> h (by simp[t]))]; rfl
lemma sparks (i:I)(x:Key I)(e:x∈hill I): cutI (fun z=>carR z s • M) i x= if s.count i=1 then carR x (s.erase i) • M else 0:=by
 let H:= X s
 by_cases v:i∈s
 · have g(j:ℂ):carR (update x i j) s=j*carR (update x i j) (s.erase i):=by
       rw[c_eq s _ (List.perm_cons_erase v)]; change update x i j i*carR _ (s.erase i)= _; rw[update_self]
   have t:= mitt (X (s.erase i)) e i
   have ht:= (hasDerivAt_id' (0:ℂ)).smul t
   have p : (fun w:ℂ=>carR (update x i w) s • M)=(fun w=> w • (carR (update x i w) (s.erase i) • M)):=by funext w; rw [g,smul_smul]
   have hu: cutI (fun z=>carR z s • M) i x= carR (update x i 0) (s.erase i) • M:=by
      rw [←(mitt H e i).deriv,show (fun w=>_)=_ from p]; have z:=ht.deriv; change deriv (fun w:ℂ=> w • (carR (update x i w) (s.erase i) • M)) _ = _ at z; simpa using z
   rw [hu]; split
   next h=> rw[levers (s.erase i) _ _ _ (List.count_eq_zero.mp (by rw[List.count_erase_self,h]))]
   next h=>
    have hz:i∈s.erase i :=List.count_pos_iff.mp ?_ -- tune
    · rw [show carR (update x i 0) (s.erase i)=0 from List.prod_eq_zero (List.mem_map.mpr ⟨i,hz,update_self ..⟩),zero_smul]
    rw [List.count_erase_self]; have hz:=List.count_pos_iff.mpr v; omega
 have g:(fun w=>carR (update x i w) s • M)=fun _=> carR x s • M:= funext fun w=> by rw [levers _ _ _ _ v]
 rw [if_neg (by rw [List.count_eq_zero.mpr v]; omega),←(mitt H e i).deriv,g,deriv_const]
abbrev ditch (S T:List I):= S.filter (fun i=>decide (i∉T))
def knowR (S T p:List I) :Prop:=∀ i∈T,S.count i=p.count i
-- require δ coordinates zero on T. River.
lemma spar_z (p:List I)(hp:p.Nodup)(t:p⊆T)(x:Key I)(e:x∈hill I)(h:∀ j∈T,x j=0):lance (fun z=>carR z s • M) p x= if knowR s T p then carR x (ditch s T) • M else 0:=by
 induction p generalizing s with
 | nil=>
    change carR x s • M= _; split
    next g=>
       rw [show ditch s T=s from List.filter_eq_self.mpr (fun b v=> decide_eq_true (fun z=> (List.count_eq_zero.mp (g b z)) v))] -- decide_eq_true in core accepts iff
    next g=> unfold knowR at g; push Not at g; obtain ⟨b,g,y⟩:= g; change s.count b≠0 at y; rw [show carR x s=0 from List.prod_eq_zero (List.mem_map.mpr ⟨b,List.count_pos_iff.mp (Nat.pos_of_ne_zero y),h b g⟩),zero_smul]
 | cons i l ih=>
    have T':i∈T:= t (by simp)
    obtain ⟨q,r⟩:=List.nodup_cons.mp hp
    have H:(i::l).count i=1:=by rw [List.count_cons_self, List.count_eq_zero.mpr q] -- tune
    by_cases a:s.count i=1
    · have P:=lace_C l (show Set.EqOn (cutI (fun z=>carR z s • M) i) (fun z=>carR z (s.erase i) • M) (hill I) from fun z e=>by rw [sparks s M i z e,if_pos a]) e
      change lance (cutI _ _) _ _= _; rw [P]; rw [ih _ r (fun j y=>t (List.mem_cons_of_mem _ y))]
      have K(b)(xT:b∈T): (s.erase i).count b = l.count b ↔ s.count b=(i::l).count b:=by
         by_cases u:b=i; · subst b; rw[List.count_erase_self,a,H,List.count_eq_zero.mpr q]; simp
         rw[List.count_erase_of_ne u]; simp [List.count_cons, Ne.symm u,u]
      by_cases w:knowR s T (i::l)
      · rw [if_pos w,if_pos (show knowR _ _ _ from fun b x=>(K b x).mpr (w b x))]; have hp:= (List.perm_cons_erase (List.count_pos_iff.mp (show 0 < s.count i by omega))).filter (fun j=>decide (j∉ T)); rw [List.filter_cons_of_neg ?_] at hp; rw [←c_eq _ _ hp]; simp [T'] -- tune
      rw [if_neg w,if_neg (fun a=> w (fun b x=>(K b x).mp (a b x)))]
    rw [if_neg (fun p=> a ((p i T').trans H))]; exact (lace_C l (show Set.EqOn (cutI (fun z=>carR z s • M) i) (fun z=>0) (hill I) from fun z t=>by rw [sparks s M i z t,if_neg a]) e).trans (launch l x e)
end
end Iona
end YM.CF.Scree.Ing
end
