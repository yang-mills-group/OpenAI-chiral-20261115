import GaugeFieldConstruction.FrostiM
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
variable {I J γ M:Type}[Fintype I][LinearOrder I][Fintype J]
section loot
variable [NormedCommRing M][NormedAlgebra ℂ M][CompleteSpace M]
lemma lances1(f g:Key I→ M)(p:River f)(q:River g)(s:List I)(h:∀ v:Key I,∀ i∈s,∀ z,g (update v i z)=g v)(z:Key I)(v:z∈hill I): lance (f*g) s z=lance f s z*g z:=by
 induction s generalizing f z with
 | nil=>rfl
 | cons i t ih=>
    have H:Set.EqOn (cutI (f*g) i) (cutI f i*g) (hill I):=by
       intro x r; have he:(fun w=> (f*g) (update x i w))=(fun w=> f (update x i w)*g x):=by funext w; rw[Pi.mul_apply,h x _ (by simp)]
       rw [←(mitt (p.mul_T q) r i).deriv, he]; exact ((mitt p r i).mul_const _).deriv
    exact (lace_C t H v).trans (ih _ (p.flow i) (fun x b w=> h x b (List.mem_cons_of_mem _ w)) _ v)
lemma lnces_S {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](f:J→ Key I→ E)(L:Finset J)(p:∀ i∈L,River (f i))(s:List I)(z:Key I)(v:z∈hill I): lance (fun x=>∑ i∈L,f i x) s z=∑ i∈L,lance (f i) s z:=by
 induction L using Finset.induction with
 | empty=> simp only[sum_empty]; -- launch private
           induction s generalizing z with
           | nil=>rfl
           | cons i s ih=>
              apply (lace_C s (show Set.EqOn (cutI (fun _=>(0:E)) i) (fun _=>0) (hill I) from fun x k=>(mitt (zeroR _) k i).deriv.symm.trans (deriv_const ..)) v).trans; exact ih z v
 | insert i L h ih=>
    have t(j)(w:j∈L):River (f j):= p j (mem_insert_of_mem w)
    simp_rw [sum_insert h]; exact (fork_H (p i (mem_insert_self ..)) (tip_bank L f t).1 s v).trans (congrArg (_ + ·) (ih t))
-- budget staff list assembly.Any enumeration incl equivalence by `Mem`; choose sorted once via `toList`.
noncomputable def rosterF(s:Finset J)(f:J→List I):List I:=(s.toList.map f).flatten
lemma roster_mem (s:Finset J)(f:J→List I)(i:I):i∈ rosterF s f↔ ∃ j∈ s, i∈ f j:=by simp[rosterF]
lemma roster_N (s:Finset J)(f:J→List I)(z:Key I):carR z (rosterF s f)=∏ i∈s,carR z (f i):=by
 unfold carR rosterF; rw [List.map_flatten,List.prod_flatten]; simp_rw[List.map_map]; change (s.toList.map (fun j=>carR z (f j))).prod=_
 rw [←List.prod_toFinset (fun j=>carR z (f j)) (Finset.nodup_toList _)]; rw [show s.toList.toFinset=s from (by ext x; simp)] -- tune
lemma roster_M (s:Finset J)(f:J→List I)(F:J→ M)(x:Key I):carR x (rosterF s f) • (∏ i∈s,F i)=∏ j∈s,carR x (f j) • F j:= by rw [roster_N, prod_smul]
lemma sil_Z (a:M)(T: List I)(v:T≠[])(z:Key I)(e:z∈hill I): lance (fun _:Key I=>a) T z=0:=by
 match T with
 | []=>exact False.elim (v rfl)
 | i::T=>
    apply (lace_C T (show Set.EqOn (cutI (fun _:Key I=>a) i) (fun _=> (0:M)) (hill I) from fun x w=> (mitt (zeroR _) w i).deriv.symm.trans (deriv_const ..)) e).trans
    have h:= lnces_S (J:=I) (E:=M) (fun _ _=>0) ∅ (by simp) T z e; simpa only [sum_empty] using h
end loot
end Iona
end YM.CF.Scree.Ing
end
