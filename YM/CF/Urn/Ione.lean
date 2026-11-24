import YM.CF.Urn.Open
import YM.CF.Urn.Shaft
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {I α ι n m: Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m][LinearOrder ι][Fintype ι]
open Stilo Scree Hake
open Pastry
-- one-particle basis matrix monochrome.
abbrev crib(U:UNI n)(k x:Bool): UNI n:=thread (if k then invFilm U else U) (x.xor k)
lemma cream(U:UNI n)(k b:Bool)(i j:n)(h:Bool): (Scree.spice U k).val (h,j) (b,i)=if h=b.xor k then (crib U k b).val j i else 0:=by cases k<;>cases b<;> cases h<;> simp [Scree.spice,Scree.opBool,jump_apply,closeV,crib]
-- Maple
abbrev lotB (b r:Bool)(U:UNI n): FC n→+* FC n where
 toFun:=Spire.tourP U b r
 map_one':=by cases r<;> simp [Spire.tourP,singT,win_i,theta_one]
 map_zero':=by cases r <;> simp [Spire.tourP,singT,win_z,theta_zero]
 map_add' A B:=by cases r<;> simp [Spire.tourP,singT,win_a,theta_add]
 map_mul' A B:=Scree.nomZ b r U A B
abbrev lotY(b r:Bool)(U:UNI n):FC (LeanV n)→+* FC (LeanV n) where
 toFun:=Scree.sauce b r U
 map_one':=by unfold sauce; rw [singT,win_i,map_one]
 map_zero':=by unfold sauce; rw [singT,win_z,map_zero]
 map_add' A B:=by unfold sauce; rw [singT,win_a,map_add]; rfl
 map_mul' A B:=by unfold sauce; rw [singT,singT,singT,win_m,map_mul] -- namespace tune
abbrev sewV(U:UNI n)(r:Bool)(i j:LeanV n):ℂ:= (Scree.spice U r).val j i
lemma mold (b r:Bool)(U:UNI n)(i:LeanV n) : lotY b r U (put i)=roseB (sewV U r) put i:=by
 rcases i with ⟨v,i⟩; rw [show lotY b r U (put _)=sauce b r U (wire v i) from rfl,leafU b r]; unfold roseB; rw [Fintype.sum_prod_type,sum_eq_single (v.xor r)]; intro a _ p; apply sum_eq_zero; intro j _; unfold sewV; rw [cream,if_neg p,zero_smul]; simp
lemma mole (b r:Bool)(U:UNI n)(i:Hake.Oboe n) : lotB b r U (bell i)= roseB (ι:=Oboe n) (sewV U r) bell i:=by
 rcases i with ⟨t,j⟩; have he :roseB (ι:=Oboe n) (sewV U r) bell (t,j)= ∑ i:n,(crib U r t).val i j • bell (t.xor r,i) :=by
    unfold roseB; rw [Fintype.sum_prod_type,sum_eq_single (t.xor r)]; apply sum_congr rfl; intro i _; unfold sewV; rw [cream, if_pos rfl]; intro a _ p; apply sum_eq_zero; intro i _; unfold sewV; rw [cream,if_neg p,zero_smul]; simp
 rw [he]; change Spire.tourP U b r _=_; unfold Spire.tourP
 have hp : windX b (put j)=put j:=by cases b; rfl; exact put_clear _
 have hk : windX b (takeF j)=takeF j:=by unfold takeF; rw [win_s,hp]
 cases r <;> cases t
 · change twist (quantU U) (windX b (takeF j))=_; rw [hk, twist_t]; rfl -- tune
 · change twist (quantU U) (windX b (put j))=_; rw [hp, twist_p]; rfl
 · change theta U (windX b (takeF j))=_; rw [hk]; unfold theta; rw [show cc _= _ from (show cc (takeF j)=takeF j from by unfold takeF; rw [cc_star, put_clear]),screenM,Fock.twin, show twist (autumn n) (takeF j)=put j from by rw [takeF,map_star,top_swap]; exact star_star _,twist_p]; rfl
 change theta U (windX b (put j))=_; rw [hp]; unfold theta; rw [put_clear,screenM,Fock.twin, top_swap, twist_t]; rfl -- tune
end YM.CF.Urn
