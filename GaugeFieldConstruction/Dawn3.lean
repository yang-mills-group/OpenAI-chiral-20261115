import GaugeFieldConstruction.SortM3
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
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
set_option linter.flexible false
variable {n:Side}{ι γ τ E:Type}[Fintype ι][LinearOrder ι][NormedAddCommGroup E][NormedSpace ℝ E]
namespace Ladder3
variable (A:FC ι)
variable {S D:Finset ι}
def scar : List (Dough ι)→ FC ι | []=>A | x::l=> bump (scar l) x.val
variable {L K H:List (Dough ι)}
open Matrix
lemma αs (X Y: Dough ι): bump (bump A X.val) Y.val=bump (bump A Y.val) X.val:=by
 unfold bump; simp only [sub_mul,mul_sub, mul_assoc]; rw[show X.val*Y.val=Y.val*X.val from congrArg Subtype.val (mul_comm X Y),←mul_assoc X.val Y.val A,←mul_assoc Y.val X.val A,show X.val*Y.val=Y.val*X.val from congrArg Subtype.val (mul_comm X Y)]; abel
lemma scar_append (S T:List (Dough ι)): scar A (S++T)=scar (scar A T) S:=by induction S with|nil=>rfl | cons i S h=> simp only [List.cons_append,scar,h]
lemma scar_perm (p:L.Perm K):scar A L=scar A K:=by
 induction p with
 | nil=>rfl
 | cons a l h=> rw [scar,scar,h]
 | swap a b l=>rw[scar,scar,scar,scar,αs]
 | trans h g p q=>exact p.trans q
lemma scar_blank (L:List (Dough ι)):scar (0:FC ι) L=0:=by induction L with|nil=>rfl|cons i L h=>simp [scar,h,bump]
lemma scar_clear (p:Fock.Sector S false A)(i:Dough ι)(q:Fock.Sector D false i.val) (w:i∈L)(h:Disjoint S D):scar A L=0:=by
 rw[scar_perm A (List.perm_cons_erase w|>.trans (List.perm_append_singleton ..).symm),scar_append, show scar A [i]=0 from ?_,scar_blank]
 exact sub_eq_zero.mpr ((p.apart q h).trans (one_smul ..))
-- sum-reindex multilinear across T tuples
lemma scar_sumA (f:γ→FC ι)(G:Finset γ)(L:List (Dough ι)):scar (∑ i∈G,f i) L=∑ i∈G,scar (f i) L:=by
 induction L with |nil=> simp[scar] |cons i L h=>simp_rw [scar,h,σq]
open Fin
section
variable [Fintype γ]
lemma scar_sum (d:ℕ)(f:γ→ Dough ι) : (∑ i:Fin d→γ,scar A (List.ofFn fun j=> f (i j)))= scar A (List.replicate d (∑ j:γ,f j)):=by
 classical
 induction d with
 | zero=> simp [List.ofFn] -- tune
 | succ d ih=>
    let M:= Dough ι; let H(i:Fin (d+1)→γ):= scar A (List.ofFn fun j=> f (i j)); let P:= Fin.consEquiv (fun _:Fin (d+1)=>γ)
    change ∑ i,H i=_
    rw[← Equiv.sum_comp P H,Fintype.sum_prod_type,List.replicate_succ,scar]; change _= bump _ (((Dough ι).val) _)
    rw [←ih,map_sum,σb]; refine sum_congr rfl fun j _=>?_; unfold H; rw[σq]; refine sum_congr rfl fun i _=>?_
    simp only [List.ofFn_succ,scar,P,consEquiv,Equiv.coe_fn_mk,Fin.cons_zero,Fin.cons_succ]; rfl -- tune val
lemma scar_double (p d:ℕ)(F:γ→ Dough ι)[Fintype τ](V:τ→ Dough ι): (∑ i:Fin p→γ,∑ j:Fin d→τ,scar A ((List.ofFn fun x=>V (j x))++ (List.ofFn fun z=>F (i z))))= scar A (List.replicate d (∑ i:τ,V i) ++ List.replicate p (∑ j:γ,F j)):=by
 simp_rw[scar_append,scar_sum]; rw[← scar_sumA (f:=fun i:Fin p→γ=> scar A _) (G:=univ),scar_sum] -- tune
end
abbrev discount (p d:ℕ):ℂ:= ((p.factorial:ℂ)*(d.factorial:ℂ))⁻¹
def packetZ (m:ℕ):= {i:ℕ × ℕ // i.1+i.2 ≤ m}
def pts₃ (m:ℕ) : Finset (ℕ×ℕ):=((Finset.range (m+1)) ×ˢ (Finset.range (m+1))).filter (fun i=> i.1+i.2 ≤ m)
lemma specs₃ (m:ℕ)(i:ℕ×ℕ): i∈pts₃ m ↔ i.1+i.2 ≤ m:=by simp only [pts₃,mem_filter,mem_product,mem_range]; omega
open scoped Classical
lemma season_e (V W T:Dough ι)(z:ℂ)(t:rank2 A)(v:T=z • 1 +(V+W)): A*(exp T).val=(exp T).val * (∑ i∈pts₃ 2, discount i.1 i.2 • scar A ((List.replicate i.2 W)++List.replicate i.1 V)):=by
 let S:=V+W
 have he(F:FC ι): bump F T.val=bump F V.val+bump F W.val:=by rw [v]; change bump F (z • (1:FC ι)+(V.val+W.val))=_; simp only [bump,mul_add,add_mul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_one,one_mul]; abel -- Dough.smul rfl?
 rw[Yz_h _ _ t]; congr 1
 simp_rw [he]; rw[δb,δb,αs _ V W]
 have hh : pts₃ 2={((0,0):ℕ×ℕ),(0,1),(0,2),(1,0),(2,0),(1,1)} :=by ext ⟨i,k⟩; rw [specs₃]; simp; omega -- tune prop simp
 rw[hh]; norm_num [discount,Finset.sum_insert,List.replicate,scar,Nat.factorial] -- produces .val. x.X sums.
 have f(Z:FC ι) : (1/2:ℂ) • Z=(1/2:ℝ) • Z:=by rw [←Complex.coe_smul]; norm_num
 have ht(Z:FC ι) : Z=(1/2:ℝ) • Z+(1/2:ℝ) • Z:=by rw [←add_smul]; norm_num
 rw [αs A V W]; simp_rw [f]
 nth_rw 3 [ht (bump (bump A W.val) V.val)]; abel
end Ladder3
end Ivey
end YM.CF.Scree.Ing
end
