import GaugeFieldConstruction.AgilaM
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 110000
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
variable {I α β:Type}[Fintype I][LinearOrder I][Fintype α][Fintype β]
namespace Isle
variable {n:Side}(B:Isle I α β n)(p:Hub n)(σ:I→Seat n)(C:BudgetPoint)(U:Orbit n){S:List I}{s:Sect I}(u:Night S s)(v':Isle.Speak B σ)(pK:poke_F σ p.val.2 S.toFinset)(μ:ℝ)(k:I)(z:Key I)
local notation "VQ"=> B.salt_Four p S s μ u k
local notation "Rκ"=> Heart p B.UV s.reg.length
local notation "Nκ"=> Fin s.reg.length
local notation "Ω"=> flags C.threshold U.1
local notation "Zκ"=> (Legist p B.UV s.reg.length)
local notation "Φ"=> B.gaugey C U
local notation "Α"=> B.κQ U
local notation "Θ" i:max=>∏ j:Fin s.reg.length, lance (B.gaugey C U (i j)) (boon s j) z
local notation "ιM"=> (z k*(μ:ℂ))
section
variable (v:z∈hill I)(t: S.Nodup)(a:∀ i∈S,z i=0) (x: Heart p B.UV s.reg.length)
local notation "H"=> (Zκ x)
local notation "HQ"=> Charcoal (Zκ x) (decide (s.pack≠[])) Ω
local notation "Λ"=> rosterF univ (fun j:Nκ=>B.purseV S (x.val j))
local notation "OΖ" d:max=> (∏ j:Fin s.reg.length, B.noteV S (boon s j) (x.val j) d)
local notation "cP" x:max=> carR z x
local notation "ηP"=> cP (rosterF univ (fun j:Nκ=>B.purseV S (x.val j)))
private lemma bankSK(T:List I)(M: Cipher n): carR z (k::T) • (μ • M)=(z k*(μ:ℂ)) • (carR z T • M):=by
 change (z k * carR z T) • _= _; rw [← Complex.coe_smul,smul_smul,smul_smul,mul_right_comm] -- tune
private lemma sail_Q (M N:Cipher n) (t p:ℂ) :(t*p) • (M*N)=(t • M)*(p • N):=by rw [mul_smul,smul_mul_assoc,Algebra.mul_smul_comm]; -- tune p •
include v t a v' pK
private lemma Iturn (K:Finset β) (l:PriceI B.U Ω K) : let J:=ashC (Zκ x) B.U K; (VQ).goReg C z U.1 x*(∏ j∈K,B.κQ U j z)+(if HQ∧ J.Nonempty then (∏ j∈K\ J,B.κQ U j z)*(carR z ((VQ).fromB x J) • ((VQ).termB x J U)) else 0)= (z k * (μ:ℂ)) • ((Θ (x.val)) * (lance (fun w=> ∏ j∈K,B.κQ U j w) s.pack z)):=by
 intro J; let L:=Zκ x; let C':=decide (s.pack≠[])
 by_cases h:HQ; swap
 · rw [if_neg (fun q=>h q.1),add_zero]; have D:s.pack=[]:=Classical.byContradiction fun q=> h (Or.inl (decide_eq_true q)); have hv : Disjoint L.val.2 Ω := Classical.byContradiction fun q=> h (Or.inr q)
   unfold Grotto.goReg; change (if !C' && decide (Disjoint L.val.2 Ω) then cP (k::Λ) • (μ • (OΖ ∅) U.1) else 0)* _= _
   rw [if_pos ?_,D, RPin B p C U z v a t u x L.val.2 ∅ (subset_refl _) (Finset.disjoint_iff_inter_eq_empty.mp hv), bankSK μ k z Λ]; exact smul_mul_assoc .. -- arg tune
   simp [C',D,hv]
 have hX:(VQ).goReg C z U.1 x=0:=by
    rcases h with h|h
    · change (if !C' && _ then (_:Cipher n) else 0)=0; change C'=true at h; rw [h]; rfl
    change (if !C' && decide (Disjoint L.val.2 Ω) then (_:Cipher n) else 0)=0; simp only[L]; simp [h]
 rw [hX,zero_mul,zero_add, Cub_Z B p σ U z v a t u v' pK x K];
 by_cases b:J.Nonempty
 · rw [if_pos ⟨h,b⟩]; let D:=til B.U J
   have e: L.val.2∪walls B.U J= (mixedHub L B.U J).val.2:=rfl
   let X:=L.val.2∪walls B.U J; have w:J⊆K:= filter_subset ..
   have he: X∩Ω=D:=by
       unfold X D; rw[Finset.union_inter_distrib_right,creek_in l J w]; apply Finset.union_eq_right.mpr; intro i q
       obtain ⟨a,u'⟩:=mem_inter.mp q; obtain ⟨d,h',k'⟩:=mem_biUnion.mp (show i∈til B.U K from l.covers ▸ u')
       refine mem_biUnion.mpr ⟨d,(ash_mem).mpr ⟨h',?_⟩,k'⟩
       intro p; exact disjoint_left.mp p a ((B.U d).property.2 k')
   rw [RPin B p C U z v a t u x X D subset_union_left he]; let F:=(OΖ D) U.1; let W:= B.oracle S s J U; let Q:= ∏ j∈K\ J,Α j z
   change Q* (cP (k::(Λ++B.tressV S J)) • (μ • (F*W)))= (ιM) • ((ηP • F)*((cP (B.tressV S J) • W)*Q))
   rw [bankSK μ k z, show cP (Λ++B.tressV S J)= ηP * cP (B.tressV S J) from (by simp only[carR,List.map_append,List.prod_append]), sail_Q,← mul_assoc (_ • F), mul_comm _ Q,Algebra.mul_smul_comm] -- tune
 rw [if_neg (fun q=>b q.2)]; have s':s.pack≠[]:=by
    intro g; rcases h with h|h; · simp [g] at h
    obtain ⟨i,k,m⟩:=Finset.not_disjoint_iff.mp h; obtain ⟨j,x,y⟩:=mem_biUnion.mp (show i∈til B.U K from l.covers ▸ m); exact b ⟨j,(ash_mem).mpr ⟨x,fun p=> disjoint_left.mp p k ((B.U j).property.2 y)⟩⟩
 have he:lance (fun v:Key I=>∏ j∈J,B.κQ U j v) s.pack z=0:=by rw [Finset.not_nonempty_iff_eq_empty.mp b]; simp only [prod_empty]; exact sil_Z _ _ s' z v
 have h:= (BPin B U z v a t u J).symm.trans he; change _ = _ • (_ *((carR z (B.tressV S J) • B.oracle S s J U)* _)); rw[h,zero_mul,mul_zero,smul_zero]
local notation "Tψ"=> lance (B.heapQ C U) s.pack z
local notation "Wκ"=> B.heapQ C U z
private lemma port_V : (VQ).goReg C z U.1 x*(Wκ)+(VQ).goBoat C z (fun i=>Α i z) U x=(ιM) • ((Θ (x.val)) * (Tψ)):=by
 let L:=(univ:Finset (Finset β)).filter (fun i=>PriceI B.U Ω i)
 let f(V:Finset β)(z):=∏ j∈V,Α j z; let Q(V:Finset β):=lance (f V) s.pack z
 have hT:(Tψ)=∑ i∈L,Q i:=lnces_S _ L (fun i _=>κr B U _) _ z v; rw[hT,mul_sum,Finset.smul_sum]
 let Y(i:Finset β):= HQ∧ (ashC (Zκ x) B.U i).Nonempty
 let E(K):= let J:=ashC (Zκ x) B.U K; (∏ j∈ K\ J,Α j z)*(carR z ((VQ).fromB x J) • ((VQ).termB x J U))
 have hx:(VQ).goBoat C z (fun i=>Α i z) U x=∑ i∈L,(if Y i then E i else 0):=by
    rw [←sum_filter]; unfold Grotto.goBoat profileT; change ∑ i∈ univ.filter (fun i=>PriceI B.U Ω i ∧ Y i), E i = _; unfold L; rw [filter_filter]
 rw [hx]; rw [show Wκ= ∑ i∈L,f i z from rfl,mul_sum,←sum_add_distrib]; apply sum_congr rfl; intro i t'; exact Iturn B p σ C U u v' pK μ k z v t a x i ((mem_filter.mp t').2)
lemma card_turn : (VQ).cashVector C z (fun i=> Α i z) U= (ιM) • (Sect.wit (B.gaugeQ C U) (B.heapQ C U) s z):=by
 unfold Grotto.cashVector Sect.wit; rw [show hum Ω _ _= Wκ from rfl,sum_mul, ←sum_add_distrib,B.Leg_B p σ C U z v a t u v' pK, sum_mul,Finset.smul_sum]; exact sum_congr rfl (fun x _=>port_V B p σ C U u v' pK μ k z v t a x)
#print axioms card_turn

end
end Isle
end Iona
end YM.CF.Scree.Ing
end
