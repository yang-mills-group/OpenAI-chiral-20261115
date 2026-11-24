import GaugeFieldConstruction.SorghumG3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 120000
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
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace Tuner
open Mica
variable {S:α→Support (More n)} (V:Mica I β n) (L:Tuner I S)(T:Ids n)
local notation "Ψ"=> Heart L.anchor S L.d
local notation "R0"=> Legist L.anchor S L.d
local notation "Vx" y:max=> ((R0) y).val.2
local notation "Xd" y:max b:max=> (mixedHub (R0 y) V.z b).val.2
local notation "Dh"=> til V.z
variable {P:BudgetPoint}{r h c:ℝ}{σ:I→Seat n}{D:ℕ}{g:α→ℝ}{w:β→ℝ}
variable (A: L.accords P σ r h c D g)(B: V.MintH σ P h r D w)
-- Pose A issue.Expects at actual trajectory X, Sector of Vx.
structure oasis (P:BudgetPoint)(D:ℕ)(f:Orbit n→(x:Heart L.anchor S L.d)→ FC (Dwell n)) : Prop where
    heard :∀ (x:Heart L.anchor S L.d)(W:Orbit n), Rue.FleetS P.threshold W.1 →∀ (X Y:Support (More n)),(Legist L.anchor S L.d x).val.2⊆X→ X∩ flags P.threshold W.1=Y→Lattice.halo D Y⊆ X→ L.issue x X Y W=f W x
    sector :∀ (x: Heart L.anchor S L.d)(W:Orbit n), Rue.FleetS P.threshold W.1→Fock.Sector (camp (Legist L.anchor S L.d x).val.2) false (f W x)
variable {f:Orbit n→ (x:Heart L.anchor S L.d)→FC (Dwell n)}(u:L.oasis P D f)(W:Orbit n)(W0:Rue.FleetS P.threshold W.1)(z:Key I)
local notation "F0"=> f W
local notation "Ω"=> flags P.threshold W.1
local notation "H0"=> L.pureT V T
local notation "H1"=> L.busyT V
local notation "ζp"=> ∀ v:Force n,True -- tune
abbrev Mu_z (V:Mica I β n)(z:Key I)(i:β)(W:Orbit n): Cipher n:=carR z (V.V i) • V.K i W
local notation "Θ" i:max=> Mu_z V z i W
section
variable (x:Heart L.anchor S L.d) (K:Finset β)(v:PriceI V.z (flags P.threshold W.1) K)
local notation "hT"=> carR z (L.from_ x)
local notation "R"=> R0 x
local notation "G"=> H1.fillT -- unused?
local notation "C"=> L.busyT V
local notation "D1"=> ashC (R0 x) V.z K
local notation "Q0"=> (∏ j∈K, Mu_z V z j W)
include A B u v W0
lemma ζash_1 : let ℓ:= ashC (R0 x) V.z K
 let A: (Cipher n):= if ℓ.Nonempty then (∏ j∈K\ℓ, Mu_z V z j W) * (carR z ((L.busyT V).fromB x ℓ) • ((L.busyT V).termB x ℓ W)) else 0
 ((L.pureT V T).goReg P z W.1 x * (Q0) + A).val= hT • Sault.rind (f W x*(Q0).val):=by -- tune notation
 intro j A'; let H0x:= (L.pureT V T).goReg P z W.1 x; let Z:= (R0 x).val.2
 let D':=til V.z j; let Y':=walls V.z j; let X:=Xd x j
 have hsub: j ⊆ K:=filter_subset ..; have hE:X∩Ω=D':=by
    change (Z∪Y') ∩ Ω=D'; rw [Finset.union_inter_distrib_right, show Y'∩Ω=D' from creek_in v j hsub]; apply Finset.union_eq_right.mpr; intro i q; obtain ⟨a,b⟩:=mem_inter.mp q
    obtain ⟨c,t,y⟩:=mem_biUnion.mp (show i∈til V.z K from v.covers ▸ b); exact mem_biUnion.mpr ⟨c,(ash_mem).mpr ⟨t,fun p=>disjoint_left.mp p a ((V.z c).property.2 y)⟩,y⟩
 let y:= R0 x; have hs:Z⊆ X:=subset_union_left
 have hD:Disjoint Z Ω↔Disjoint Z D':=by
    constructor; intro p; rw[←hE]; exact Disjoint.mono_right inter_subset_right p
    intro p; exact Finset.disjoint_left.mpr fun i q s=> disjoint_left.mp p q (hE ▸ mem_inter.mpr ⟨hs q,s⟩)
 let Kh:= ∏ l∈K\ j,Mu_z V z l W; let KP:=∏ l∈j,Mu_z V z l W
 let F:= F0 x
 have he:Q0= Kh*KP:=(prod_sdiff hsub).symm
 let Y:=∀ i:β,i∈K\j → Disjoint (plateI V.z i) Z
 have hY:Y:=fun i p=> Disjoint.symm (Classical.byContradiction fun q=> (mem_sdiff.mp p).2 (ash_mem.mpr ⟨(mem_sdiff.mp p).1,q⟩))
 let Vw:= walls V.z (K\j)
 have dF:= u.sector x W W0
 have hp: Flour (camp Vw) Kh.val:=by
    let x':=K\j; have hu(a:Finset β)(q:a⊆x') : Flour (camp Vw) (∏ l∈a,Mu_z V z l W).val:= by
       induction a using Finset.induction with | empty=> rw [prod_empty]; exact Flour.grainE | insert i a p v=> rw[prod_insert p]; refine ((Flour.smul ((((B.rate i).lit W).lift ?_)) _).mul (v ((subset_insert ..).trans q))); exact camp_b (fun w e=> mem_biUnion.mpr ⟨i,q (mem_insert_self ..),e⟩)
    exact hu _ le_rfl
 have ht: Sault.rind (F*(Q0).val)= Kh.val * Sault.rind (F*KP.val):=by
    have hu:Disjoint (camp Z) (camp Vw):=by
       refine Finset.disjoint_left.mpr ?_; intro i z w; obtain ⟨j,u',d⟩:=mem_biUnion.mp (mem_filter.mp w).2; exact disjoint_left.mp (hY _ u') d (mem_filter.mp z).2
    rw [he]; exact pert dF hp hu KP.val
 rw [show _=hT • (Kh.val*Sault.rind (F*KP.val)) from congrArg (hT • ·) ht]
 let M:=L.rockT x
 have hr:H0x= if Disjoint Z D' then hT • (M W) else 0:=by
    unfold H0x Grotto.goReg; change (ite (!false && decide (Disjoint Z Ω)) (hT • L.rockT x (W.1,T)) 0)=_; rw [show L.rockT x (W.1,T)=M W from congrArg fair (A.tag ..)]; simp [hD]
 let ZM:= if Disjoint Z D' then M W else (0:Cipher n); change (H0x*(Q0)+A').val= _
 by_cases s:j.Nonempty; swap
 · rw[hr,if_pos (show Disjoint Z D' from (by unfold D' til; simp [not_nonempty_iff_eq_empty.mp s])), show A'=0 from if_neg s, add_zero,he, show KP=1 from (by unfold KP; rw [Finset.not_nonempty_iff_eq_empty.mp s]; simp),mul_one, mul_comm _ Kh,Algebra.mul_smul_comm]
   have P0: Disjoint Z Ω:= hD.mpr (by unfold D' til; simp [not_nonempty_iff_eq_empty.mp s]); have hw:L.issue x Z ∅ W =F:=u.heard x W W0 Z ∅ le_rfl (disjoint_iff_inter_eq_empty.mp P0) (by simp[Lattice.halo])
   have he: (M W).val= Sault.rind F:=(congrArg Subtype.val (congrArg fair hw)).trans (pie_s _ _ dF)
   change hT • (Kh.val* (M W).val)= _; rw [he, show F*(1:Cipher n).val=F from mul_one _] -- maybe $rw he$ rewrote KP RHS? both instances he rewrites RHS.KTune
 let Ck:=∏ l∈j,V.K l; let c':=Ck W; let hJ:=carR z (V.legend j)
 have hz:KP=hJ • c':=by unfold c' Ck KP; rw [Finset.prod_apply]; exact (roster_M j V.V (fun j=> V.K j W) z).symm
 have hv: ZM*c'= ((if Disjoint Z D' then M*Ck else 0):Copy n) W:=by change _= _; unfold ZM; split_ifs; rfl; exact zero_mul _ -- tune
 have ℓ: H0x=hT • ZM:=by rw [hr]; unfold ZM; split_ifs; rfl; exact (smul_zero _).symm
 have hA:A'=Kh*((hT*hJ) • (fair (L.issue x X D' W * c'.val)- ZM*c')):=by
    rw [hv]; unfold A'; rw[if_pos s, show carR z ((H1).fromB x j)= hT*hJ from (by change carR _ (_++_)=_; unfold carR; exact (by change _= (List.map z _).prod*(List.map z _).prod; rw[List.map_append,List.prod_append]))]; rfl -- tune
 let P':= L.issue x X D' W
 rw [ℓ,hA,he,hz,show L.issue x X D' W=P' from rfl]; by_cases h:c'=0
 · rw[h]; simp [Sault.rind,fair0]
 have u':P'=F:= u.heard _ _ W0 _ _ hs hE ((Mica.someL V _ j B W h).1)
 rw [u']; have fy : (fair (F*c'.val)).val=Sault.rind (F*c'.val):=by
    have g:Fock.Sector Finset.univ false F:= lift_v dF (subset_univ _)
    rw [fair,dif_pos (light_e (g.mul (life (fineShape c'))))]
 have hx(T K₀ J:Cipher n)(c u:ℂ): (c • T)*(K₀*(u • c'))+K₀*((c*u) • (J-T*c'))=K₀*((c*u) • J):=by
    have he:(c • T)*(K₀*(u • c'))=K₀*((c*u) • (T*c')):=by
       calc _=K₀*((c • T)*(u • c')):=by ring
            _=_:=by rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm u T, mul_smul c]
    rw [he,smul_sub,mul_sub]; abel
 rw [hx]; change Kh.val*((hT*hJ) • (fair _).val) = hT • (Kh.val*Sault.rind (F* (hJ • c'.val)))
 rw [fy, Alma F _ hJ, mul_smul (hT)]; rw [Algebra.mul_smul_comm]
where Alma(F B:FC (Dwell n))(t:ℂ):Sault.rind (F*(t • B))= t • Sault.rind (F*B):=by rw [Algebra.mul_smul_comm, Sault.rind, map_smul]
end
include A B u W0
lemma πash : ((H0).cashVector P z (fun i=> Θ i) W +(H1).cashVector P z (fun i=> Θ i) W).val=Sault.rind ((∑ x:Heart L.anchor S L.d, carR z (L.from_ x) • f W x) * (hum (flags P.threshold W.1) V.z (fun i=> Θ i)).val):=by
 let F(i:Finset β):= ∏ j∈i, Θ j; let a:= univ.filter (fun i:Finset β=>PriceI V.z Ω i); let U:= ∑ i∈a,F i
 have hu: hum Ω V.z (fun i=> Θ i)=U:=rfl
 let t(x:Ψ):= L.ζash_1 V T A B u W W0 z x -- need K currency.As.
 have hp(x:Ψ):((H0).goReg P z W.1 x*U+(H1).goBoat P z (fun i=> Θ i) W x).val=Sault.rind ((carR z (L.from_ x) • F0 x)*U.val):=by
    let g:= (H0).goReg P z W.1 x; let L0(i:Finset β):= ashC (R0 x) V.z i
    let q(i):= F (i\L0 i)*(carR z ((H1).fromB x (L0 i)) • ((H1).termB x (L0 i) W))
    let b:=fun i=> if (L0 i).Nonempty then q i else 0
    have hz : (H1).goBoat P z (fun i=> Θ i) W x =∑ i∈a,b i:=by
       change ∑ i∈univ.filter (fun i=>PriceI _ _ i ∧ Charcoal (R0 x) true _ ∧ (L0 i).Nonempty),q i=_
       unfold b; rw[← sum_filter (s:= a) (p:=fun i:Finset β=> (L0 i).Nonempty) (f:=q)]; unfold a; rw[filter_filter]; simp [Charcoal]
    let M:Cipher n→+FC (Dwell n):=(Dough (Dwell n)).val.toRingHom.toAddMonoidHom
    let Z:=carR z (L.from_ x) • F0 x
    rw[hz]; unfold U; rw[mul_sum,←sum_add_distrib]; change M (∑ i∈a,(g*F i+b i))= Sault.rind (Z*M (∑ i∈a,F i)); rw [map_sum,map_sum, mul_sum,Sault.rind,map_sum]; apply sum_congr rfl; intro i w
    apply (t x i (mem_filter.mp w).2).trans; unfold Z; rw[Algebra.smul_mul_assoc,map_smul]; rfl
 have hs: ∀ x:Heart L.anchor S L.d,(H0).goBoat P z (fun i=> Θ i) W x=0:=by
    intro x; unfold Grotto.goBoat; exact sum_eq_zero fun j _=>by dsimp only; rw [show ∀ v,(H0).termB x v W=0 from fun v=>rfl,smul_zero,mul_zero]
 have hr:∀ x:Ψ,(H1).goReg P z W.1 x=0:=fun x=> if_neg (by simp[busyT]) -- tune
 unfold Grotto.cashVector
 -- dependently.To change
 let Y₀(x:Ψ):=carR z (L.from_ x) • F0 x
 let H(x:Ψ):= (H0).goReg P z W.1 x; let Px(x:Ψ):=(H1).goBoat P z (fun i=> Θ i) W x; let M:= (Dough (Dwell n)).val
 rw [hu]; change M ((∑ x:Ψ,H x)*U+(∑ x:Ψ,(H0).goBoat P z (fun i=> Θ i) W x)+((∑ x:Ψ,(H1).goReg P z W.1 x)*U+∑ x:Ψ,Px x))= _
 rw [sum_eq_zero (s:= (univ:Finset Ψ)) (fun i _=> hs i), sum_eq_zero (s:= (univ:Finset Ψ)) (fun i _=>hr i), zero_mul,zero_add, add_zero, sum_mul, ←sum_add_distrib,map_sum, sum_mul,Sault.rind,map_sum]
 apply sum_congr rfl; exact fun x _=>hp x
#print axioms ζash_1
end Tuner
end Ivey
end YM.CF.Scree.Ing
end
