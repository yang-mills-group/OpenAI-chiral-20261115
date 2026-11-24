import GaugeFieldConstruction.DeemL
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
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
structure Mica (I β:Type)(n:Side) where
 z : β→ Force n
 V : β→ List I
 K : β→ Copy n
structure RegLime (I α:Type)(n:Side) where
 S : α→ Support (More n)
 V : α→ List I
 K : α→ Support (More n)→ Copy n -- D regarded as full barrier; often cap intersect here.
namespace Mica
variable {P:BudgetPoint}
variable (V:Mica I β n)(p:Hub n) (σ:I→Seat n)
section
variable (x:Finset β)(b:Bool)(k:ℕ)
structure MintH (σ:I→Seat n)(P:BudgetPoint)(h r:ℝ)(k:ℕ)(X:β→ℝ):Prop where
    rate(y): Medal P (plateI V.z y) (sealI V.z y) (V.K y) h (Bplain (V.V y).length (X y) r)
    form(y)(u): V.K y u≠0 → (sealI V.z y ⊆ flags P.threshold u.1) ∧ Lattice.halo k (sealI V.z y) ⊆ plateI V.z y
    seen(y): V.K y≠0→ poke_F σ (plateI V.z y) (V.V y).toFinset
local notation "D"=> til V.z x
local notation "X"=> (mixedHub p V.z x).val.2
lemma mistR(j)(q:j∈x): plateI V.z j ⊆ X:=fun _ v=>mem_union_right _ (mem_biUnion.mpr ⟨j,q,v⟩)
lemma addsF(j)(q:j∈x):sealI V.z j ⊆ D:=fun _ v=> mem_biUnion.mpr ⟨j,q,v⟩
lemma fair0 : fair (0:FC (Dwell n))=0:=Subtype.ext ((pie_s 0 (n:=n) ∅ (Fock.Sector.zero false)).trans (map_zero _)) -- tune
-- pricing full K
local notation "L"=> V.z
local notation "W"=>∏ j∈x,V.K j
def legend:= rosterF x V.V
lemma legend_len(r:ℝ): r^(legend V x).length=∏ j∈x,r^(V.V j).length:=by
 have he(L0:List ℕ):r^L0.sum=(L0.map (fun j=>r^j)).prod:=by induction L0 with|nil=>simp|cons i ls h=>rw [List.sum_cons,List.map_cons,List.prod_cons,pow_add,h]
 unfold legend rosterF; rw [List.length_flatten,List.map_map,he]; change (((x.toList.map (fun i=>(V.V i).length)).map fun i=>r^i).prod)= _; rw[List.map_map]; change (x.toList.map fun i=>r^(V.V i).length).prod= _; rw [←List.prod_toFinset (fun i=>r^(V.V i).length) (Finset.nodup_toList _)]; simp
lemma μy0{S₀:Type}[CommMonoidWithZero S₀] (f:β→S₀)(v:(∏ j∈x,f j)≠0)(i)(p:i∈x):f i≠0:=fun e=> v (prod_eq_zero p e)
section
variable {h r:ℝ}{B:β→ℝ}{k:ℕ}{σ:I→Seat n}(t:MintH V σ P h r k B)
include t
lemma make_Q (z:BasisI L p b x)(g:0≤ h): Medal P X D W h (Bplain (legend V x).length (∏ j∈x,B j) r):=by
 unfold Bplain; rw[legend_len,←Finset.prod_div_distrib]; refine Medal.prodP _ _ _ (fun j t' =>?_ ) g
 have u:=t.rate j
 have hq:= z.distinct.foot V.z t'
 refine u.stretchB (mistR V p x j t') (addsF V x j t') (fun i w=> Finset.mem_sdiff.mpr ?_)
 obtain ⟨a,h⟩:=mem_sdiff.mp w; exact ⟨mistR V p x j t' a,fun e=>h (hq ▸ mem_inter.mpr ⟨a,e⟩)⟩
lemma someL(u)(g:(W) u ≠0): (Lattice.halo k D⊆ X) ∧ D⊆flags P.threshold u.1:=by
 rw [Finset.prod_apply] at g; have f(j)(p:j∈x):= t.form j u (μy0 x _ g _ p)
 constructor
 · intro i h; unfold Lattice.halo at h; obtain ⟨v,a,b⟩:= (mem_filter.mp h).2|>.elim fun i u=>Exists.intro i (mem_filter.mp u)
   obtain ⟨j,l,w⟩:=mem_biUnion.mp a; exact mistR V p x j l ((f j l).2 (mem_filter.mpr ⟨mem_univ _,⟨v,mem_filter.mpr ⟨w,b⟩⟩⟩))
 intro i e; obtain ⟨j,a,b⟩:=mem_biUnion.mp e; exact (f j a).1 b
lemma see_M (v:(W)≠0)(i)(e:i∈ V.legend x):σ i∈ X:=by
 obtain ⟨j,t',b⟩:= (roster_mem ..).1 e
 exact mistR V p x j t' ((t.seen _ (μy0 _ _ v j t')) i (List.mem_toFinset.mpr b))
end
end
end Mica
end Ivey
end YM.CF.Scree.Ing
end
