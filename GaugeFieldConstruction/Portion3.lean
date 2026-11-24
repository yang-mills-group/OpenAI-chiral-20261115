import GaugeFieldConstruction.Panel3
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
namespace ShoreQ
open Tuner
variable (V:RegLime I α n)(A:Factor3 n)(Q:LeaseQ γ n)(σ:I→ Seat n)(k:I)
variable (p d:ℕ)(y:Hub n)(T:Heart A.H Q.H p)
local notation "Θv"=> Heart y V.S d
variable (P:BudgetPoint)(W:Orbit n)
local notation "Ω"=> flags P.threshold W.1
local notation "Ar"=> A.raw W
local notation "Tz"=> Q.raw
abbrev φU(x:Key I)(s:α): Cipher n:= carR x (V.V s) • V.K s (flags P.threshold W.1) W
def subjectD(p:ℕ)(x:Key I)(t: Fin p→γ)(u:Fin d→α) : FC (Dwell n):= discount p d • scar (A.raw W) ((List.ofFn fun i=> φU V P W x (u i)) ++ List.ofFn (fun i=>Q.raw (t i) W))
section
variable {r h s:ℝ}{g:α→ℝ}{l:γ→ℝ}{K:ℕ}(u:RegPay V P σ r h g)(v:Act3 A P K h s)(L:Leased Q P K h l)
variable (b:ScopeΔ A Q p T y)(ht:p+d≤fadeN A)(pW:Rue.FleetS P.threshold W.1)(x:Key I)
local notation "Vz"=> filmic V A Q
lemma re_sc (u:Heart y V.S d): subjectD V A Q d P W p x T.val u.val=carR x (tags V d y u) • origin3 V A Q p d y T P W u:=by
 let q:= loomR V A Q p d T y u; let f:= (Sum.elim (fun j=> V.K j Ω W) (fun i=>Q.raw i W)); let Λ:= (Sum.elim (fun j=>carR x (V.V j)) (fun _:γ=> (1:ℂ)))
 have hp:q.map f=(List.ofFn fun i=> V.K (u.val i) Ω W)++List.ofFn (fun i=>Q.raw (T.val i) W):=by unfold q loomR; simp only [List.map_append,List.map_ofFn]; rfl
 have he:q.map (fun i=>Λ i • f i)=(List.ofFn fun i=> φU V P W x (u.val i)) ++ List.ofFn (fun i=>Q.raw (T.val i) W):=by unfold q loomR; simp only [List.map_append,List.map_ofFn]; congr 2; funext i; exact one_smul ..
 have hc:(q.map Λ).prod=carR x (tags V d y u):=by
    unfold q loomR; rw [List.map_append,List.prod_append,List.map_ofFn,List.map_ofFn,List.prod_ofFn,List.prod_ofFn]; simp only [Λ,Function.comp_apply,Sum.elim_inl,Sum.elim_inr, Finset.prod_const_one,mul_one]; exact (roster_N ..).symm
 unfold subjectD origin3; rw [←hp,←he,scar_one,hc,smul_comm]
local notation "costJ"=> subjectD V A Q d P W p x
include v pW
private lemma scar_zoom (L:List (Cipher n))(i:Cipher n)(h:i∈L)(X:Support (More n))(q:Fock.Sector (camp X) false i.val)(t:Disjoint A.H.val.2 X): scar Ar L=0:= scar_clear Ar (v.qual _ pW) _ q h (Finset.disjoint_left.mpr fun s v p=>Finset.disjoint_left.mp t (mem_filter.mp v).2 (mem_filter.mp p).2)
include b u ht
lemma saleR : (∑ i:Fin d→α,x k • (costJ) T.val i)=∑ u:Heart y V.S d, (carR x ((peatE V A Q k p d ht T y).from_ u)) • origin3 V A Q p d y T P W u:=by
 have ht(u:Heart y V.S d): carR x ((peatE V A Q k p d ht T y).from_ u) = x k* carR x (tags V d y u):=rfl
 simp_rw [ht,mul_smul (x k),← re_sc V A Q p d y T P W x]
 let Z(i:Fin d→α):=x k • (costJ) T.val i; let Y:= LeadQ y.val.2 V.S d
 change ∑ i,Z i=∑ i:↥Y,Z i.val; rw [←sum_subtype Y (p:=fun i=>i∈Y) (fun _=>Iff.rfl)]; symm; apply sum_subset (subset_univ _); intro i α t; by_contra H
 apply t; refine mem_filter.mpr ⟨mem_univ _,fun j=>mem_filter.mpr ⟨mem_univ _,?_⟩⟩; intro q
 let e:=φU V P W x (i j)
 have he: Fock.Sector (camp (V.S (i j))) false e.val:=(life ((u.wine (i j) Ω).lit W)).scale _
 unfold Z subjectD at H; exact H (by rw [scar_zoom A P W v pW _ e (List.mem_append_left _ (List.mem_ofFn.mpr ⟨j,rfl⟩)) _ he (Disjoint.mono_left b.1 q),smul_zero,smul_zero])
omit ht u b
include L
lemma saleT : (∑ i:Heart A.H Q.H p,∑ j:Fin d→α,(costJ) i.val j)=∑ t:Fin p→γ,∑ u:Fin d→α,(costJ) t u:=by
 let G(t:Fin p→γ):=∑ i:Fin d→α,(costJ) t i; let Y:=LeadQ A.H.val.2 Q.H p; change (∑ i:↥Y,G i.val)=∑ i,G i; rw[←sum_subtype Y (p:=fun i=>i∈Y) (fun i=>Iff.rfl)]
 apply sum_subset (subset_univ _); intro i w hu
 refine sum_eq_zero fun j p=>?_ ; unfold subjectD; by_contra h; apply hu; refine mem_filter.mpr ⟨mem_univ _,fun z=>mem_filter.mpr ⟨mem_univ _,?_⟩⟩; intro t
 exact h (by rw[scar_zoom A P W v pW _ (Q.raw (i z) W) (List.mem_append_right _ (List.mem_ofFn.mpr ⟨z,rfl⟩)) _ (L.qual ..) t,smul_zero])
omit v pW L
lemma Sale_U: (∑ t:Fin p→γ,∑ u:Fin d→α,(costJ) t u)= discount p d • scar Ar ((List.replicate d (∑ i:α,φU V P W x i))++List.replicate p (∑ j:γ,(Tz) j W)):=by
 unfold subjectD; rw [←scar_double (τ:=α) Ar p d (fun j=>(Tz) j W)]; simp_rw [Finset.smul_sum]
end
-- Binder dangers explicitly print.
#print axioms saleR
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
