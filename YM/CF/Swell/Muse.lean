import YM.CF.Swell.Bark
import YM.CF.Neon.Hick
import YM.CF.Swell.Chill
import YM.CF.Swell.Yard
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
open Push.AbsoluteSums Trees Wray Ione Fief
-- exchange ordinary anchor bank to incidence over all sites.Extra fuel.PSR.
variable {N:Side}{P:BudgetPoint} {K:ℕ}{c α Θ:ℝ}
open Py
open Neon
open Larch Oath
variable {B m:Side}{n L:ℕ}(o:Site (mid m B))(F:RegBudget (mid m B)){h r a:ℝ}
variable (pF:IncX (fun _=>False) F P h r)(ht:1 ≤ h)(hs:∀ i:Scree.Hub (mid m B),i.val.1≠Cube.node o → F i=0)
variable {x:ℝ}
variable (Ψ:Taxi.DayT P.order a)(uK:0 ≤ a)(Υ:Gala P.power P.order 100 x 3)(hu:10 ≤ P.B)(hk:P.threshold=Pressure.temp x)(he:1 ≤ Pressure.radiusB x)(hp:20 < (More (mid m B)).val)(hP:3 ≤ (mid m B).val)
include pF ht hs Ψ uK Υ hu hk he hp hP
lemma brink_K (L:ℕ): ∃ E T,∃ Z:ℂ, Axon L o P E h (Δv P a*r) T ∧ ‖T.1‖ ≤ r ∧ ‖T.2‖*h^2 ≤ 2*peka_H P.power*r ∧∀ (V:Orbit (mid m B)),Rue.FleetS P.threshold V.1 → flags P.threshold V.1=∅→ exponentL P F V.1 = Z • (1:Cipher (mid m B)) + exponentL P E V.1:=by
 let Q:=univ.filter (fun i:Scree.Hub (mid m B)=> i.val.1 = Cube.node o); obtain ⟨A,x,u⟩:=pF.weight; have hv(i:Scree.Hub (mid m B))(p:i∈Q): i.val.1=node o:= (mem_filter.mp p).2
 have hh: (∑ i∈Q,P.mass i.val.2 (A i)) ≤ r:=by unfold Q; rw [sum_filter]; refine le_trans ?_ (u (node o)); refine Finset.sum_le_sum ?_; intro i x; simp [eq_comm]
 let V:=hand_W o P h Q id F A r (fun i _=>x i) hv ht hh L a Ψ uK Υ hu hk he hp hP; obtain ⟨e,h_,z,k,mh⟩:= V
 let s:=firth P L Q id; let T:= (Eφ o P Q id F L,Eκ o P Q id F L); have hp:= quest_B o P h Q id F A r (fun i _=> x i) hv ht hh s (show s⊆ Q from filter_subset ..)
 refine ⟨_,T,Moto.hypeE F s,e,hp.1,hp.2,fun U v h'=>?_⟩; have H:=mh U v; unfold fuelV at H; rw [Finset.sum_filter] at H; simp_rw [h'] at H; simp only [fuelH] at H -- trim
 refine Eq.trans ?_ (show pump_I P Q id F U=_ from by simpa only [fuelH,Finset.disjoint_empty_right,not_true,ite_false,sum_const_zero, add_zero] using H); unfold exponentL pump_I; symm; refine Eq.trans (sum_congr (g:=fun j:Scree.Hub (mid m B)=> numbE P.threshold j.val.2 (F j) U.1) rfl (fun i _=>(numb_b (P:=P) i (F i) U).symm)) (sum_subset (subset_univ Q) (fun j p u=>by rw [hs _ (fun h=>u (mem_filter.mpr ⟨p,h⟩))]; simp [numbE]))
omit pF ht hs Ψ uK Υ hu hk he hp hP
end YM.CF.Swell
