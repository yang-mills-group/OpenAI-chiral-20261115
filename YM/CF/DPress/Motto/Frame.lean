import YM.CF.DPress.Motto.Shade
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open DPress.Plaque Larch Ione Taxi Bake Salt Rue
namespace WagesC.Blend
variable {n:Side}{k L:ℕ}(P:BudgetPoint){a h b:ℝ}
local notation "Sx"=> Point n
variable (B:Blend n k)(z:ℝ)(V:Orbit n)
local notation "Y"=> (P.threshold)
local notation "F'"=> (flags P.threshold V.1)
local notation "α"=> (φΩ B)
lemma αscale (p:ℝ)(F:Cusp n): fuelV P (p • F) V=p • fuelV P F V:=by unfold fuelV; rw [Finset.smul_sum]; exact sum_congr rfl fun i _=>rfl
lemma march_p(v:Point n) : Vow.march P (τ₀ v) (oV (fund v)) V =moldV n (μM (v:=Y) v V.1) :=by
 unfold μM Set.indicator Vow.march; simp only [Set.mem_setOf_eq]; by_cases t:pingS Y (haloW v) V.1; · rw [if_pos (show pingS _ (τ₀ v).val _ from t),if_pos t]
 rw [if_neg (show ¬pingS _ (τ₀ v).val _ from t),if_neg t,map_zero]
variable (u:FleetS P.threshold V.1)
include u
lemma kia (i:Sx × Sx) : (z*φΩ B i) • Vow.march P (τ₀ i.2) (oV (fund i.2)) V= φΩ B i • Vow.march P (τ₀ i.1) (oV (pureQ z i.1)) V+Vow.march P (coinP i) (oV (fA B z i)) V+ (z*φΩ B i) • fuelV P (stroke (τ₀ i.2) (τ₀ i.1) (coinP i) (oV (fund i.2)) (oV (fund i.1))) V := by -- precedence: (*) > •?
 let x:=τ₀ i.1; let y:= τ₀ i.2; let w:=coinP i; let X:= F'; let L:=X∩w.val; let f:= oV (fund i.1); let g:=oV (fund i.2)
 have hv:y.val ⊆ w.val:= subset_union_right; have hz:x.val⊆ w.val:=subset_union_left
 rw [show Vow.march P (τ₀ i.1) (oV (pureQ z i.1)) V = z • Vow.march P x f V from ?_]; swap
 · unfold Vow.march; by_cases h:pingS Y x.val V.1; rw [if_pos h,if_pos h]; rfl; rw [if_neg h,if_neg h,smul_zero] -- y vs ∅
 have he(y:Aura n)(v: y.val⊆ w.val)(g:Copy n):flick y g L V=Vow.march P y g V:=by
    rw [march_f V u]; unfold Vow.flick; have hc:Disjoint X y.val↔ Disjoint L y.val:= ⟨Disjoint.mono_left inter_subset_left ,fun t=> Finset.disjoint_left.mpr fun i x h=> Finset.disjoint_left.mp t (Finset.mem_inter.mpr ⟨x,v h⟩) h⟩ -- implicit arg order
    split_ifs with p p' p'; rfl; exact (p' (hc.2 p)).elim; exact (p (hc.1 p')).elim; rfl
 let U:=fuelV P (stroke y x w g f) V; let b:=φΩ B i
 by_cases h : Disjoint X w.val; swap
 · have hx:U=Vow.march P y g V-Vow.march P x f V:=by unfold U stroke; rw [shade_t,if_pos (show fuelH X w from ?_), Pi.sub_apply,he y hv g, he x hz f]; intro e; exact h e.symm -- unfold fuelH is ¬Disjoint _ _
   have hh:Vow.march P (coinP i) (oV (fA B z i)) V=0:=by rw [march_f V u,if_neg h]
   rw [hh]; change _= b • (z • _) +0+(z*b) • U; rw [hx,smul_sub,add_zero, smul_smul,mul_comm b z]; abel
 have hx:U=0:=by unfold U stroke; rw [shade_t,if_neg (show ¬ fuelH X w from ?_)]; intro p; exact p h.symm
 rw [march_f V u (τ₀ i.2),march_f V u (coinP i),march_f V u x,if_pos h,if_pos (Disjoint.mono_right hv h),if_pos (Disjoint.mono_right hz h)]; change _= b • (z • _) +(z*b) • (g V - f V) +(z*b) • U; rw [hx,smul_zero,smul_sub,smul_smul,mul_comm b z]; abel
omit u
lemma ownT : exponentL P (αLan (n:=n) z) V.1=∑ i∈κN n k,φΩ B i • Vow.march P (τ₀ i.1) (oV (pureQ z i.1)) V:=by
 let X(i:Sx):= Vow.march P (τ₀ i) (oV (pureQ z i)) V; let U':=(univ:Finset Sx); suffices h: exponentL P (αLan z) V.1=∑ i,X i by
    rw [h,←sum_fiberwise_of_maps_to (s:=κN n k) (g:=fun i:Sx×Sx=>i.1) (t:=U') (fun _ _=>mem_univ _)]; refine sum_congr rfl ?_; intro i _; symm; rw [←one_smul ℝ (X i),← B.money i,sum_smul]; exact sum_congr rfl fun j t=>by rw [(mem_filter.mp t).2] -- rw orientation h metavariable
 unfold exponentL; rw [←sum_fiberwise (g:=fun i:Scree.Hub n=>i.val.1)]; refine sum_congr rfl fun i _=>?_ ; rw [sum_eq_single (hup i),numb_b,αLan,if_pos rfl]
 · intro j t g; rw [numb_b,αLan,if_neg (show j≠_ from by rw [(mem_filter.mp t).2]; exact g)]; unfold Vow.march; split<;> rfl
 simp
include u
lemma finances : moldV n (B.Φ (h:=P.threshold) z V.1)= exponentL P (αLan z+B.Sα z) V.1+fuelV P (B.Zα z) V:=by
 unfold Φ Zα Sα; rw [map_sum,Larch.ripe_H P V ..,ownT P B,release_v,←sum_add_distrib,tunes,←sum_add_distrib]; apply sum_congr rfl; intro i q
 rw [αscale,←show Vow.march P (coinP i) _ V=Vow.march P (lagE (χΩ i)) (oV (fA B z i)) V from rfl,←kia P B z V u,march_p]; rw [←map_smul]; unfold φΩ; congr 2; rw [mul_comm z] -- copies
omit u
lemma origin(x:Pane n): B.Φ (h:=P.threshold) 0 x=0:=by simp [Φ]
@[fun_prop] lemma measurable_t : Measurable (B.Φ (h:=P.threshold) z):=by unfold Φ; fun_prop
lemma mode(g:Sweep n)(U:B.even g)(x:Pane n): B.Φ (h:=h) z (flashA g x)= B.Φ (h:=h) z x:=by
 unfold Φ; symm; refine sum_equiv (τσ g) (fun i=>similar ..) (fun i _=>?_ ); rw [show φΩ B (τσ g i)=φΩ B i from U i.1 i.2,show μM (v:=h) (τσ g i).2 (flashA g x)=_ from transitμ g i.2 x]
end WagesC.Blend
end YM.CF.Py.Kay
