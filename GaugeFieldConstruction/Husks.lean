import GaugeFieldConstruction.Infar
import GaugeFieldConstruction.Paris
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 55000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
open TableF Lenten Lenten.Layout Fren
open Frugal
open Py.Riant
-- arbitrary finite labels grouped by Seat. further partition within group by programs.D.
variable {N:Side}{I S:Type}[LinearOrder I][Fintype I][Fintype S][DecidableEq S]
namespace Directory
variable (D: Directory I S)
variable {P B:Side} {X:GramM (mid N B)} {Y:GramM (mid P B)}
variable (L:Side)(o:S→Seat (mid P B))(y:S→Seat (mid N B))(T: S→Scree.Hub (mid N B))(hT:∀ i,(T i).val.1=y i)
variable (VΨ:I→ RegBudget (mid P B))(F:I→Vow.Pax (mid N B)) (W:I→ Zone (mid N B))
variable {h t s a μ τ b q d:ℝ} {A: S→Aura (mid N B)}
variable (M0:D.TourG)(M1:D.TourF)(K0:D.ToMG)(K1:D.ToPC)
variable (Tq:Paid D X W y M1 M0 K0 K1 L t b h) (j:S)
open Connect
abbrev Tribe (z:Key I)(j:S):Prop:=∀ i:I,D.own i≠j→ z i=0
abbrev κPart (k:Bool)(z:Key I):FrameK (D.NameK j k):=fun i=>z i.val
abbrev κLift (k:Bool)(z:FrameK (D.NameK j k)): Key I:= fun i=> if h:D.own i=j∧ D.kind i=k then z ⟨i,h⟩ else 0
abbrev Salary:= Ctags D K0 K1 L M0
abbrev TransferX (z:Key I):= toV_C (F_v D y) (Salary D L M0 K0 K1) z
lemma Liftκ (k:Bool)(z:FrameK (D.NameK j k))(i:D.NameK j k): κLift D j k z i.val=z i:=dif_pos i.property
lemma LiftX(k: Bool)(z:FrameK (D.NameK j k))(i:I)(h:D.own i≠ j∨ D.kind i ≠ k): κLift D j k z i=0:=dif_neg (not_and_or.mpr h)
lemma Tribe_up (k:Bool)(z:FrameK (D.NameK j k)): Tribe D (κLift D j k z) j:=fun i h=> LiftX _ _ _ _ _ (Or.inl h)
lemma Tribe_sum (z:Key I)(h:Tribe D z j):κLift D j true (κPart D j true z) +κLift D j false (κPart D j false z)=z:=by
 funext i; rw [Pi.add_apply]
 by_cases hp:D.own i=j; swap; · rw [LiftX (h:=Or.inl hp),LiftX (h:=Or.inl hp),h i hp,add_zero]
 cases he:D.kind i<;> unfold κLift <;> simp [hp,he] -- tune κPart
lemma Salary_zero {k i:I}(e:D.own k≠D.own i): D.Salary L M0 K0 K1 k i=0:=by
 unfold Salary Ctags DayP DayF; have p:k≠i:=fun h=>e (h ▸ rfl); split<;>simp [e,p]
-- lemma support and gap.
local notation "Fm"=> D.F_v y
local notation "CK"=> D.Salary L M0 K0 K1
local notation "Tφ"=> D.TransferX L y M0 K0 K1
lemma Tribe_c {z:Key I}(t: Tribe D z j): Tribe D (Tφ z) j:=by
 intro i h; apply sum_eq_zero; intro k p; by_cases q:D.own k=j; · rw [Salary_zero _ _ _ _ _ (i:=k) (k:=i) (by rwa [q]),zero_mul] -- tune
 rw [t _ q,mul_zero]
lemma κGap_T (z:Key I)(i:D.Vname j): Tφ z i.val=(GapGain L (D.depth j):ℂ) * z i.val:=by
 unfold TransferX toV_C
 let v:=i.property.1; let u:=i.property.2
 rw [sum_eq_single_of_mem (s:=pipe_ζ Fm i.val) i.val (mem_filter.mpr ⟨mem_univ _,rfl⟩)]; · rw [Salary,Day_G]; unfold DayF; simp [i.property.2]
 intro a p q; rw [show CK i.val a=0 from ?_,zero_mul]; by_cases t:D.own a=j; swap; · apply Salary_zero; rw [v]; exact Ne.symm t
 cases d:D.kind a
 · let V:D.Vname j:= ⟨a,t,d⟩; rw [show CK i.val a=D.DayF K0 K1 L M0 j V i.val from Day_G D K0 K1 L M0 j V _]; unfold DayF; simp [i.property.2,Ne.symm q,V]
 let V:D.Pname j:=⟨a,t,d⟩; rw [show CK i.val a=D.DayP K1 L M0 j V i.val from Day_C D K0 K1 L M0 j V _]; exact dif_neg (by simp [i.property.2]) -- tune
lemma Coat_β (v:FrameK (D.Pname j))(i:D.Pname j): Tφ (κLift D j true v) i.val= CoatP (K1 j) L (M0 j) v i:=by
 let T:= CoatP (K1 j) L (M0 j); have he:T v=∑ k:D.Pname j,v k • T (κEye k):=by
    conv_lhs => rw [show v= ∑ k:D.Pname j,v k • κEye k from (by ext j; unfold κEye; simp [Finset.sum_apply,Pi.single_apply,mul_ite]),map_sum]
    simp_rw [map_smul]
 change _= T v i; rw [he,Finset.sum_apply]; refine shift_p D y i.val j true i.property.1 _ _ ?_ ?_ -- tune missing X
 · exact fun a z=>(show CK i.val a*κLift D j true v a=0 from (by rw [LiftX _ _ _ _ _ z,mul_zero]))
 intro b; rw [Liftκ,Salary,Day_C]; unfold DayP; rw [dif_pos i.property]; exact mul_comm .. -- tune shift_p omitted p
lemma Yaw_sum (u v:Key I): Tφ (u+v)= Tφ u+ Tφ v:= by funext i; simp only [TransferX,Pi.add_apply,toV_C,mul_add,sum_add_distrib]
lemma Y_sum {u v:Key I}(p:D.Tribe u j)(h:D.Tribe v j) : D.Tribe (u+v) j:=fun i g=> by rw [Pi.add_apply,p i g,h i g, add_zero]
include Tq
lemma Pierce_T (G:Key I)(h:Tribe D G j) : ∃ z:Key I,D.Tribe z j∧ Tφ z= G:=by
 let L':ℂ:= GapGain L (D.depth j); have hx:L'≠0:=by unfold L'; exact_mod_cast (show 0< GapGain L (D.depth j) from Real.rpow_pos_of_pos (by exact_mod_cast L.property) _).ne' -- tune
 let F:=fun i:D.Vname j=> L'⁻¹* G i.val; let F':=κLift D j false F
 let H:=fun i:D.Pname j=> G i.val- Tφ F' i.val
 obtain ⟨u,v⟩:= (Tq.lenses j).1.2 H; let U:= κLift D j true u; let Z:=U+F'
 have he: Tribe D Z j:= Y_sum D j (Tribe_up D j true u) (Tribe_up D j false F) -- tune props
 refine ⟨Z,he,?_⟩; let t:=Tribe_c D L y M0 K0 K1 j he
 funext i; by_cases p:D.own i=j; swap; · rw [t i p,h i p]
 cases d:D.kind i
 · let x:D.Vname j:=⟨i,p,d⟩; change Tφ Z x.val=_; rw [κGap_T]; change L'*(U i+ F' i)=G i; rw [show U i=0 from LiftX _ j _ _ _ (Or.inr (by simp [d])),zero_add, show F' i= L'⁻¹* G i from Liftκ D j false F x, mul_inv_cancel_left₀ hx]
 let x:D.Pname j:=⟨i,p,d⟩; unfold Z; rw [Yaw_sum,Pi.add_apply]; rw [show Tφ U i= H x from (Coat_β D L y M0 K0 K1 j u x).trans (congrFun v x)]; exact sub_add_cancel ..
#print axioms Pierce_T
end Directory
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
