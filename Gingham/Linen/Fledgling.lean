import Gingham.Linen.Tatting
import YM.CF.Vow.Goal
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Linen
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Ione


open Vow
variable {P:BudgetPoint} {n: Side} {a b h:ℝ}
variable {i:Scree.Hub n}

/-- Unmarked Reg: final flag consultation for term i.X. Includes its Ping mask,
 implemented by flag query on this support (consultation domains below). -/
def consult (X:Support (Cube.More n)) (E:InkD n) (D:Support (Cube.More n)): Copy n:=
 if Disjoint X D then oV E else 0

/-- Clearance for a final Y,D; wider domain (no halo test). -/
def Clears (P:BudgetPoint) (Y D:Support (Cube.More n)) (V: Pane n):Prop:=
 pingS P.threshold (Y\D) V ∧ D⊆flags P.threshold V

lemma clears_no_ties {Y:Support (Cube.More n)} {V: Pane n}
 (t: Rue.FleetS P.threshold V) :
 Clears P Y (Y∩flags P.threshold V) V :=
 ⟨(Rue.shoreK _ V t _).1 (Finset.disjoint_left.mpr fun _ v g=>
 (mem_sdiff.mp v).2 (mem_inter.mpr ⟨(mem_sdiff.mp v).1,g⟩)),inter_subset_right⟩

lemma consult_matches {X Y D:Support (Cube.More n)} (E:InkD n) (v: Orbit n)
    (s:X⊆Y) (k: Clears P Y D v.1):
    consult X E D v=numbE P.threshold X E v.1:=by
 unfold consult
 split
 · rename_i t; symm
   apply Set.indicator_of_mem (show v.1∈ _ from grow_b (show X⊆ Y\D from fun i p=>mem_sdiff.mpr ⟨s p,Finset.disjoint_left.mp t p⟩) k.1)


 rename_i t; symm
 apply Set.indicator_of_notMem (show v.1∉ _ from fun u =>
    t ((ping_le (show pingS P.threshold X v.1 from u)).mono_right k.2))

lemma Clears.open_set (Y D:Support (Cube.More n)): IsOpen {V|Clears P Y D V}:=by
 have h:IsOpen {V:Pane n|D⊆flags P.threshold V}:=by
   rw [show {V:Pane n|D⊆flags P.threshold V}=⋂ i:D,{V|i.val∈flags P.threshold V} by
        ext x; simp only [Set.mem_setOf_eq,Set.mem_iInter]; exact ⟨fun p i=>p i.property,fun u i h=> u ⟨i,h⟩⟩]
   exact isOpen_iInter_of_finite fun i=>flags_open _ _
 exact ping_o.inter h

/-- Consultation agrees even as a germ on the paying uses. -/
lemma consult_germ {X Y D:Support (Cube.More n)} (E:InkD n) (v: Orbit n)
    (s:X⊆Y) (k: Clears P Y D v.1):
    (fun x=> consult X E D (x,v.2)) =ᶠ[𝓝 v.1] numbE P.threshold X E := ((Clears.open_set Y D).eventually_mem k).mono fun i h=>consult_matches E (i,v.2) s h

structure LitReg (P:BudgetPoint)(i:Scree.Hub n)(E:InkD n)(h a:ℝ):Prop where
  stiff : PressB P i E h a
  localCharge (D) : Medal P i.val.2 (D∩i.val.2) (consult i.val.2 E D) h a
  dresses (Y D:Support (Cube.More n)): i.val.2⊆Y→
     Medal P Y D (consult i.val.2 E D) h a

lemma pressT {E:InkD n}(p:PressB P i E h a)(t:a≤b): PressB P i E h b where


 term:=p.term
 fitted:=p.fitted
 measureV:=p.measureV
 gaugeV:=p.gaugeV
 worth:=by obtain ⟨v,k,u,g⟩:=p.worth; exact ⟨v,k,u,g.trans t⟩

lemma pressFloor {E:InkD n}(p:PressB P i E h a)(u:0≤h) :0 ≤a:=by
 obtain ⟨v,y,_,b⟩:=p.worth
 exact le_trans (sum_nonneg fun j _=>mul_nonneg
   (show 0≤Scree.tariff P i.val.1 h j by unfold Scree.tariff; positivity) (y j)) b

/-- Simultaneously per Hub, using only one fixed activation constant,
 payment for Press and for consultation on any final support/flag configuration. -/
lemma light {E:InkD n}(p:PressB P i E h a)(u:0≤h) :
 LitReg P i E h ((1+chi_f P.order)*a):=by
 have v:=pressFloor p u
 have r:=rimR p u
 have activ(D Y T:Support (Cube.More n)) (sub:i.val.2⊆Y) (s:T⊆D) :
   Medal P Y T (consult i.val.2 E D) h ((1+chi_f P.order)*a):=by
   rw [add_mul]
   have t:0 ≤chi_f P.order*a:=mul_nonneg (spicy_f _) v
   unfold consult; split
   · rename_i d; refine Medal.big (Medal.stretchB r sub (empty_subset _) ?_) (le_add_of_nonneg_left ((one_mul a).symm ▸ v))
     exact fun x b=> mem_sdiff.mpr
       ⟨sub (mem_sdiff.mp b).1, Finset.disjoint_left.mp (d.mono_right s) (mem_sdiff.mp b).1⟩
   exact Medal.big Medal.zeroT (by rw [one_mul]; exact add_nonneg v t)


 exact ⟨pressT p (by rw [add_mul, one_mul]; exact le_add_of_nonneg_right (mul_nonneg (spicy_f _) v)),
    fun D=>activ D _ _ le_rfl inter_subset_left, fun Y D t=>activ D Y D t le_rfl⟩

