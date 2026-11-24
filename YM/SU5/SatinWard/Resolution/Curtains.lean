import YM.SU5.SatinWard.Resolution.Tariff
set_option autoImplicit false
set_option maxHeartbeats 85000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]
-- Bureau.Plan for replacing only PARENT slots at first step. Allows all further hidden reserve/demand labels.
namespace ResolutionFrame
abbrev Announcement (ι η:Type):= Primary ι (ι ⊕ η)
variable {η:Type} [DecidableEq η] [Fintype η]
local notation "Κμ"=> Announcement ι η
local notation "Κπ"=> ι ⊕ η
abbrev familySpot(i:Κμ):Bool:=match i with| .inr (.inl _)=>true| _=>false
lemma family_eq (i:Κμ):familySpot i=true ↔ ∃ t:ι,i=.inr (.inl t):=by rcases i with i|(i|i)<;> simp [familySpot]
abbrev escrow (i:ι):Announcement ι η:= .inr (.inl i)
abbrev batchBy {E:Sort*} (P:Announcement ι η→ E)(T:ι→E)(i:Announcement ι η):E:= match i with | .inr (.inl i)=> T i| i=> P i
lemma oldbatch {E:Sort*} {i:Κμ}(p:familySpot i=false)(P:Κμ→ E)(T:ι→E): batchBy P T i=P i:=by rcases i with i|(i|i)<;> first| rfl| simp [familySpot] at p
lemma unaffected {E:Type*}[AddCommMonoid E][Module ℝ E](R:Reflow ι (ι⊕η))(L:Side)(T:Κμ→ E)(K:ι→ E)(i:Κμ)(p:familySpot i=false): (∑ j:Κμ,(R.sales L j i) • batchBy T K j)= ∑ j:Κμ,(R.sales L j i) • T j:=by
 apply sum_congr rfl; intro j _; rcases j with j|(j|j)
 · rfl
 · rcases i with i|(i|i)<;> simp_all [familySpot,Reflow.sales]
 rfl
lemma unaffected_u {R:Reflow ι (ι⊕η)} {L:Side} (T:Κμ→ ℝ)(K:ι→ℝ)(i:Κμ)(p:familySpot i=false): (∑ j:Κμ,|R.sales L j i| * batchBy T K j)= ∑ j:Κμ,|R.sales L j i| * T j:=by
 refine sum_congr rfl fun j _=>?_ ; rcases j with j|(j|j)
 · rfl
 · rcases i with i|(i|i)<;> simp_all [familySpot,Reflow.sales]
 rfl
abbrev coupon (R:Reflow ι (ι⊕η))(L:Side)(j:Κμ)(i:ι):ℝ:= if j=escrow i then -(1/2) else (1/2) * R.sales L j (.inl i)
abbrev incrementShip (R:Reflow ι (ι⊕η))(L:Side)(j i:Κμ):ℝ:= batchBy (R.sales L j) (coupon R L j) i
lemma couponSale (R:Reflow ι (ι⊕η))(L:Side)(j:Κμ)(i:ι) : coupon R L j i = (1/2)*(R.sales L j (Sum.inl i))-(1/2)*(if j=escrow i then 1 else 0):=by by_cases h:j=escrow i <;> simp [coupon,h,Reflow.sales]
lemma couponAbs (R:Reflow ι (ι⊕η))(L:Side)(j:Κμ)(i:ι) : |coupon R L j i| = (1/2)*|R.sales L j (Sum.inl i)|+(1/2)*(if j=escrow i then 1 else 0):= by by_cases h:j=escrow i<;> simp [coupon,h,Reflow.sales,abs_mul]
lemma dirac {E:Type*}[AddCommGroup E][Module ℝ E](Y:Κμ→ E)(i:Κμ): (∑ j:Κμ,(if j=i then 1 else 0:ℝ) • Y j)=Y i:=by simp [ite_smul]
lemma sailCoupon {E:Type*}[AddCommGroup E][Module ℝ E](R:Reflow ι (ι⊕η))(L:Side)(Y:Κμ→ E)(Z:ι→E)(i:ι): (∑ j:Κμ,incrementShip R L j (escrow i) • batchBy Y Z j)= (1/2:ℝ) • (∑ j:Κμ,R.sales L j (.inl i) • Y j)-(1/2:ℝ) • Z i:=by
 change (∑ j:Κμ,coupon R L j i • _) = _; simp_rw [couponSale,sub_smul,mul_smul,sum_sub_distrib,←smul_sum]; rw [dirac,unaffected R L Y Z _ rfl]
lemma energizing {F:ResolutionFrame ι}{X:Κμ→ArcΦ}{R:Reflow ι (ι⊕η)} {h θ:ℝ} (L:Side)(p:Energized F h θ X R)(i:Κμ): (∑ j:Κμ,incrementShip R L j i • batchBy X (fun j:ι=> F.enterBasis (η:=ι⊕η) h θ (Sum.inl j)) j)= F.enterBasis h θ i:= by
 by_cases v: familySpot i=true; swap
 · simp_rw [incrementShip,oldbatch (Bool.eq_false_iff.mpr v)]; rw [unaffected R L _ _ i (Bool.eq_false_iff.mpr v), economy_go L X F R h θ p i]
 obtain ⟨z,rfl⟩ := (family_eq ..).mp v; rw [sailCoupon R L X _ z, economy_go L X F R h θ p,sub_self]; rfl
lemma incent {F:ResolutionFrame ι}{R:Reflow ι (ι⊕η)}{X Y:BudgetPoint}{A κ q Q h T W C K v:ℝ}{L:Side} (r:RepositoryRent F C K A L)(y: |κ| ≤ Real.exp 1)(H:1≤h)(w:|T| ≤ nullLoss L*q)(g:Stretch F C)(p:1≤A)(u:1≤K)(f:0<q)(l:q≤Q)(e:Economics F C K A L X Y κ q Q R)(hW:|W| ≤ K)(z:v ≤ A*Q)(i:Κμ): (∑ j:Κμ,|incrementShip R L j i| * batchBy (F.rentInk A q h T W κ L) (fun _=> v) j) ≤ A* Q:=by
 let D:= F.rentInk (η:=ι⊕η) A q h T W κ L
 let D':=fun _:ι=> v
 let V:=batchBy D D'; have hx (j:Κμ):= rents_formula r y H w g p u f l e hW j
 change (∑ j:Κμ,_*V j) ≤ _
 unfold V; by_cases h:familySpot i=true; swap
 · simp_rw [incrementShip,oldbatch (Bool.eq_false_iff.mpr h)]; rw [unaffected_u D D' i (Bool.eq_false_iff.mpr h)]; exact hx i
 obtain ⟨i,rfl⟩:=(family_eq ..).mp h
 change (∑ j:Κμ,|coupon R L j i| * batchBy D D' j)≤ _
 simp_rw [couponAbs, add_mul,mul_assoc,sum_add_distrib, ←mul_sum,ite_mul,zero_mul,one_mul]
 rw [unaffected_u D D' _ rfl]; -- tune
 simp_rw [sum_ite_eq',mem_univ,if_true]; change _+(1/2)*v ≤ A*Q; linarith only [z,(show (∑ j: Announcement ι η, |R.sales L j (.inl i)| * D j) ≤ A*Q from hx _)]
-- can pay enlarged 1+f etc. Use paper at 1+2*#*(1+sprint L)
lemma repairSize {F:ResolutionFrame ι}{L:Side}{R:Reflow ι (ι⊕η)}{A C K κ q Q:ℝ}{X Y:BudgetPoint} (r:RepositoryRent F C K A L)(e:Economics F C K A L X Y κ q Q R) (j i:Κμ): |incrementShip R L j i|≤1+sprintCost L:= by
 unfold incrementShip; have v:= sprint_pos L; by_cases p: familySpot i=true; swap
 · rw [oldbatch (Bool.eq_false_iff.mpr p)]; exact (economical_bound r e j i).trans (le_add_of_nonneg_left zero_le_one)
 obtain ⟨i,rfl⟩:= (family_eq ..).mp p; change |coupon R L j i|≤ _; by_cases h:j=escrow i; simp [coupon,h]; linarith
 simp [coupon,h,abs_mul]; linarith [economical_bound r e j (.inl i)]
#print axioms incent
end ResolutionFrame
end ShapeLab
end YM.CF.QuadClock
