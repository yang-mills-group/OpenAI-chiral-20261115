import GaugeFieldConstruction.Photon4
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
open Pastry 
namespace Iona
variable {I nι:Type}[Fintype I][LinearOrder I]{n:Side}
open Rio Grotto
namespace Isle
-- map directly.Q grade output. lengths consistency.Realm.No skiplits.
variable (σ:I→ Seat n) (F:XE I (InkD n) n)(K:KK I (Copy n) n)
local notation "Ακ"=> InkD n
local notation "Βκ"=> Copy n
abbrev PI (I:Type)(n:Side):= dues I (Hub n)
abbrev KI (I:Type)(n:Side):= dues I (Force n)
abbrev FrameT : Isle I (PI I n) (KI I n) n:=⟨Prod.snd,F,Prod.snd,K,fun i=>Cue I i.1,fun i=> Cue I i.1⟩
variable (X:CashI I n) (C:BudgetPoint)(h r:ℝ)(v:ℕ)(T:PI I n → ℝ)(Y:KI I n→ℝ)(fV:BillX C σ h r T F)(vY:BillF C σ h r v Y K)
local notation "B"=> FrameT F K
private lemma cue_D (S:Finset I): (Cue I S).toFinset=S:=sort_toFinset .. -- tune
private lemma cue_L (S:Finset I):(Cue I S).length=S.card:=length_sort ..
include fV vY
lemma frameL : Load (FrameT F K) C σ r h v T Y:=by
 refine ⟨fun i=>?_,fun i=>?_,fun i=>?_ ,fun i g=>?_,fun i g=>?_⟩ -- `form tuple` expects x
 · change Medal _ _ _ _ _ (Bplain (Cue I i.1).length _ _); rw[cue_L]; exact fV.lit i
 · change Medal _ _ _ _ _ (Bplain (Cue I i.1).length _ _); rw[cue_L]; exact (vY.lit i).1
 · exact (vY.lit i).2 -- lean `_` placeholder earlier not `?_`
 · change Pub _ (Cue I i.1).toFinset _; rw[cue_D]; exact fV.pin i g
 change Pub _ (Cue I i.1).toFinset _; rw [cue_D]; exact vY.pin i g
variable (P:Rio I n)(Y':CashI I n)(W:Weighted C σ r h v P Y')
local notation "Xκ"=> F+ P.X+P.Y
local notation "Yκ"=> K+ P.B
local notation "p∆"=> FrameT (F+P.X+P.Y) (K+P.B)
include W
lemma frame_r : Load (FrameT (F+P.X+P.Y) (K+P.B)) C σ r h v (T+Y'.W+Y'.M) (Y+Y'.F) :=by
 have he:= ReefX.registry_plus σ cloudP (T:=PitR C h r) ReefxR fV W.white; have hx:=ReefX.registry_plus σ cloudP (T:=PitR C h r) ReefxR he W.active; exact frameL σ _ _ C h r v _ _ hx (ReefX.registry_plus σ cloudK (T:=PitF C h r v) (ReefxF v) vY W.bank)
-- speak.(Frame Space.A2). explicit coeff star.
lemma frameSoul : Isle.Speak (FrameT (F+P.X+P.Y) (K+P.B)) σ:= by
 let H:=frame_r σ _ _ _ _ _ _ _ _ fV vY _ _ W; exact ⟨fun i g=>(H.refs i g).2,fun i g=>(H.rolls i g).2⟩
omit fV vY W
section
variable (z:Key I) {ι E:Type}[Fintype ι][AddCommMonoid E][Module ℂ E]
lemma sorterH (S:Finset I):carR z (Cue I S)=pine S z:=by
 have he:=List.prod_toFinset z (show (Cue I S).Nodup from Finset.sort_nodup ..); rw [cue_D] at he; exact he.symm
lemma sorter_C (G:dues I ι→ E) (h:∀ i:dues I ι,G i ≠0→ i.1∈realm_C σ)(i:ι):Canz σ _ G z i=∑ j: Finset I,carR z (Cue I j) • G (j,i):=by
 unfold Canz; simp_rw [sorterH]; apply Finset.sum_subset (subset_univ _) (fun c d e=>?_); rw [show G (c,i)=0 from Classical.byContradiction (fun j=>e (h (c,i) j)),smul_zero]
end
variable (z:Key I)(U:Orbit n)(q:Rue.FleetS C.threshold U.1)
include fV q
omit q fV
include vY
lemma Φ_formula (U:Orbit n): PourUp (FrameT F K).U (fun i=>(FrameT F K).κQ U i z)= (fun i=> Canz σ _ K z i U) :=by -- include vY
 funext i; unfold PourUp κQ; rw [sum_filter]; rw [sorter_C σ z K (fun i h=> (vY.pin i h).1) i]; unfold KI dues; rw [Fintype.sum_prod_type]; simp [Finset.sum_apply,FrameT]
omit vY
include q fV
lemma Γ_formula (z:Key I): exponentL C (Canz σ _ F z) U.1= (FrameT F K).gaugeQ C U z:=by
 unfold exponentL gaugeQ PI dues; rw [Fintype.sum_prod_type,sum_comm]; apply sum_congr rfl; intro i _
 unfold gaugey numbE; change _= ∑ j:Finset I,(if Disjoint i.val.2 (flags _ U.1) then (_:Cipher n) else 0); rw[sorter_C σ z F (fun i h=> (fV.pin i h).1)]
 by_cases h:pingS C.threshold i.val.2 U.1
 · rw[Set.indicator_of_mem h]; rw[Finset.sum_apply]; apply Finset.sum_congr rfl; intro j k; exact (if_pos ((Rue.shoreK C.threshold U.1 q i.val.2).mpr h)).symm
 rw [Set.indicator_of_notMem h]; exact Eq.symm (Finset.sum_eq_zero fun j _=> if_neg (fun k=> h ((Rue.shoreK _ _ q _).mp k)))
end Isle
end Iona
end YM.CF.Scree.Ing
end
