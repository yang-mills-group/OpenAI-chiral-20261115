import GaugeFieldConstruction.Wens
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
abbrev pairC:= Cover×Cover
abbrev slice:= Axis⊕Axis
abbrev petals(i:slice) : pairC:= Sum.elim (fun j=> (-(step j:Cover),0)) (fun j=> (0,step j)) i
abbrev innerX: pairC:= (-((step 0: Cover)+step 0),(step 0:Cover)+step 0)
abbrev Ortho := Option slice
abbrev lotV := Ortho × Ortho
def spad (v:Ortho):pairC:= v.elim 0 petals
abbrev knots (k:lotV) := innerX+spad k.1+spad k.2
lemma petals_rad(i:Ortho): lateral (spad i).1 ≤ 1∧ lateral (spad i).2 ≤1:=by
 rcases i with _|i; · simp [spad,lateral_zero]
 rcases i with i|i
 · change lateral (-(step i:Cover))≤ 1 ∧ lateral (0:Cover)≤1; rw [lateral_neg]; exact ⟨(lateral_single _ (1:ℤ)).le,by rw [lateral_zero]; decide⟩
 change lateral (0: Cover)≤1∧ lateral (step i: Cover) ≤1; exact ⟨by rw [lateral_zero]; decide,(lateral_single _ (1:ℤ)).le⟩
lemma innerX_bound : lateral innerX.1 ≤2∧ lateral innerX.2 ≤ 2:=by
 change lateral (-(innerX.2:Cover))≤ _ ∧ _; rw [lateral_neg]; suffices h:lateral innerX.2 ≤2 by exact ⟨h,h⟩
 refine (lateral_add (step 0: Cover) (step 0: Cover)).trans ?_; rw [show lateral (step 0: Cover)=1 from lateral_single _ _] -- tune
lemma knot_rad(k:lotV): lateral (knots k).1 ≤4 ∧ lateral (knots k).2 ≤4:=by
 have he(x i j:Cover)(p:lateral x≤2)(v:lateral i≤1)(t:lateral j≤1):lateral (x+i+j) ≤4:=by have hx:=lateral_add x i; have ht:=lateral_add (x+i) j; omega
 exact ⟨he _ _ _ innerX_bound.1 (petals_rad _).1 (petals_rad _).1,he _ _ _ innerX_bound.2 (petals_rad _).2 (petals_rad _).2⟩
lemma knot_two(k: lotV): (knots k).1 ≠ (knots k).2:=by
 have h(i:Ortho):(spad i).1 0≤0 ∧ 0≤ (spad i).2 0:=by
    cases i with | none=> simp [spad]| some v=>rcases v with v|v <;> simp [spad,petals,Lattice.step,Pi.single_apply] <;> split <;> omega
 intro e; have hp:=congrFun e 0; change innerX.1 0 + (spad k.1).1 0+ (spad k.2).1 0= innerX.2 0+(spad k.1).2 0+(spad k.2).2 0 at hp; rw [show innerX.1 0= -2 by simp [Lattice.step], show innerX.2 0= 2 by simp [Lattice.step]] at hp
 have hi:= h k.1; have hj:=h k.2; omega
variable (o:Skye.Seat n)
abbrev parked (x:Cover) := AnchorN o+wrap n x
abbrev measuresN (k:lotV) := (parked o (knots k).1,parked o (knots k).2)
def siteOffset : Cover:= -Lattice.lift ((assembly n).residue (o-1))
lemma rent_z : lateral (siteOffset o) ≤4:=by
 unfold siteOffset; rw [lateral_neg]; unfold lateral; apply (sum_le_sum (g:=fun i=>1) _).trans; · simp [Axis]
 intro i _; have he:= lift_centers ((assembly n).residue (o-1)) i; change -(2:ℤ)< _ ∧ _ ≤ 2 at he
 omega
lemma anchor_E : node (AnchorN o)= o + wrap _ (siteOffset o):=by
 let X:= AnchorN o; let V:= Lattice.lift ((assembly n).residue (o-1)); have he: (assembly n).root X+wrap _ V=o-1:=(assembly n).unpack_at _
 rw [siteOffset,map_neg]; change (assembly n).root X+1=o+ -wrap _ V; have hp: (assembly n).root X=o-1-wrap _ V:=eq_sub_of_add_eq he; rw [hp]; abel
abbrev spotSize (x:Cover) := siteOffset o +(2:ℕ) • x
lemma mark_node (x:Cover) : node (parked o x)=o+wrap _ (spotSize o x):=by
 unfold node parked; rw [map_add,add_right_comm, show (assembly n).root _+ 1= _ from anchor_E o, Ratio.root_embed,Ratio.embed_wrap,add_assoc,←map_add]; rfl
lemma spot_price(x:Cover)(p:lateral x ≤ 4) : lateral (spotSize o x) ≤12:=by
 unfold spotSize; rw [two_smul]; have hp:= rent_z o; have ht:=lateral_add x x; have hv:=lateral_add (siteOffset o) (x+x); omega
lemma spot_lift (x:Cover)(p:lateral x ≤4)(u:20<n.val): stem o (node (parked o x))=spotSize o x:=by
 apply lift_path; · rw [mark_node]; abel
 have h:= spot_price o x p; change _ < n.val*2
 omega
lemma spot_gap(x:Cover)(p:lateral x ≤4)(u:20<n.val):separation o (node (parked o x)) ≤12:=by rw [separation_comm,separation]; change spread (stem o _ ) ≤ _; rw [spot_lift o x p u]; exact Finset.sup_le fun i _=> (height_l _ _).trans (spot_price o _ p)
lemma lift_park(x:Cover)(p:lateral x≤4)(u:20<n.val): stem (AnchorN o) (parked o x)=x:= lift_path (by unfold parked; abel) (by omega)
lemma takes(k:lotV)(u:20<n.val):(measuresN o k).1≠(measuresN o k).2:= fun e=> knot_two k ((lift_park o _ (knot_rad k).1 u).symm.trans ((congrArg (stem (AnchorN o)) e).trans (lift_park _ _ (knot_rad k).2 u)))
end Layout
end Lenten
end YM.CF.TableF
end
