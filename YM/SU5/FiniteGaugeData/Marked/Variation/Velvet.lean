import YM.SU5.FiniteGaugeData.Marked.Variation.Menu
import YM.SU5.FiniteGaugeData.Marked.Grammar

/-!
# Bounded entries for the wave fee + stencil form of the mode substitutions
@softer than tariffing the whole Fock CM operator cross-period
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Fock Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window
attribute [local instance] opCStarAlgebra

abbrev spinSlot:= SpinIdx × SU.Slot
private noncomputable abbrev align (n:Type*)[d:DecidableEq n](l:LinearOrder n): LinearOrder n:={l with
 toDecidableEq := d
 compare_eq_compareOfLessAndEq :=by
   letI : LinearOrder n:=l; have hp:d=l.toDecidableEq:=Subsingleton.elim _ _; rw [hp]; exact l.compare_eq_compareOfLessAndEq}
local instance :LinearOrder spinSlot:= align _ (LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective)
def nick (N:Side)(x:Site N):spinSlot ↪ Single N:=
 ⟨fun y=> ((x,y.1),y.2),by rintro ⟨i,b⟩ ⟨j,l⟩ h; simpa using h⟩

def chamberW (Q:Op SU.Slot):Op spinSlot := (Fir.Aop-(1/2:ℂ) • 1) ⊗ₖ Q
@[fun_prop] lemma cwCont : Continuous chamberW:= by
 unfold chamberW; apply continuous_matrix
 rintro ⟨i,b⟩ ⟨j,x⟩; dsimp; fun_prop
set_option maxRecDepth 4000 in
set_option maxHeartbeats 350000 in
lemma block_plank (N:Side)(x:Site N)(Q:Op SU.Slot)(v:Ket spinSlot):
 coat (nick N x) (acts (chamberW Q) v)= acts (plankP N Q) (coat (nick N x) v):=by
 nth_rw 1 2 [←basis_expand v]; simp_rw [map_sum,map_smul,basis_shell]
 apply sum_congr rfl; rintro ⟨i,j⟩ _; apply congrArg
 apply PiLp.ext; intro w
 obtain ⟨⟨y,x'⟩,k⟩:=w
 rw [basis_act]; by_cases h:x=y
 · subst y; let t:= acts (chamberW Q) (basisKet (show spinSlot from (i,j))); let H:=nick N x
   have he(a:spinSlot): (coat H t).ofLp (H a)=t.ofLp a:=by rw [←seamK,trails];
   calc
    _ = t.ofLp (x',k):= he (x',k)
    _ = chamberW Q (x',k) (i,j):=basis_act ..
    _ = plankP N Q ((x,x'),k) (H (i,j)):=by change _= jump (Equiv.refl _) (fun _:Site N=> chamberW Q) (x,x',k) (x,i,j); simp [jump_apply]
 rw [basin]
 · change _= jump (Equiv.refl (Site N)) (fun _=> chamberW Q) (y,x',k) (x,i,j); rw [jump_apply,Equiv.refl_apply,if_neg (Ne.symm h)]
 intro e; obtain ⟨⟨a,c⟩,-,p⟩:=Finset.mem_map.mp e
 change ((x,a),c)=_ at p; simp [h] at p

def roomF (b:Bool)(Q:Op SU.Slot):Op spinSlot:= if b then exp (chamberW Q) else exp (-chamberW Q)
lemma roomCont (b:Bool):Continuous (roomF b):= by letI : NormedAlgebra ℚ (Op spinSlot):=NormedAlgebra.restrictScalars ℚ ℂ _; unfold roomF; cases b; exact (exp_continuous.comp cwCont.neg); exact exp_continuous.comp cwCont
lemma fee_place (N:Side)(x:Site N)(b:Bool)(Q:Op SU.Slot)(v:Ket spinSlot) :
 coat (nick N x) (acts (roomF b Q) v)= acts (feeL b N Q) (coat (nick N x) v):=by
 cases b
 · apply Mail.on_exp _ _ v
   intro x'; rw [act_neg,act_neg,map_neg,block_plank]
 exact Mail.on_exp _ (block_plank N x Q) v
lemma fee_vector (N:Side)(x:Site N)(b:Bool)(Q:Op SU.Slot)(i:spinSlot):
 acts (feeL b N Q) (basisKet (nick N x i))=∑ j:spinSlot, roomF b Q j i • basisKet (nick N x j):=by
 rw [←basis_shell,←fee_place]
 nth_rw 1 [←basis_expand (acts _ _)]
 simp_rw [basis_act,map_sum,map_smul,basis_shell]
lemma room_bound (d:ℝ): ∃ l:ℝ, 0≤l ∧ ∀ Q:Op SU.Slot, ‖Q‖ ≤ d → ∀ b i j, ‖roomF b Q i j‖ ≤ l:=by
 have h(b:Bool):∃ l:ℝ,0≤l∧∀ Q:Op SU.Slot,‖Q‖≤d→∀ i j, ‖roomF b Q i j‖≤l:=by
    obtain ⟨k,w⟩:= ((ProperSpace.isCompact_closedBall (0:Op SU.Slot) d).image ((roomCont b).norm)).bddAbove; exact ⟨max k 0,le_max_right ..,fun Q p i j=> (norm_entry ..|>.trans (w ⟨Q,mem_closedBall_zero_iff.mpr p,rfl⟩)).trans (le_max_left ..)⟩
 obtain ⟨m,M,u⟩:=h false; obtain ⟨n,N,v⟩:=h true; refine ⟨m+n,by linarith,fun Q p b i j=>?_⟩; cases b
 · exact (u Q p ..).trans (by linarith)
 exact (v Q p ..).trans (by linarith)
#print axioms room_bound
