import YM.SU5.Reconstruction.Hygrometry.Upward
import YM.SU5.Reconstruction.Hygrometry.Reflecting
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
open Mir Reflect RP Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open PriceCliff
variable {α : Type*} {N m B:Side} {S:ℕ→Side}{R:ℕ→ℝ}
-- exported units Gaia, shape exactly in node convention. Dist plane positive.
lemma atlas_tend {F:ℕ→Gaia} {x: Gaia}: Tendsto F atTop (𝓝 x) ↔ ∀ j:Axis,Tendsto (fun i:ℕ=> F i j) atTop (𝓝 (x j)) := by
 constructor
 · intro h i; refine (show Continuous fun x:Gaia=>x i from (by fun_prop)).continuousAt.tendsto.comp h
 intro f; exact ((show Continuous fun z : Axis→ℝ => WithLp.toLp 2 z from PiLp.continuous_toLp ..).tendsto (Stationary.exileE x)).comp (show Tendsto (Stationary.exileE ∘ F) atTop (𝓝 (Stationary.exileE x)) from tendsto_pi_nhds.mpr f)

def traceV (R:ℝ)(x:Cover): Gaia := WithLp.toLp 2 fun i=>((x i :ℝ)+1/2)/R
lemma trace_iff (Y:Yard S R)(s:ℕ→ Cover)(x: Gaia) : Tendsto (fun i=> traceV (R i) (s i)) atTop (𝓝 x) ↔ Tendsto (fun i=>riseX (R i) (s i)) atTop (𝓝 x):=by
 rw [atlas_tend,atlas_tend]; apply forall_congr'; intro a
 let G(i:ℕ):=(1/2:ℝ)/R i; have hg:Tendsto G atTop (𝓝 0):= Y.thinner _; constructor <;> intro h
 · refine (sub_zero (x a) ▸ h.sub hg).congr fun i=>?_ ; change ((s i a:ℝ)+1/2)/R i-(1/2)/R i=_; rw [add_div,add_sub_cancel_right]; rfl
 refine (add_zero (x a) ▸ h.add hg).congr fun i=>?_; exact (add_div ..).symm
noncomputable def land_axis (a:Axis)(x:Gaia): Gaia:= WithLp.toLp 2 fun i=> if i=a then -x i else x i
noncomputable def land_tilt (P:Ramp)(x:Gaia): Gaia:= WithLp.toLp 2 (P.s.act x.ofLp)
def face_axis (a:Axis)(x: Gaia) : Prop:= 0<x a
def face_tilt (P:Ramp)(x:Gaia): Prop:=0<x P.a+x P.b
lemma here_axes (a:Axis)(r:ℝ)(x:Cover): traceV r ((applaud a).cell x)= land_axis a (traceV r x):=by
 apply PiLp.ext; intro b; change ((_ + 1/2)/r:ℝ) = if b=a then -_ else _; change ((↑((Buffered.plane a 0).flee x b):ℝ) + 1/2)/r= _; rw [Lifted.flee_pos]; by_cases p:a=b
 · rw [if_pos p,if_pos p.symm]; push_cast; change _ = -(((x b:ℝ)+1/2)/r) -- a=b but x b?
   ring
 rw [if_neg p,if_neg (Ne.symm p)]; rfl
lemma here_tilts (P:Ramp)(r:ℝ)(x:Cover): traceV r ((whisper P).cell x)=land_tilt P (traceV r x) := by
 let t:=P.plan.flee x; have ht: nodeC t=P.s.act (nodeC x):= (P.mode_motion (nodeC x)) ▸ (Shape.mote P.plan x).symm
 have hκ (x:Cover)(i:Axis): traceV r x i=(nodeC x i:ℝ)/(2*r):=by change ((x i:ℝ)+1/2)/r=_; rw [show nodeC x i=2*x i+1 from (by unfold nodeC; simp)]; push_cast; ring
 apply PiLp.ext; intro i; have he := congrFun ht i; change traceV r t i= _; rw [hκ]; change _= P.s.act (traceV r x).ofLp i; rw [he]; by_cases p:i=P.a
 · subst i; rw [P.move_a,P.move_a]; push_cast; simp_rw [show (traceV r x).ofLp P.b=_ from hκ ..]; ring
 by_cases u:i=P.b; · subst i; rw [P.move_b,P.move_b]; push_cast; simp_rw [show (traceV r x).ofLp P.a=_ from hκ ..]; ring
 rw [P.move_h _ p u,P.move_h _ p u]; exact (hκ x i).symm
lemma lands_axis (a:Axis) (F:ℕ→Gaia){x:Gaia}(p:Tendsto F atTop (𝓝 x)): Tendsto (land_axis a ∘ F) atTop (𝓝 (land_axis a x)):=by
 apply atlas_tend.2; intro i; change Tendsto (fun n=> if i=a then -(F n i) else F n i) _ _; by_cases h:i=a
 · change Tendsto _ _ (𝓝 (if i=a then -x i else x i)); simp_rw [if_pos h]; exact (atlas_tend.1 p i).neg -- tune
 change Tendsto _ _ (𝓝 (if i=a then -x i else x i)); simp_rw [if_neg h]; exact atlas_tend.1 p i
lemma lands_tilt (P:Ramp) (F:ℕ→Gaia){x:Gaia}(p:Tendsto F atTop (𝓝 x)): Tendsto (land_tilt P ∘ F) atTop (𝓝 (land_tilt P x)):=by
 apply atlas_tend.2; intro i; change Tendsto (fun n=>P.s.act (F n).ofLp i) atTop (𝓝 (P.s.act x.ofLp i)); by_cases h:i=P.a; · subst i; simp_rw [P.move_a]; exact (atlas_tend.1 p P.b).neg
 by_cases v:i=P.b; · subst i; simp_rw [P.move_b]; exact (atlas_tend.1 p P.a).neg
 simp_rw [show ∀ z:Four ℝ,P.s.act z i=z i from fun z=> P.move_h z h v]; exact atlas_tend.1 p i

noncomputable def posted (A:ActMark) (P:α→ Cover):α ⊕ α→ Cover:= Sum.elim (A.cell ∘ P) P
-- make axis & tilt extension Agenda around right.Starts frame conditions
private lemma diskReady (A: ActMark)(F:Gaia→Gaia)(Y:Yard S R)(P:Agenda α R)(H:∀ x y:α,P.posV x≠F (P.posV y)) (r:Injective F)(g:∀ (x:ℕ→ Gaia){v}, Tendsto x atTop (𝓝 v)→ Tendsto (F ∘ x) atTop (𝓝 (F v)))(h:∀ r x, traceV r (A.cell x)=F (traceV r x)): Nonempty {C:Agenda (α⊕α) R // C.posV=Sum.elim (F ∘ P.posV) P.posV ∧ C.appointments=fun i=>posted A (P.appointments i)}:=by
 let x (n:ℕ) (i:α) := traceV (R n) (P.appointments n i); let u: Agenda (α⊕α) R:=⟨Sum.elim (F ∘ P.posV) P.posV,fun i=>posted A (P.appointments i),?_,?_⟩
 exact ⟨u,rfl,rfl⟩
 · rintro (i|i); swap; exact P.timeR _
   apply (trace_iff Y ..).1; change Tendsto (fun n=> traceV (R n) (A.cell _)) atTop (𝓝 _); simp_rw [h]; exact g _ ((trace_iff Y _ _).2 (P.timeR i)) -- def comp arg
 · rintro (i|i) (j|j) p; exact (P.tied _ _ (r p)).mono fun n u=> congrArg A.cell u; exact (H _ _ p.symm).elim; exact (H _ _ p).elim; exact P.tied i j p
noncomputable def nextTilt (P: Agenda α R)(U:Ramp)(e:Yard S R)(h:∀ i,face_tilt U (P.posV i)): {Q:Agenda (α⊕α) R // Q.posV=Sum.elim (land_tilt U ∘ P.posV) P.posV ∧ Q.appointments=fun i=>posted (whisper U) (P.appointments i)} := Nonempty.some <| diskReady _ _ e P (fun i j v=>by
    have he:=congrArg (fun x:Gaia=> x U.a + x U.b) v; change _= U.s.act _ _ + U.s.act _ _ at he; rw [U.move_a, U.move_b] at he; have hp:i=i:=rfl; have hb:=h i; have hx:=h j; unfold face_tilt at hb hx; change (_:ℝ)= -(P.posV j U.b)+-(P.posV j U.a) at he ; linarith) (fun i j h=> PiLp.ext (fun z=> congrFun ((U.s.actEquiv (R:=ℝ)).injective (show U.s.act i.ofLp=U.s.act j.ofLp from congrArg (fun x:Gaia=>x.ofLp) h)) z)) (lands_tilt U) (here_tilts U)
noncomputable def nextAxis (P: Agenda α R)(a:Axis)(e:Yard S R)(h:∀ i,face_axis a (P.posV i)): {Q:Agenda (α⊕α) R // Q.posV=Sum.elim (land_axis a ∘ P.posV) P.posV ∧ Q.appointments=fun i=>posted (applaud a) (P.appointments i)} := Nonempty.some <| diskReady _ _ e P (fun i j v=>by have he:=congrArg (fun x:Gaia=> x a) v; change (P.posV i) a= (if a=a then -(P.posV j a) else _) at he; rw [if_pos rfl] at he; linarith only [he, show 0<P.posV i a from h i, show 0<P.posV j a from h j]) (fun i j h=> by
 apply PiLp.ext; intro z; have he:=congrArg (fun x:Gaia=> x z) h; change (if z=a then -_ else i z) = if z=a then -_ else j z at he; split_ifs at he <;> first | exact he | exact neg_injective he) (lands_axis a) (here_axes a)
end YM.CF.Hygrometry
