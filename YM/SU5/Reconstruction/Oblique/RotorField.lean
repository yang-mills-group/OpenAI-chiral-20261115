import YM.SU5.Reconstruction.Oblique.Tilt
/-! # changing Tilt on the actual finite labels -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Tilted
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance
  Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin SatinVerification
namespace Ramp
open Reed (Fine)
variable {N : Side}(P:Ramp)

-- actual Shape (plan) on both direct (gauge) and matter via shifted nodes
lemma mode_motion (x:Cover): P.plan.motion x=P.s.act x:= by simp [plan,Shape.motion,incX]
lemma act_act {X:Type*}[AddGroup X](x:Four X):P.s.act (P.s.act x)=x:=by rw [←Signed.act_mul,P.swing,Signed.act_one]
lemma modes_m (x:Cover):P.plan.motion (P.plan.motion x)=x:= by rw [P.mode_motion,P.mode_motion,P.act_act]
lemma moved_wing (x:Cover): P.plan.motion (nodeC x)=nodeC (P.plan.flee x):= P.plan.mote x
lemma fend (x:Cover): P.plan.flee (P.plan.flee x) =x:= by
 apply nsmul_right_injective (M:=Cover) (show (2:ℕ)≠0 by decide); change (2:ℕ)•_=2•_
 apply add_right_cancel (b:= (_:Cover)) (show (2:ℕ) • P.plan.flee (P.plan.flee x)+1=2•x+1 from by rw [←Shape.mote, ←Shape.mote,P.modes_m])
lemma fence (x: Site N):P.plan.mills N (P.plan.mills N x)=x:= by rw [←Rush.nat_true x,Shape.mill,Shape.mill, P.fend]
lemma fenceG (x: Site (More N)): P.plan.anon N (P.plan.anon N x)=x:=by rw [←Rush.nat_true x,Shape.anno,Shape.anno,P.modes_m]

abbrev vehicle (P:Ramp)(N:Side) := prepU P.plan P.reel inert N
abbrev turnLink (P:Ramp)(N: Side): Pane N→ Pane N:= Yg P.plan
def both (P:Ramp)(N:Side) := Prod.map (P.turnLink N) (P.turnLink N)
def bill (P:Ramp) (f: Mark N) : Mark N := fun y=> Fock.theta (P.vehicle N) (f (P.both N y))
lemma turn_pull (N:Side): P.turnLink N = pull P.s (0: Site (More N)) := by
 change pull P.s (wrap (More N) (2 • P.plan.t))= _; rw [show P.plan.t=0 from rfl, smul_zero,map_zero] -- implicit K links universe type
lemma turnover (x:Pane N): P.turnLink N (P.turnLink N x)=x:= by unfold turnLink; rw [←kor,P.replan,Nacre.blank]
lemma link_cont (N:Side): Continuous (P.turnLink N):= by rw [P.turn_pull]; exact Wilson.continuous_pull ..
lemma retrace (x:Fields N): P.both N (P.both N x)=x:=Prod.ext (P.turnover _) (P.turnover _)
lemma pin_car (N:Side): (P.vehicle N).val * (P.vehicle N).val = -1:=by
 change (P.vehicle N*P.vehicle N).val=_; rw [vehicle,kio,P.replan]; have h:(P.reel*P.reel).val= (-1:ℂ) • (1:UNI SpinIdx).val:= by rw [neg_one_smul]; exact P.squarish
 rw [Ygs _ _ 1 h,prep_one,neg_one_smul]; rfl
lemma exchanges (N:Side): twist (P.vehicle N) (cutM (Tset N)ᶜ)=cutM (Tset N):=by
 have h: twist (P.vehicle N) (cutM (Tset N)) =1-cutM (Tset N):= tickR P.plan inert P.reel P.jet N
 rw [dim_cut,map_sub,map_one,h]; abel
lemma swings_modes (S:Support (More N)): twist (P.vehicle N) (cutM (modesIn N S))=cutM (modesIn N (S.image (P.plan.anon N))):=by
 apply prep_moves; intro x; constructor
 · rintro h; obtain ⟨_,p,rfl⟩:=mem_image.mp h; rwa [P.fenceG]
 exact fun p=>mem_image.mpr ⟨_,p,P.fenceG _⟩
variable {b:Bool}{S:Support (More N)}{f:Mark N}
lemma sectorCharge (T:Support (More N))(u:FC (Single N))(v:Fine (Tset N) (modesIn N T) b u):Fine (Tset N) (modesIn N (T.image (P.plan.anon N))) b (Fock.theta (P.vehicle N) u):= Reed.Fine.arrive (P.swings_modes T) (P.exchanges _) v
-- Density/exact bill at this volume
lemma term_marked (p:AtSupport b S f):AtSupport b (S.image (P.plan.anon N)) (P.bill f) :=
  ⟨ Girt.pole_w (fun V=>f (P.both N V)) (Fock.theta (P.vehicle N)) (theta_cont (P.vehicle N)) (Env.along p.env (Continuous.measurable (Continuous.prodMap (P.link_cont N) (P.link_cont N)))),fun x y u v=>congrArg (Fock.theta (P.vehicle N)) (p.dep (P.both N x) (P.both N y) (Yg_agrees _ _ u) (Yg_agrees _ _ v)), fun _=>P.sectorCharge S _ (p.allV _)⟩
lemma term_twice (p:AtSupport b S f): P.bill (P.bill f)=f:=by funext y; simp only [bill,P.retrace]; exact Fock.theta_twice _ (P.pin_car N) (p.allV _).sector
lemma vehicle_cost (y:FC (Single N)): ‖Fock.theta (P.vehicle N) y‖=‖y‖:=by rw [Fock.theta,twist_norm,Scroll.norm_cc] -- tune norm_cc
lemma comm_gauge (g:Seat N→ E): P.vehicle N * tradew N (g ∘ P.plan.anon N)=tradew N g* P.vehicle N:=by
 unfold vehicle; rw [envoy]; rw [show (g ∘ P.plan.anon N) ∘ P.plan.anon N=g from funext fun x=>congrArg g (P.fenceG x)] -- tune
lemma term_cov (h:AtSupport b S f)(v:covariant f): covariant (P.bill f):=by
 intro g x; unfold bill; let g':=g ∘ P.plan.anon N; rw [show P.both N (simultaneous g x)= simultaneous g' (P.both N x) from Prod.ext (van ..) (van ..), v]; exact theta_twist_right _ _ _ (congrArg Subtype.val (P.comm_gauge g)) (h.allV _).sector
end Ramp
end YM.CF.Buffered.Afterglow.Tower.Tilted
