import YM.SU5.SatinWard.Resolution.Glare
import Anomaly.Ward.Raw
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Buffered Salt
-- Circ on Pane too: note one mesh q, areal. shared mask for tax (inc bar subtraction)
-- and for each chir ingredient.
variable {P T:SOp N} {p:BudgetPoint}{K:Scree.Loom N}{t u:ℝ}{k q:ℕ}
open Urn

namespace Chamber
section proof
variable (bI:Division)(K:Scree.Loom N)(p:BudgetPoint)(k:ℕ)(w:ℝ)(x:Site N)(E:Pattern P T r d a v)
local notation "Â"=> skyHat bI x E K p k
local notation "J"=> centHat bI x E K p k
local notation "Λ"=> (tickA N)
variable (z:Checked p K t d a k q)
include z
local notation "χ"=> beforePing (grantA bI E x) k
local notation "ι★"=> live K p k x (grantA bI E x)
-- type budgets.Boot Kernel exact even charge.Sign.
open QuadClock
open Sonar
lemma walk_plate (U:Pane N) (pU:Guard U d)(u:pingS p.threshold (offsetMask p.B x) U) : skyHat bI x E K p k U= χ (profile U):=by
 let Q':Openc (More N) d:=⟨_,insideQ (n:=N) ⟨_,pU⟩ z.angle⟩; let p':Orbit N:=⟨U,Classical.arbitrary _⟩
 change ι★ p'.1= _; let T:moored (node x) (grantA bI E x):= E.moorA x; rw [noTag _ (grantA bI E x) z T, if_pos (show pingS _ _ _ from u)]; exact runs _ _ z T p' u U Q' rfl (fun _ _ _ _ _ _ _ _=> rfl)
omit z in
lemma sky_correct (U:Pane N): skyHat bI x E K p k U=pinMatrix p K (node x) χ U:=rfl
lemma sky_herm (U:Pane N): star (skyHat bI x E K p k U)= skyHat bI x E K p k U:=by
 let V:Orbit N:=⟨U,Classical.arbitrary _⟩
 let h:= E.hatted z x V -- check order
 change star (live K p k x (income bI (E.A x)) V.1)= _
 unfold skyHat grantA; rw [live_at]; change star (hall bI _) = hall bI (live K p k x (E.A x) V.1)
 unfold hall; rw [star_mul,star_mul,seal_star, h.star_eq, mul_assoc]
lemma idleAspect : rawQ χ 1=0:=by
 obtain ⟨s,t,h,t'⟩:= poseAll (n:=N) (Signed.mirror 1) x x; have hp:pose s x=x:= (earlier_mills ..).mp t'.backward
 let X:Fields N:=⟨1,1⟩; have he: s.charge=false:=h; have ht:det_S s=true:=by unfold det_S; rw [t,det_t]
 have hb:flashA s 1=1:=by ext1 i; unfold flashA stir; simp only [Function.comp_apply,Lattice.pull,Step.read,Pi.one_apply]; simp
 let F:= skyHat bI x E K p k; have h:= poses_gauge bI x z E s X X (show X.1=flashA s X.1 from hb.symm)
 rw [hp] at h; change lotB s.charge _ _ ((F 1).trace • 1)=Scroll.hush (det_S s) ((F 1).trace • 1) at h; rw [visage,map_one,he,ht,hush_true] at h
 have hh:star (F 1).trace= (F 1).trace:= by rw [← Matrix.trace_conjTranspose]; exact congrArg Matrix.trace (sky_herm bI _ _ _ x E z 1)
 rw [show cSignX (Bool.xor false true) (F 1).trace=(F 1).trace from hh,←neg_smul] at h
 have hv: (F 1).trace= 0:= neg_forces _ (smul_left_injective ℂ (by simp : (1:FC I)≠0) h)
 change Matrix.trace (χ (profile 1))=_; rw [← walk_plate bI _ _ _ x E z _ (guard0 z.angle.le) (ping_f p _)]; exact hv
end proof
end Chamber
end YM.CF.LitCurrent
