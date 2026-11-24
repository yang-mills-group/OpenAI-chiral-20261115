import YM.SU5.SatinWard.Resolution.Floribunda
import YM.SU5.SatinWard.Resolution.GrainMap
import YM.CF.Moire.Niche
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical Kronecker
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "Γ" => Single N
open Buffered _root_.Zephyr.Chern
open IndexMag Chamber Surplus
namespace AuroraX
local notation "I"=> _root_.Zephyr.Chern.IS
open Laurent
variable (D:Division)
variable {P T:SOp N}(E:Pattern P T r d a v)
local notation "Z₁"=>Openc (More N) d
open Salt
variable (h:0<d) (x y:Cover)
noncomputable def mintN (N:Side)(h:0<d): Openc (More N) d:=⟨profile 1,(show profile (1:Pane N)∈_ from profile_trivial (N:=More N) ▸ vacancy0 d h)⟩ -- ∈
noncomputable abbrev fullScreen (o:Cover)(i:Axis): Op (Single N):= fullL D E (wrap N o) (mintN _ h) (i,false)
noncomputable def fullnx (i:Axis): Op I:= shore N x y (fullScreen D E h 0 i)
lemma recoverFull (z:Cover)(i:Axis):fullnx D E h (x-z) (y-z) i= shore N x y (fullScreen D E h z i):=by
 unfold fullnx; let q:=sky_zero D E (mintN _ h) rfl (i,false) (x-z) (y-z) 0 z; dsimp only at q; rw [sub_add_cancel,sub_add_cancel,zero_add] at q; exact q
variable (h₁:Solo a c P d)(h₂:Solo a c T d)(h3:T 1=0)(q:BudgetPoint)(p:0<a)
lemma liveTops {S':Scree.Loom N}{t:ℝ}{q:BudgetPoint}{k g:ℕ} (z:Checked q S' t d a k g) (w:Axis) : centHat D (wrap N 0) E S' q k (w,false) 1=beforePing (grantJ D E (wrap N 0,(w,false))) k (profile 1):=by
 let V:Orbit N := (1,Classical.arbitrary _); let e:=grantJ D E (wrap N 0,(w,false)); have hu:moored (node (wrap N 0)) e:=(E.moorJ (wrap N 0,(w,false))); change live _ _ _ _ e V.1=_; rw [noTag _ e z hu]; have ht:pingS q.threshold (offsetMask q.B (wrap N 0)) V.1:=ping_f q _; rw [if_pos ht]; exact runs _ e z hu V ht 1 (mintN _ z.angle) rfl (fun _ _ _ _ _ _ _ _=>rfl)
local notation "Θ" z:max u:max F:max=> shore N z u F
local notation "G" o:max x:max y:max j:max=> fullnx D E h (x-o) (y-o) j
-- ling. use Trem.O.(some W). hold valuation. cost statement per poll. now pre.F.D.Cal.Axis at N any.
include h₁ h₂ h3
lemma tarGlow (x y o:Cover) : let r':=r; let Ψ(o:Cover)(i:Axis):= fullnx D E h (x-o) (y-o) i
 (∑ i: Axis,(Ψ (o+r' • step i) i-Ψ (o-r' • step i) i))= shore N x y (Sault.inward (P (profile 1)) (hall D (roomW (wrap N o) r)) 0):=by
 let Q:= mintN N h; have hp: Q.val=profile 1:=rfl; have h: Guard (1: Pane N) d:= guard0 h.le; have g:= salaryC D (wrap N o) E Q 1 h hp h₁ h₂
 intro e F
 rw [curl_permit (p:=?_)] at g; swap; · exact fun x i=>bulkFlip D E x Q hp i
 rw [show (0:Op Γ)=T Q.val from (by rw [hp,profile_trivial,h3]), ←hp,←g,map_sum]; refine sum_congr rfl fun i _=>?_ -- map.Sub etc
 rw [map_sub]; unfold F; rw [recoverFull, recoverFull]; unfold fullScreen fullL; rw [map_add,map_nsmul,wrap_step,map_sub,map_nsmul,wrap_step]
#print axioms tarGlow
local notation "τ" β:max=>LitCurrent.expiry (4*a) β
omit h₁ h₂ h3
include h p
omit h in
lemma pearl_pos (Q:StageTree N d (4*a) v){o:Seat N}(w:moored o Q) :0≤ LitCurrent.expiry (4*a) v := soakCostNN (totals Q p w 0).1.pay
include h p
lemma peakBarrier (i:Axis)(U:Lattice.lift (wrap N x)=x)(V:Lattice.lift (wrap N y)=y) : ‖fullnx D E h x y i‖ ≤ faithMoney (LitCurrent.expiry (4*a) v)*expNote a x y:=by
 let F:= grantJ D E (wrap N 0,(i,false)); have g:moored (node (wrap N 0)) F:= E.moorJ (wrap N 0,(i,false)); let S:= (mintN N h); have hz:= minuteAge (Real.exp (-a * ↑(0:ℕ))*expiry (4*a) v) x y U V ((totals F p g 0).2: Soak (node (wrap N 0)) (beyond F 0) a _ d ) p S
 rw [beyond,dif_pos S.property] at hz; rw [show retain F 0 S=0 from (by simp only [retain,Nat.not_lt_zero, if_false, sum_const_zero]), sub_zero] at hz; change ‖shore N x y (sky F S)‖ ≤_; simpa only [Nat.cast_zero,mul_zero,neg_zero, Real.exp_zero,one_mul] using hz
variable (S': Scree.Loom N){t:ℝ}{k g:ℕ} (z:Checked q S' t d a k g)
include z
lemma peakBridge (i:Axis)(U:Lattice.lift (wrap N x)=x)(V:Lattice.lift (wrap N y)=y) : ‖fullnx D E h x y i-shore N x y (centHat D (wrap N 0) E S' q k (i,false) 1)‖ ≤ (Real.exp (-a*k)*faithMoney (LitCurrent.expiry (4*a) v))*expNote a x y:=by
 let F:= grantJ D E (wrap N 0,(i,false)); have gh:moored (node (wrap N 0)) F := E.moorJ (wrap N 0,(i,false)); let S:= mintN N h; have hz:shore N x y (beyond F k S.val)=fullnx D E h x y i-shore N x y (centHat D (wrap N 0) E S' q k (i,false) 1):=by
    rw [liveTops D E z i]; change _ = shore N x y (sky F S)-shore N x y (beforePing F k S.val); rw [←map_sub, saw_recover F k S|>.symm,add_sub_cancel_left]
 rw [←hz,←faith_scale]; exact minuteAge _ x y U V (totals F p gh k).2 p S
#print axioms peakBridge
end AuroraX
end YM.CF.LitCurrent
