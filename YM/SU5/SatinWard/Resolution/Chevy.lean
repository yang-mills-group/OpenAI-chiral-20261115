import YM.SU5.LitCurrent.Reached
import YM.SU5.SatinWard.Resolution.Trachea
import YM.SU5.LitCurrent.Copy
import YM.CF.Prism.Gale
-- Cut the very assigned kernels to a trace sector. Preserves all Suite costs.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
-- true for tens. accept all on none for joint pricing
namespace Chamber
variable {N:Side}{P T:SOp N} {p:BudgetPoint}{a b d v:ℝ}{r:ℕ}
variable (U:Division)(x:Site N)(E:Pattern P T r d a v)
local notation "I"=> Single N
local notation "ξ"=> markG U N
open Buffered Salt
private lemma curtain (S:Finset (Single N)): Commute ξ (cutM S):=by
 unfold markG cutM Commute SemiconjBy; rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; congr 1; ext; exact mul_comm ..
lemma ticketA : Commute ξ (tickA N):=by rw [touchP]; apply curtain
lemma traffic (r:ℕ): Commute (tickA N) (hall U (roomW x r)):= ((ticketA U).symm.mul_right (rooms_pay x r)).mul_right ((ticketA U).symm)
lemma transparent (R:ℕ)(V:8*r≤R) :
    let L:=cutM (modesIn N (offsetMask R x)); L * hall U (roomW x r) * L= hall U (roomW x r):= by
 intro h; apply cut_scope; intro i j w; apply scope_cut (room_local x _ _ V); intro g; rw [hallAt,g] at w; simp at w
lemma tStar : star (hall U (roomW x r))=hall U (roomW x r):=by unfold hall; rw [star_mul,star_mul,seal_star,room_star,mul_assoc] -- direction tune
lemma hallRight (K H:Op I)(h:Commute ξ H): hall U (K*H)=hall U K * H:=by unfold hall; rw [mul_assoc _ ξ H,h.eq]; simp only [mul_assoc] -- tune
lemma hallLeft (H K:Op I)(h:Commute ξ H): hall U (H*K)=H*hall U K:=by unfold hall; rw [←mul_assoc ξ,h.eq]; simp only [mul_assoc]
lemma hallPlus (X Y:Op I): hall U (X+Y) =hall U X+hall U Y:=by simp [hall,mul_add,add_mul]
lemma hallMinus (X Y:Op I): hall U (X-Y)=hall U X-hall U Y:=by simp [hall,mul_sub,sub_mul]
variable (W:Openc (More N) d) (V:Pane N) (g:Guard V d) (u:W.val=profile V)
variable (pP: Solo a b P d)(pT:Solo a b T d)
include u
private lemma tiV {S:SOp N} (m:Solo a b S d): Commute (markG U N) (S W.val):=by rw [u]; exact sits U V m (u ▸ W.property) -- simp
omit u
abbrev income (U:Division) (A:StageTree N d a v) : StageTree N d a v:=
 ⟨fun i _ x=>hall U (A.F i () x), A.W, fun i=>⟨fun _=> suite U ((A.coat i).1 ()), fun _=>continuous_const⟩,A.bank⟩ -- include E may unwanted
abbrev grantA (x:Site N):= income U (E.A x)
abbrev grantJ (y:Ensemble N):= income U (E.J y)
lemma stack (A:StageTree N d a v) :sky (income U A) W=hall U (sky A W):=by unfold sky hall; rw [Finset.mul_sum,Finset.sum_mul]
include pP u
lemma shadow : Commute ξ (P W.val):=tiV _ _ _ u pP
include pT
lemma scepter : Commute ξ (capT (P W.val) (T W.val)):= (( (Commute.one_right _).sub_right (shadow _ _ _ u pP)|>.mul_right (tiV _ _ _ u pT)).mul_right (shadow _ _ _ u pP)) -- tune he uses pP u
lemma gainP (Z:Op I): hall U (Sault.inward (P W.val) Z (T W.val))= Sault.inward (P W.val) (hall U Z) (T W.val):=by
 let X:=P W.val; let K:=T W.val; have hp:=shadow U W V u pP; have ht:=scepter U W V u pP pT; let hg:Commute ξ (1-P W.val):=(Commute.one_right _).sub_right hp
 unfold Sault.inward blockD; rw [hallMinus,hallRight U _ _ ((Commute.one_right _).sub_right ht),hallLeft U _ _ ((Commute.one_right _).add_right ht),hallPlus,hallRight U _ _ hp,hallLeft U _ _ hp,hallRight U _ _ hg,hallLeft U _ _ hg]
omit pP u pT
-- aliases to adapted Pattern.Supplied on root.
include g u pP
lemma shadows (r':ℕ)(z:r'=r): -- notation r avoid ambiguity
    Matrix.trace (sky (grantA U E x) W)= Matrix.trace ((P W.val - tickA N)* hall U (roomW x r')):=by -- arg order?
 subst r'; let A:=tickA N; let L:= P W.val-A; let H:=hall U (roomW x r); let v:Commute ξ L:=(shadow U W V u pP).sub_right (ticketA U)
 change Matrix.trace (sky (income U (E.A x)) W)=_; rw [stack,← E.tax x V g W u]; unfold taxKernel
 rw [show hall U ((2:ℂ)⁻¹ • (L*roomW x r + roomW x r*L))=(2:ℂ)⁻¹ • (L*H + H*L) from ?_,Matrix.trace_smul,Matrix.trace_add,Matrix.trace_mul_comm H,smul_eq_mul]; change _=Matrix.trace (L*H); ring -- X
 rw [show hall U ((2:ℂ)⁻¹ • (L*roomW x r + roomW x r*L))=(2:ℂ)⁻¹ • (hall U (L* roomW x r+roomW x r* L)) from by unfold hall; rw [Matrix.mul_smul,Matrix.smul_mul]]; rw [hallPlus,hallLeft U _ _ v,hallRight U _ _ v]
include pT
lemma salaryC : bears (fun x i=>sky (grantJ U E (x,i)) W) r x= Sault.inward (P W.val) (hall U (roomW x r)) (T W.val):=by
 unfold grantJ bears; simp_rw [stack]; rw [←gainP U W V u pP pT]; have hv:=E.chimeJ x V g W u; unfold bears at hv;
 -- pull sum
 conv_rhs=>rw [←hv]; unfold hall; rw [Finset.mul_sum,Finset.sum_mul]
omit pT pP g u
section secondary
variable (K:Scree.Loom N)(p:BudgetPoint)(k:ℕ)(w:ℝ)
local notation "S"=>offsetMask p.B x
noncomputable def skyHat : Pane N→Op I:=live K p k x (grantA U E x)
noncomputable def centHat (e:FaceDir): Pane N→ Op I:=live K p k x (grantJ U E (x,e))
local notation "Â"=> skyHat U x E K p k
local notation "J"=> centHat U x E K p k
local notation "Λ"=> (tickA N)
def jewelY : Mark N:=fun V=> Matrix.trace (Â V.1) • 1
def jewelJ (e:FaceDir): Mark N:=fun V=> preHalf w Λ (J e V.1)
noncomputable def jewelO : Mark N:= jewelY U x E K p k+ ∑ e:FaceDir,jewelJ U (destSite x r e) E K p k w e
noncomputable def jewelExcess (r:ℕ): Mark N:= fun V => if pingS p.threshold (offsetMask p.B x) V.1 then
    dg (hall U (roomW x r))- Matrix.trace ((tickA N)* hall U (roomW x r)) • 1 else 0
def jewelLeg (e:FaceDir): Mark N:=fun V=> liftHalf w (J e V.1)
def jewelT : Mark N:= jewelY U x E K p k+ ∑ e:FaceDir,jewelLeg U (destSite x r e) E K p k w e - jewelExcess U x p r
-- commute cutting with live. Useful proof. Robust.
lemma live_at {T:StageTree N d (4*a) v} (W:Pane N): live K p k x (income U T) W = hall U (live K p k x T W):=by -- needs h? uses mask cert free by def
 unfold live; by_cases e:pingS p.threshold (offsetMask p.B x) W; swap; · rw [Set.indicator_of_notMem (show W∉_ from e),Set.indicator_of_notMem (show W∉_ from e)]; simp [hall]
 rw [Set.indicator_of_mem (show W∈_ from e),Set.indicator_of_mem (show W∈_ from e)]; unfold beforePing; split
 · unfold retain hall; rw [Finset.mul_sum,Finset.sum_mul]; exact sum_congr rfl (fun i _=> by split_ifs <;> first |rfl|simp)
 simp [hall]
end secondary
end Chamber
end YM.CF.LitCurrent
