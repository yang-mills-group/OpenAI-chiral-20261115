import YM.CF.DPress.Yarn.Heights
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Thrift RoomF
variable (F: RoomF J Λ M Δ)
structure Crib (F: RoomF J Λ M Δ)(n:ℕ) where
 β : ℕ→ℝ
 head : Due V C.w C.p C.i (Ntop P_) Δ M F.legal n β
 clk : Align C J
variable {F} (D:Crib F n)
namespace Crib
abbrev venue (j:ℕ):=hueR V C.w C.p C.i (Ntop P_) Δ M F.legal n D.β j
abbrev rate (j:ℕ):= Dh V M B (n-1-j) j
abbrev pace (j:ℕ):= V.L.mint (n-1-j) (kint M B R.L j)
abbrev Lax (j:ℕ):= cell M B R.L j
local notation "S'" j:max=> apt M B R.L j
local notation "jH" j:max=> hat R.L x j
local notation "Sβ" i:max=> rate (M:=M) (B:=B) (n:=n) (V:=V) i
local notation "Yp"=> F.Y
abbrev γn (j:ℕ):= V.L.charge (n-1-j)
abbrev shift (j:ℕ):=(W.arm (Δ.large.trans F.legal) n).shift j
abbrev toll(j:ℕ):=D.β j- D.β (j+1)
lemma κt(h:j<n): toll D j= V.L.charge (n-1-j) + (W.arm (Δ.large.trans F.legal) n).shift j:=by unfold toll; rw [D.head.fee j h]; change _+(_+_)-_= _; ring -- tune underscores
abbrev paid(j:ℕ)(θ:ℝ):=pay_K (venue D j) (θ+toll D j) -- θ at j+1. not final!
lemma warmth {X:GramM (cell M B R.L (j+1))}(h:j<n) (p: CloseC (D.venue (j+1)) X) (hx:matchedX (hat R.L x (j+1)) X.beta): StatV V (S' j) (V.L.mint (n-1-j) (kint M B R.L j)) U W (D.paid j X.beta) X (V.L.charge (n-1-j)) ((W.arm (Δ.large.trans F.legal) n).shift j) C.w (hat R.L x j) C.p C.i:= sized_F (N:=mesh M R.L j) (P:=mesh M R.L (j+1)) (B:=B) (S:=(Sβ j)) (T:=V.L.mint (n-1-j) (kint M B R.L j)) V C.w C.p C.i (Ntop P_) Δ M F.legal n D.β D.head j X p h hx
lemma stat (h:j<n):StatV V (S' j) (V.L.mint (n-1-j) (kint M B R.L j)) U W (venue D j) (venue D (j+1)) (V.L.charge (n-1-j)) ((W.arm (Δ.large.trans F.legal) n).shift j) C.w (jH j) C.p C.i:=by
 have hp:= warmth (j:=j) D h (X:=D.venue (j+1)) ⟨rfl,rfl,rfl,rfl⟩ (D.head.space _ h); rwa [show D.paid j (D.venue (j+1)).beta=D.venue j from (by unfold paid toll; rw [show (D.venue (j+1)).beta+_=D.β j from (by change D.β (j+1)+(D.β j-D.β (j+1)) = _; abel)])] at hp
lemma basic {X:GramM (cell M B R.L (j+1))}{b c:ℝ}(w:LotR X C.h b c)(h:j<n)(p:CloseC (D.venue (j+1)) X)(v:matchedX (hat R.L x (j+1)) X.beta):Nonempty (Girt.BaseL U (apt M B R.L j) X (F.Y j) (F.Y (j+1)) C.q' J.d):=by
 have he:= D.warmth h p v; apply rig V U W J C.q' (F.rocket j) _ (F.rocket (j+1)).paid X he.sound rfl; exact ward_m (show X.path.Bounds X.funds _ _ _ from by rw [he.move,he.coinY]; exact he.hunt.up) w
abbrev venueLot(j) : LotR (D.venue j) C.h 0 0:= ⟨(AccountY.zero (n:=cell M B R.L j) (q:=(venue D j).p) C.uB).E,rfl,(AccountY.zero (n:=cell M B R.L j) (q:=(venue D j).p) C.uB).K⟩
abbrev Hq(j):=Λ.O (hat R.L x j)
abbrev ωQuota(j):=Tew.tiny R (hat R.L x j)
abbrev locale(j:ℕ)(g:j<n):Maud (hat R.L x j) C (apt M B R.L j) (Dh V M B (n-1-j) j):=⟨V.L.mint (n-1-j) (kint M B R.L j),D.venue j, D.venue (j+1),F.Y j,F.Y (j+1),γn (V:=V) (n:=n) j,(W.arm (Δ.large.trans F.legal) n).shift j,by rw [D.clk.one,D.clk.νs,D.clk.v0]; exact (F.rocket j).paid,by rw [D.clk.one,D.clk.νs,D.clk.v0]; exact (F.rocket _).paid,by rw [D.clk.point,D.clk.νs]; exact (F.rocket j).pose, Classical.choice (by rw [D.clk.point]; exact D.basic (D.venueLot _) g (⟨rfl,rfl,rfl,rfl⟩) (D.head.space _ g)), D.stat g, (Nat.mul_le_mul_right _ (show C.n₀≤ Ntop P_ from Nat.le_add_right ..)).trans (F.size _)⟩ -- Sector Tactic. leave Maud.reducible
include F in
lemma σG(j:ℕ) : P_.μN≤ (cell M B R.L j).val:=by
 have he:=F.size j; have ht: P_.μN * 2 ≤ Ntop P_ * radiusB (hat R.L x j):=Nat.mul_le_mul (Nat.le_add_left ..) ((by decide : 2 ≤ (6:ℕ)).trans (F.epoch j).wide); have hv:= ht.trans he; change _≤ (cell M B R.L j).val*2 at hv; omega
abbrev νB (j:ℕ):= Λ.O (hat R.L x j)
lemma earned (h:i<n):Nonempty (Silo A Λ.ξ (D.locale i h) (Λ.O (hat R.L x i))):= (F.epoch i).tax.lends (D.locale i h) (σG (F:=F) _) (F.Ξqual i) -- `σG` include F? inferred above?
def σp (i:ℕ)(h:i<n):=Classical.choice (earned D h)
variable {Θ:ℝ}{h:i<n} (E:Lobby (D.locale i h) (Λ.O (hat R.L x i)) Θ)
-- simpler
end Crib
end FitD
end YM.CF.Py.Kay
