import YM.CF.DPress.Plaque.Taps
import YM.CF.Salt.Mica
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.DPress.Plaque
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
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
open AnalyticBridge.VerifiedReset
variable {n:Side}{t:ℝ}{T:BudgetPoint}
local notation "Y₀"=>SU.group
abbrev haloW(o: Site n):Support n:= halo 2 {o}
-- Use WilsonStartup subsurface for gauge Preis and normalized HS via G.price. Exactly SU.
lemma siteW_(o:Site n): o∈ haloW o:=halo_spec.mpr ⟨o,mem_singleton_self _,by simp⟩
def feeW (o:Site n) (U: Config Y₀ n) := (4:ℝ)⁻¹*∑ i∈Rings o,(Y₀).price (faceValue U i)
attribute [local instance] Gauge.frobInner
lemma CH : 4*‖(Y₀).colorMat (AnalyticBridge.VerifiedReset.spike Y₀)‖^2/((Y₀).repDim:ℝ)=4:=by rw [Gauge.colorMat_norm,AnalyticBridge.VerifiedReset.spike_norm Thera.yet_one,mul_one,Gauge.colorScale_sq]; change 4*(↑(5:ℕ):ℝ)/↑(5:ℕ)=4; norm_num
lemma known : (Y₀).repDim=5:= rfl
lemma gaugeW(o:Site n) (U:Config Y₀ n)(G:Site n→ (Y₀).El) : feeW o (Lattice.gauge G U)=feeW o U:=by simp only [feeW,face_gauge,Gauge.price_conj]
lemma fee_one(o:Site n): feeW o 1=0:=by unfold feeW; simp_rw [WilsonStartup.face_one,Gauge.price_one,sum_const_zero,mul_zero]
@[fun_prop] lemma contFee(o:Site n): Continuous (feeW o):=by unfold feeW faceValue; fun_prop -- G.price_cont
lemma sits (o:Site n): LocalOn (haloW o) (feeW o):=by
 intro u v p; unfold feeW; refine congrArg _ (sum_congr rfl fun i k=>?_); apply congrArg; exact WilsonStartup.face_local i u v (fun i' j x=> p _ (halo_spec.mpr ⟨_,mem_singleton_self _,bill i ((mem_filter.mp k).2) j⟩) (halo_spec.mpr ⟨o,mem_singleton_self _,bill i ((mem_filter.mp k).2) x⟩)) -- near confusion with Bill
open AnalyticBridge.GaussianFieldAlignment Locations Salt
lemma moving_halo(r:Sweep n)(o:Skye.Seat n) : haloW ((boxA r).symm o)= actY r (haloW o):=by unfold haloW; rw [show { (boxA r).symm o }= actY r {o} from (map_singleton (boxA r).symm.toEmbedding o).symm,Salt.walkA]
lemma stampW (r:Sweep n)(V:Pane n) (o:Skye.Seat n): feeW ((boxA r).symm o) (flashA r V)= feeW o V:=by
 -- adapted Salt/Mica
 let s:=r.s; let b:=(assembly n).embed r.b; let Z:=shiftFaces s b; let U:Config Y₀ (More n):= Lattice.pull s b V; have hx(i:Cell (More n)):Pressure.toll (flashA r V) i=Pressure.toll V (Z i):=by
    have he: Pressure.toll U i=Pressure.toll V (Z i):=Face.send_price V i s b _ (Y₀).chord_inv fun u w=> (Y₀).chord_conj w u
    rw [revoke]; generalize r.charge=q; cases q; exact he; exact (Rink.mint_b U i).trans he
 have ht(i:Cell (More n)): touched i=actY r (touched (Z i)):=by
    rw [actY,show touched (Z i)=(touched i).map (boxA r).toEmbedding from ?_]; ext j; simp
    rw [map_eq_image]; refine Eq.trans (Work.H03.touched_send s b i) ?_; exact image_congr fun x _=> (sitA ..).symm
 unfold feeW; apply congrArg; apply sum_equiv Z; · intro i; unfold Rings; simp only [mem_filter,mem_univ,true_and]; rw [ht]; simp [actY]
 intro i p; have hv:= hx i; change (Y₀).chord _=(Y₀).chord _ at hv; obtain he:=congrArg (fun x:ℝ=>x^2) hv; rw [(Y₀).chord_price,(Y₀).chord_price] at he; linarith
-- mask support further note.
end YM.CF.DPress.Plaque
