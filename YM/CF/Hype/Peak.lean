import YM.CF.Oath.Gear
import YM.CF.Muse.Pure
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> (LeanV (Single Kx))
-- Exact resolve PH.Wick all shares.SupportX both senses. 
variable (p q: Single (mid P B))(Tg:Rill.Arch G t)(W: Meter TailB G t)(Y:Meter Grave G t)(g_: Odd G.count.val)(t':0<t)(kR:ℕ)
local notation "ρ"=> Support (Domain P B)
local notation "PX" b:max a:max=> (twigExt (b,a))
local notation "β"=> bring t' Tg
local notation "Xm"=> cala G S g_ t t' W Y Tg kR
-- reindex independent True Tilt.Axis. Metric after PE.Z.W. EACH (p,q) coarse independent shape.ALL order consensus
variable (F':RegBudget (mid P B))(DΦ:Finset (Scree.Hub (mid P B)))
local notation "Xρ"=> (γl x (Domain P B))
local notation "KΩ"=> (Finset (Support (Domain P B)))
local notation "SX"=> (StackL F' DΦ)
-- stack includes all.Slip combined separately. ANY charges.
local notation "ρk"=> (inbool (Domain P B) x)
variable (X: Finset (Support (Domain P B)))(U:Pane (mid N B))
local notation "Fv"=> (pulled G (bring t' Tg) W SX X)
local notation "tU"=> (bring t' Tg)
local notation "LI"=> (frame_w Fv)
variable (u:∀ i∈ DΦ,∀ (W':Pane (mid P B)), Flour (camp i.val.2) ((F' i W').val))
-- localized docks for reanchor tariff exactly first endpoint. Edge h. support.C. Without revolution. 
variable (i:Scree.Hub (mid P B))(p₁ p₂:Rock (mid P B))(q₁ q₂:Rock (mid N B))(Y Z:Support (Domain P B))
local notation "Θ"=> lyric G t' W (F' i) Y Z p₁ p₂ q₁ q₂ 1 Tg
local notation "oQ"=> (S.ratio.parent i.val.1)
variable(Qx:TailB→Support (Domain P B)→Toll (Iota G))(pR:∀ i B,Suite (badge _) (pinH G t true) (pinH G t false) B (Qx i B) (W i B))
variable {u0:ℝ}(h: Prism.Rock (mid P B))
local notation "vZ"=> (hatY S)
variable(Fs:Rock (mid N B)→Rock (mid N B)→Op SU.Slot)
abbrev cars_P (p q:Rock (mid N B)) (V:Pane (mid N B))(A:Op SU.Slot): FC CM:=lineY p q (Haro.taxi V p q A)
lemma roll_P (H':Op SU.Slot): cars_P q₁ q₂ 1 H'= lineY q₁ q₂ H':=by
 unfold cars_P Haro.taxi; have he(i:Site (Domain N B))(w:Lattice.Walk): travel (1:Pane (mid N B)) i w=1:=by induction w generalizing i with | nil=>rfl| cons a b ih=>rw [travel,ih]; simp [Step.read]
 rw [he]; unfold mater; simp only [map_one]; rw [show Subtype.val (1:UNI SU.Slot)=(1:Op SU.Slot) from rfl, mul_one]
local notation "Qφ"=> (∑ p:Rock (mid N B),∑ q:Rock (mid N B),cars_P p q 1 (Fs p q))
lemma linX {ι:Type*}(p q:Rock (mid N B))(K:Finset ι)(V:Pane (mid N B))(F:ι→Op SU.Slot): ∑ i∈K,cars_P p q V (F i)= cars_P p q V (∑ i∈K,F i) :=by unfold cars_P Haro.taxi; rw [Matrix.sum_mul, line_s]
lemma urn_drop (p q:Single (mid N B))(T:Finset CM)(u:T≠Haro.tray p q)(z:ℂ):crumb (z • gateY p q) T=0:=by rw [reel,crumb_scale,crumb_scale,Pastry.chip,if_neg u,mul_zero,mul_zero]
lemma tier_b (p q:Single (mid N B))(z:ℂ):‖crumb (z • gateY p q) (Haro.tray p q)‖=‖z‖:=by rw [reel,crumb_scale,crumb_scale,Pastry.chip,if_pos rfl]; simp [handY,parity]
private lemma trayH(a b:Single (mid N B))(p q: Single (mid N B))(t:Haro.tray a b=Haro.tray p q):a=p∧b=q:= Prod.mk.inj (tray_in (a₁:=(a,b)) (a₂:=(p,q)) t) -- name syntax tune
lemma pearl_S (u v: SU.Slot): ‖Fs q₁ q₂ u v‖ ≤ ‖Qφ‖:=by
 let T:= Haro.tray (q₁,u) (q₂,v); let F(i j:Rock (mid N B))(a b:SU.Slot):=crumb (Fs i j a b • gateY (i,a) (j,b)) T
 have h(A B p q)(tv:A≠ q₁ ∨ B≠q₂ ∨ p≠ u ∨ q≠ v): F A B p q=0:= urn_drop _ _ _ (fun g=> (by obtain ⟨z,t⟩:= trayH _ _ _ _ g; simp_all only [Prod.mk.injEq]; tauto)) _ -- replace v'.
 have hp : crumb Qφ T= F q₁ q₂ u v:=by
    simp_rw [roll_P,lineY,Pastry.crumb_sum]; change (∑ p:Rock (mid N B),∑ q:Rock (mid N B),∑ u:SU.Slot,∑ v:SU.Slot,F p q u v)=_
    rw [sum_eq_single q₁]; swap; · intro y _ q; exact sum_eq_zero fun i _=>sum_eq_zero fun j _=>sum_eq_zero fun k _=>h y i j k (Or.inl q)
    rotate_left; · simp
    rw [sum_eq_single q₂]; swap; · intro i _ q; exact sum_eq_zero fun v _=> sum_eq_zero fun j _=> h _ _ v j (Or.inr (Or.inl q))
    rotate_left; · simp
    rw [sum_eq_single u]; swap; · intro i _ q; exact sum_eq_zero fun j _=> h _ _ i j (Or.inr (Or.inr (Or.inl q)))
    rotate_left; · simp
    rw [sum_eq_single v]; exact fun i _ q=> h _ _ _ _ (Or.inr (Or.inr (Or.inr q))); simp
 rw [← tier_b (B:=B) (q₁,u) (q₂,v),←show _=crumb ((Fs q₁ q₂ u v) • gateY (q₁,u) (q₂,v)) T from hp]; exact norm_entry .. -- tune matching tray
end YM.CF.Oath
