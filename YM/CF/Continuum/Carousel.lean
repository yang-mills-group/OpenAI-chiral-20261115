import YM.CF.Continuum.CarnI
import YM.CF.Continuum.Ramp
import YM.CF.Continuum.Scope
import YM.CF.Continuum.Episode
import YM.CF.Continuum.Symmetric
import YM.CF.Continuum.Allowed
/-!
# Which expanding periods? Retain astronaut and grants

Details: use the SAME reconstruction apparatus on the old UV-limit witness and
on new periods. No separate positive measures. We express the non-anchored
inhabitance range and produce history witnesses `Session`s and normalized limit
on this permit. At anchor mark-specialized; may choose same f. This is phase I,
period extension NOT common-limit yet. Stamp requirements don't connect bare-data
values across those periods (including β_l). Need cross-period bounds.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Period
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
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
open CF.Window
open Graph Girt
variable {M M0 : Side}
local notation "hatQ" => hat R.L x
/-!
# Initial sequences in the fixed-x `MeterQ` regime. Captures what a d8
trajectory has on a (possibly shorter than its top) prefix. Also used for
comparing regulators in exactly the same **periods** & resolution.
`Promoted`: price stamp to support through-level bounds. There is no hypothesis
of matching temperature-exponent in the REAL path in or beyond each session;
need to use a `PaidFrame` et al for that. `Carn*` compares `β,E` sectors
attempt permitting the same pivot and normalized stance in same epochs. This
declaration doesn't encode any preferred regulator change and can't replace a
matching estimate.
-/
open Jade.Earn
structure Carousel (x:ℝ)(Ns:Side)(l:ℕ) where
 val:Month x a i p N0 V W
 tip: val.q ≤ Ns.val
 top:ℕ
 probed:l≤top
 main:ℕ→ℝ
 E:Vestal Ns B R.L
 Y:Cape Ns B R.L
 Q:ℕ→Haro.SpaceM
 tilt:ℕ→ℝ
 -- data all the way up
 wear (j:ℕ): j<top →∀ V':Orbit (cell Ns B R.L j),Rue.FleetS (E j).p.threshold V'.1→ stove U (Y j) (E (j+1)) (Y (j+1)) (apt Ns B R.L j) (V.L.op (top-1-j) (kint Ns B R.L j)) q J.d (Q j).val V' = denZ (E j) U (Y j) V'
 owns(j:ℕ): j ≤ top → CloseC (hueR V a p i N0 val Ns tip top main j) (E j)
 sift(j:ℕ): j ≤ top → matchedX (hat R.L x j) (E j).beta
 mark(i:ℕ):Rue.IsleB SU.group (val.a i).threshold
 pole(i:ℕ):(val.a i).threshold ≤ J.k
 roof(j:ℕ):RocketV V (mesh Ns R.L j) (mesh Ns R.L (j+1)) U W J (Y j) (apt Ns B R.L j) q
 day: Due V a p i N0 val Ns tip top main
 legal(j:ℕ): j ≤ top→ Girt.Ward (E j)
 balance(j:ℕ): j ≤ top → partitionZ (E j) U (Y j) = partitionZ (E top) U (Y top)
 color:(E 0).beta=x
 -- prefix with the STRONG REGIME receipt
 heat(j:ℕ): j<l→ ‖Q j‖ ≤ R0 (hat R.L x j)
 price(j:ℕ):j<l→ |tilt j| ≤ δ (hat R.L x j)
 note(j:ℕ): j ≤ l → Laurel (E j) K.j h (dleaf R.L (hat R.L x j)) (dleaf R.L (hat R.L x j)) R.L.val
 shift(j:ℕ):j<l→ ((E (j+1)).beta-(main (j+1)))-((E j).beta-(main j)) = tilt j
open Girt
namespace Carousel
variable (F:Carousel V a p i N0 J q h R0 δ x M l)
noncomputable def standard (F:Session V a p i N0 J q h R0 δ x M l) : Carousel V a p i N0 J q h R0 δ x M l:=
 ⟨F.val,F.tip,l,le_rfl,F.main,F.E,F.Y,F.Q,F.tilt,F.scale.note.wear,F.scale.note.owns,F.scale.note.sift,F.scale.mark,F.scale.pole,F.scale.roof,F.scale.day,(fun j p'=>ward_m (footprint_B V a p i N0 J q h R0 δ F j p') ((F.scale.note.note j p').lot_p le_rfl le_rfl)),F.scale.balance,F.scale.note.color.trans F.scale.day.unit,F.scale.note.tip,F.scale.note.price,F.scale.note.note,F.scale.note.shift⟩
variable (Pq : Carousel V a p i N0 J q h R0 δ x M l)
lemma credit_rule(j:ℕ)(hp:j ≤ l) : InterestX W.C (cell M B R.L j) (Pq.E j).J := (Pq.owns j (hp.trans Pq.probed)).taste ▸ ((W.arm ..).sound j)
lemma expense (j:ℕ)(hp:j ≤ l) (w0:1≤h) : Graph.Ledger h (Lr (hatQ j)) (Lr (hatQ j)) (levelQ W.C) (cashU W.C) (Pq.E j) := frostQ ((Pq.note j hp).lot_p le_rfl le_rfl) (zero_le_one.trans w0) (credit_rule V a p i N0 J q h R0 δ Pq j hp)
lemma footprint_B(j:ℕ)(hp:j≤l) : (Pq.E j).path.Bounds (Pq.E j).funds K.top.width K.top.paths V.W.bar:=by
    let he:= Pq.owns j (hp.trans Pq.probed); rw [← (show _=(Pq.E j).path from he.path),←(show _=(Pq.E j).funds from he.fund)]; exact V.L.mood _
include V
lemma loomActs (j:ℕ) : Roof (cell M B R.L j) J.k d J.n (Pq.Y j):=let T:=(Pq.roof j).paid; {T with paid:=fun i=>(T.paid i).shrink J.hr.le}
variable {KX b' vL c' l' b a' D E' C0 h1 r:ℝ}{kT d' :ℕ} (P_: Pic.Span W.pearl KX b' vL c' l' b kT)(Q:Roe.Port P_ D E' C0 h1 r d')(hX:C0 ≤ h)(hp:1≤h)
open MeasureTheory
local notation "PS" f s l=> Carousel V a p i N0 J q h R0 δ f s l
local notation "Bₓ" v=> cell v B R.L 0
local notation "Mₓ" v=> Vale.mesh v R.L 0
local notation "core″" x => oYY V N0 J x
-- all large root witnesses matter. no comparisons using different Subalgebras
variable {α β:ℕ→ℝ} {F N : ℕ→Side}{H:ℕ→ℕ} (S:∀ j,Carousel V a p i N0 J q h R0 δ (α j) (F j) (H j))
include hp
lemma openStart (he : Window.AdmittedSeries α (eur (fun i=>Bₓ (F i)))) :
    Window.Pastures B (fun i=> Mₓ (F i)) α h (cashU W.C) (levelQ W.C) K.top.width K.top.paths K.top.clip.linear K.top.clip.direct V.W.bar (fun i=>dleaf R.L (α i)) (fun i=>(S i).E 0) := by
  have h0(i:ℝ):hat R.L i 0=i:=by simp [hat]
  let L:=eur (fun i=>Bₓ (F i)); let X(i):=(S i).E 0; have ht:Aqua L (fun i=>dleaf R.L (α i)):=by
     let g(i):= Scales.g SU.group R.L (α i); have hg:Tendsto g atTop (𝓝 0):= (YM.SectorNext.Remainder.Scales.minute SU.group R.L).comp he.inverse_large
     exact (show Aqua L (tame α) from he.tame_bills).fed (Gray.thin he.side_large hg) he.side_large
  refine ⟨he,fun i=>(S i).color,ht,hp,level_p _,cash_v _,K.top.clip.tail_pos, wing_budget V, Eventually.of_forall fun k=>?_⟩
  dsimp only; let P:=S k; let Y:= P.E 0; let he:= P.owns 0 (Nat.zero_le _); let ht0:= expense V a p i N0 J q h R0 δ P 0 (Nat.zero_le _) hp; have hQ:= P.val.boot 0; have ht':0 ≤ Lr (hat R.L (α k) 0):= hush_h ((P.note 0 (Nat.zero_le _)).lot_p le_rfl le_rfl) (zero_le_one.trans hp); have hv : Y.funds=K.top.clip:=he.fund.symm; rw [h0] at ht0 hQ ht'
  have heQ: P.val.a 0=Y.p := he.width
  exact ⟨heQ ▸ hQ.1, ht0, footprint_B V a p i N0 J q h R0 δ P 0 (Nat.zero_le _), le_of_eq (congrArg Clip.linear hv.symm),le_of_eq (congrArg Clip.direct hv), ht'⟩
end Carousel
end YM.CF.Py.Period
