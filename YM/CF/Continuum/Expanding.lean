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
variable (Pq : Session V a p i N0 J q h R0 δ x M l)
lemma credit_rule(j:ℕ)(hp:j ≤ l) : InterestX W.C (cell M B R.L j) (Pq.E j).J := (Pq.scale.note.owns j hp).taste ▸ ((W.arm ..).sound j)
lemma expense (j:ℕ)(hp:j ≤ l) (w0:1≤h) : Graph.Ledger h (Lr (hatQ j)) (Lr (hatQ j)) (levelQ W.C) (cashU W.C) (Pq.E j) := frostQ ((Pq.scale.note.note j hp).lot_p le_rfl le_rfl) (zero_le_one.trans w0) (credit_rule V a p i N0 J q h R0 δ Pq j hp)
lemma footprint_B(j:ℕ)(hp:j≤l) : (Pq.E j).path.Bounds (Pq.E j).funds K.top.width K.top.paths V.W.bar:=by
    let he:= Pq.scale.note.owns j hp; rw [← (show _=(Pq.E j).path from he.path),←(show _=(Pq.E j).funds from he.fund)]; exact V.L.mood _
include V
lemma wing_budget : 0≤ K.top.paths:=by
    obtain ⟨t,h,q⟩:= (V.L.mood 0).rows (⟨(0,1), by decide⟩); exact le_trans (tsum_nonneg t) q
lemma loomActs (j:ℕ) : Roof (cell M B R.L j) J.k d J.n (Pq.Y j):=let T:=(Pq.scale.roof j).paid; {T with paid:=fun i=>(T.paid i).shrink J.hr.le}
lemma mirrors (j:ℕ)(hp:j≤l)(s : Axis) : Window.expectationsMirror (Vale.mesh M R.L j) B s (Window.finiteForm V.U U (Pq.E j) (Pq.Y j)):=by
  let H:= Pq.scale.note.note j hp; have hg:1 ≤ K.j:=by have he:=V.L.lobby; have hv:=R.order_cut; omega
  have hx := H.buoy; have hb : IncX (fun _=>True) (Pq.E j).slip (Pq.E j).p h 0 :=by rw [H.tone]; exact (Vale.lye ..).1
  intro F P; exact Window.mirror_normal (credit_rule V a p i N0 J q h R0 δ Pq j hp) hg W.pearl V.note (loomActs V a p i N0 J q h R0 δ Pq j) hx hb H.nite (J.gran.trans (Pq.scale.roof _).size) s P
section
variable {KX b' vL c' l' b a' D E' C0 h1 r:ℝ}{kT d' :ℕ} (P_: Pic.Span W.pearl KX b' vL c' l' b kT)(Q:Roe.Port P_ D E' C0 h1 r d')(hX:C0 ≤ h)(hp:1≤h)
open MeasureTheory
local notation "PS" f s l=> Session V a p i N0 J q h R0 δ f s l
local notation "Bₓ" v=> cell v B R.L 0
local notation "Mₓ" v=> Vale.mesh v R.L 0
local notation "core″" x => oYY V N0 J x
-- all large root witnesses matter. no comparisons using different Subalgebras
variable {α β:ℕ→ℝ} {F N : ℕ→Side}{H:ℕ→ℕ} (S:∀ j,Session V a p i N0 J q h R0 δ (α j) (F j) (H j))
include hp
lemma broad_fields (he : Window.AdmittedSeries α (eur (fun i=>Bₓ (F i)))) :
    Window.Pastures B (fun i=> Mₓ (F i)) α h (cashU W.C) (levelQ W.C) K.top.width K.top.paths K.top.clip.linear K.top.clip.direct V.W.bar (fun i=>dleaf R.L (α i)) (fun i=>(S i).E 0) := by
  have h0(i:ℝ):hat R.L i 0=i:=by simp [hat]
  let L:=eur (fun i=>Bₓ (F i)); let X(i):=(S i).E 0; have ht:Aqua L (fun i=>dleaf R.L (α i)):=by
     let g(i):= Scales.g SU.group R.L (α i); have hg:Tendsto g atTop (𝓝 0):= (YM.SectorNext.Remainder.Scales.minute SU.group R.L).comp he.inverse_large
     exact (show Aqua L (tame α) from he.tame_bills).fed (Gray.thin he.side_large hg) he.side_large
  refine ⟨he,fun i=>(S i).scale.note.color.trans (S i).scale.day.unit,ht,hp,level_p _,cash_v _,K.top.clip.tail_pos, wing_budget V, Eventually.of_forall fun k=>?_⟩
  dsimp only; let P:=S k; let Y:= P.E 0; let he:= P.scale.note.owns 0 (Nat.zero_le _); let ht0:= expense V a p i N0 J q h R0 δ P 0 (Nat.zero_le _) hp; have hQ:= P.val.boot 0; have ht':0 ≤ Lr (hat R.L (α k) 0):= hush_h ((P.scale.note.note 0 (Nat.zero_le _)).lot_p le_rfl le_rfl) (zero_le_one.trans hp); have hv : Y.funds=K.top.clip:=he.fund.symm; rw [h0] at ht0 hQ ht'
  have heQ: P.val.a 0=Y.p := he.width
  exact ⟨heQ ▸ hQ.1, ht0, footprint_B V a p i N0 J q h R0 δ P 0 (Nat.zero_le _), le_of_eq (congrArg Clip.linear hv.symm),le_of_eq (congrArg Clip.direct hv), ht'⟩
-- permit express with α *ordered*, same finite root range.
def stopPrice (M:Side)(x r c:ℝ):=Graph.gainS (More (Bₓ M)) (Mint.hemp (fun _=>x) 0)*Real.exp (-stoutY (More (Bₓ M)) x (4*Mint.hemp (fun _=>x) 0) K.top.clip.direct (temp x) K.top.paths V.W.bar) *Roe.horn (Bₓ M) r*c
include Q hX
lemma known_lower (t: Window.AdmittedSeries α (eur (fun i=>Bₓ (F i)))) : ∀ᶠ i in atTop, stopPrice (B:=B) V (F i) (α i) b ((b'/(2*Nova.poseX))/2) ≤ ‖Complex.exp (-((S i).E 0).v)*partitionZ ((S i).E 0) U ((S i).Y 0)‖:= by
  let X:= broad_fields V a p i N0 J q h R0 δ hp S t
  have hg(k):Graph.SkinT ((S k).E 0) ((S k).Y 0) d:=by
     let P:=S k; exact Mint.Stop.sage _ _ _ (loomActs V a p i N0 J q h R0 δ P 0) ((P.scale.note.owns 0 (Nat.zero_le _)).width ▸ P.scale.pole 0)
  have hv:0 < (b'/(2*Nova.poseX))/2:=by have hg:=P_.pos; have hv:=Nova.pose_p; positivity
  filter_upwards [X.angleLower P_,(X.costR P_ (fun k=>(S k).Y 0) (Eventually.of_forall hg) Q hX).1] with k ⟨ht,_⟩ Kν
  rw [X.beta] at ht; exact (mul_le_mul_of_nonneg_right ht hv.le).trans Kν.2.2.2.2.2.2.1

lemma until_gate : ∀ᶠ x in atTop,∀ M:Side, Allowed V N0 J x M → ∃ ℓ:ℝ,0<ℓ∧∀ k:ℕ,∀ X:Session V a p i N0 J q h R0 δ x (M*N') k, ℓ ≤ ‖Complex.exp (-(X.E 0).v)*partitionZ (X.E 0) U (X.Y 0)‖:= by
  let cost(x:ℝ)(M):= stopPrice (B:=B) V M x b (b'/(2*Nova.poseX)/2); have h_0:=(P_.pos)
  have u:∀ᶠ x:ℝ in atTop, ∀ i', 0<cost x i':=(eventually_gt_atTop (0:ℝ)).mono fun x p i'=>by unfold cost stopPrice Graph.gainS Mint.hemp Roe.horn; have he:= P_.rP; have hv:=Nova.pose_p; have hw:=Ember.pinch_pos (cell i' B R.L 0); positivity
  suffices y:∀ᶠ x:ℝ in atTop,∀ M:Side, Allowed V N0 J x M→∀ l:ℕ,∀ X:Session V a p i N0 J q h R0 δ x (M*N') l, cost x (M*N') ≤ ‖Complex.exp (-(X.E 0).v)*partitionZ (X.E 0) U (X.Y 0)‖ by exact (u.and y).mono fun i v M p=>⟨_,v.1 _,v.2 M p⟩
  rw [eventually_atTop]; by_contra! hh
  choose f t m P0 l X g using fun i:ℕ=>hh i; have ht:=known_lower V a p i N0 J q h R0 δ P_ Q hX hp X (by_series V N0 J (tendsto_atTop_mono t tendsto_natCast_atTop_atTop) P0); exact (ht.exists).elim fun i v=> (not_le.mpr (g i)) v
end
end YM.CF.Py.Period
