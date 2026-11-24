import YM.CF.Vp929.Budget.Read
import YM.CF.Ups.Stone

/-! Small window from FiniteGaugeData applied to the room at the bottom of an arbitrary auxiliary run.
Adapted from FiniteGaugeData files Paxos/Rost, Ups/Stone. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief VolumeRate CF.Mint Graph
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d h : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W)
  (N0 : ℕ)
variable {KX b' vL c' l' b DD E C0 h1 r:ℝ}{kT d' :ℕ} (P_: Pic.Span W.pearl KX b' vL c' l' b kT)(Q:Roe.Port P_ DD E C0 h1 r d')(hX:C0 ≤ h) (hp : 1 ≤ h)
local notation "M" => (oYY V N0 J)
local notation "N'" x => cell (oYY V N0 J x) B R.L 0
local notation "PZ" => K.top.clip

def only_base (x b s : ℝ):= Graph.gainS (More (cell (oYY V N0 J x) B R.L 0)) ((Real.sqrt x)⁻¹ /4)*Real.exp (-stoutY (More (cell (oYY V N0 J x) B R.L 0)) x (4*((Real.sqrt x)⁻¹/4)) K.top.clip.direct (temp x) K.top.paths V.W.bar) *Roe.horn (cell (oYY V N0 J x) B R.L 0) b*s
local notation "cpT"=> (b'/(2*Nova.poseX)/2)
structure RoomAt (x : ℝ) (X : GramM (cell (M x) B R.L 0)) (S : Scree.Loom (cell (M x) B R.L 0)) : Prop where
  tempX : X.p.threshold=temp x
  funds : X.funds=K.top.clip
  beta : X.beta=x
  path : X.path.Bounds X.funds K.top.width K.top.paths V.W.bar
  skin : SkinT X S d
  ledger : Ledger h (dleaf R.L x) (dleaf R.L x) (levelQ W.C) (cashU W.C) X
  pos : 0 ≤ dleaf R.L x

include Q hX hp
private theorem base_series {x : ℕ → ℝ} (t:Tendsto x atTop atTop) {A:∀ i, GramM (cell (M (x i)) B R.L 0)} {S:∀ i, Scree.Loom (cell (M (x i)) B R.L 0)}
    (p:∀ i, RoomAt (h:=h) J N0 (x i) (A i) (S i)) : ∀ᶠ i in atTop, only_base J N0 (x i) b cpT ≤ ‖compensated U (A i) (S i)‖ := by
  let δ(i):=dleaf R.L (x i); let I:=rimZ V N0 J (x':=x)
  have q: Roe.WindS B I x h (cashU W.C) (levelQ W.C) K.top.width K.top.paths K.top.clip.linear K.top.clip.direct 1 1 δ δ (fun _=>V.W.bar) A:= by
    obtain ⟨px,pc,hpT⟩:= front V N0 J t
    let D(i:ℕ):ℝ:= radiusB (x i); let w:Tendsto D atTop atTop:=tendsto_natCast_atTop_atTop.comp (Work.E01.radiusB_tendsto.comp t); have he:Aqua D δ:=by
      intro n; exact (((sizeK.powC (sizeK.Bcash R.L) n).tint ((dev_R R).1.low (k:=1) (by decide))).spine.comp t)
    have ht:= he.through w pc
    refine ⟨⟨zero_lt_one,zero_lt_one,t,Eventually.of_forall (fun i=>?_)⟩,px,hpT,ht,Gray.thin (tc t) ht.shrinks, Gray.coef (tc t) _,hp,level_p _,cash_v _,K.top.clip.tail_pos,paths_nonneg V, Eventually.of_forall fun i=> ⟨(p i).tempX,(p i).ledger,(p i).path,le_of_eq (congrArg Clip.linear (p i).funds.symm),le_of_eq (congrArg Clip.direct (p i).funds),(p i).pos⟩⟩
    simp [(p i).beta]
  have hw : 0 ≤ cpT:= by have := Nova.pose_p; have := P_.pos; positivity
  filter_upwards [Roe.fog P_ q,(Roe.costR P_ q S (Eventually.of_forall fun i=> (p i).skin) Q hX).1] with i g u
  have g:=g.1; rw [(p i).beta] at g; exact le_trans (mul_le_mul_of_nonneg_right g hw) u.2.2.2.2.2.2.1
lemma base_point : ∀ᶠ x in atTop, ∃ u > (0:ℝ), ∀ (X : GramM (cell (M x) B R.L 0)) (S:Scree.Loom (cell (M x) B R.L 0)), RoomAt (h:=h) J N0 x X S → u ≤ ‖compensated U X S‖ := by
  suffices ∀ᶠ x in atTop, ∀ (X : GramM (cell (M x) B R.L 0)) (S:Scree.Loom (cell (M x) B R.L 0)), RoomAt (h:=h) J N0 x X S → only_base J N0 x b cpT ≤ ‖compensated U X S‖ by
    filter_upwards [this,eventually_gt_atTop (0:ℝ)] with x e h; refine ⟨_, ?_, e⟩
    unfold only_base Graph.gainS Mint.Roe.horn; have :=Ember.pinch_pos (cell (M x) B R.L 0); have := P_.rP; have := P_.pos; have := Nova.pose_p; positivity
  rw [eventually_atTop]; by_contra! hx
  choose x h f s p t using fun i:ℕ=> hx (i:ℝ); obtain ⟨i,v⟩:= (base_series J N0 P_ Q hX hp (tendsto_atTop_mono h tendsto_natCast_atTop_atTop) p).exists; exact not_le.mpr (t i) v
end YM.CF.Py.Rate
