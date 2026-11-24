import YM.CF.Oath.Gloria
import GaugeFieldConstruction.Hollow
import GaugeFieldConstruction.Vuoto
import GaugeFieldConstruction.Nocta
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
section
variable
  {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
  {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
  (V:Grace K R L)
  {x y0 β:ℝ}
  {r d':ℕ}
  (F:Pilot)
  {s u:ℝ}{q q':Chi}
  (D:Corset d q' u (k+2) k')(pV:BudgetPoint)
  {σ:ℝ}(Z:Pluck R)(U:Grasp V.U B d)(W:GivenX V U){Xs: GramM (mid N B)}{Y: GramM (mid P B)}{M:Sheep V U W G Y.J Xs.J (k+2) n A}(P_:∀ X: Support (Domain P B),Lend P B d X)(H:Muster G S x d T)
  {γ α:ℝ} (uF:Fend V H M Z F q Y.p Xs.p γ α j l r)
  {q'' q0 : ℝ}(w':Hive.Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*q'') M.lot M.tone)
  (Fκ:FerryP H F K R D) (φ: Xs.p.power=k')
  {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}(D_: Girt.BaseL U G Y G₀ G₁ q' u)(L0: StageP V H Y Xs U)
  (Cp: Plume.Cord S)(K_:Fairy S (F.hat R x) Cp)(Tp:Ids (mid N B))(U':Pane (mid N B))(i:Roc (mid P B))(O:Ride S)(y:pingS (temp x) (Stilo.bay O) U')
  (Roδ :Support (Domain N B))(Roα :S.ratio.parent i.1.val.1 ∈ Roδ)
  {a a' s0:ℝ}(hx:a < s)(hu:0<a')(hu':a' < u)
  (Qp: Palot.fits (BranchX (r:=r) S (vast (k:=Z.N1*radiusB x) H) ((H.post+90)*radiusB x)) (subtK (r:=r) S i) O)
  (k₀ k₁:ℕ)(A_: Roof (mid N B) s s0 k₀ G₀)(A₁: Roof (mid P B) s s0 k₁ G₁)(heV:k₀+k₁ ≤ radiusB x)(η':l≤18)(ss:s ≤ s0)(tK:s0 < d)(hU:u< firstRadius SU.group) (hpZ:fiery SU.group x R.L < s)
  (hv:∀ (Q: Monk SU.group S), Chir Q x → ‖Q.z‖≤ F.hat R x → Bell S Q x T H.trot H.room H.post H.beta a a')
  (M₀ a0 C C' v w:ℝ)(R0:PlanS k Xs.p Y.p i O (cort U' Cp) (school (cort U' Cp) r H) T R M₀ a0 C C' v w r l x)
  {vK Kρ K₁ ε Bz:ℝ}
  (oθ:Find Xs.p Y.p k n x R.L)(Jp:PactH d u ε Bz q' (k+2) k' D)
  (F':Raid (Dwell (mid P B)))(Q CC:ℝ)(Xf:PressB Y.p i.1 (actionZ Y i) Q CC)(fF:∀ U,BedP Y.p U (actionZ Y i) i.1 F')(fP:∀ i,0≤ F' i)
  (r₂ r₃:Prism.Rock (mid P B))(p₂ p₃:Prism.Rock (mid N B))(zU:r₂∈ hue_I i.1.val.2)(zV:r₃∈ hue_I i.1.val.2)(hlim:Kρ*Xs.p.threshold*(1+(Heir.reach x:ℝ))<u)
  (X' Y₀:Support (Domain P B))
  (Qx:TailB→Support (Domain P B)→Toll (Iota G))(X00:∀ i x, Suite (badge _) (pinH G d true) (pinH G d false) x (Qx i x) (M.X i x))
  (hf:insideS X' x)(uX:mark_l S ((H.post+90)*radiusB x) X'≤ O)(sh: Short S Y.p i.1.val.2)(hK:0≤ Kρ)
open Py Tap Broc Cour
variable (bZ: StatV V G T U W Xs Y α γ t x n k) (h:K.j=4) (W_X:Rill.Arch G d)(tW:W_X.val=1)
include bZ h tW M D_
lemma openingπ (Q:Op (Single (mid P B))) : pulled G (Rill.bring Jp.ink W_X) M.X Q univ= Hove.totF 4 G M.oddP (Thread 4) M.castX.2 Q:=by
 have hf:Even K.j:=by rw [h]; decide; -- tune nat inst
 let A:= (Rill.bring Jp.ink W_X); have hz: fulfills G M.oddP d (j:=K.j) Prod.snd (arcB V.f V.g V.F1 V.F2) M.castX M.X M.Y (Rill.bring Jp.ink W_X):= M.call.issue (onK W_X) _ W_X.property.2 (Rill.bring Jp.ink W_X) rfl
 have ht: (A).val=1:=by unfold A Rill.bring; simp [tW,unionP,Tulip.profile_trivial]
 have hf:=torchCore hf (by omega) M.oddP Prod.snd _ (alum V.pos1.le V.pos2.le V.width1 V.width2).2 M.castX _ ht M.X M.Y hz (Py.prop_L V bZ M D_ W_X tW) Q
 exact hf.trans (congrArg (fun n=> Hove.totF n G M.oddP (Thread n) M.castX.2 Q) h)
end
end YM.CF.Oath
end
