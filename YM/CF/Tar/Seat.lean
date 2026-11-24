import YM.CF.Tar.Dial
import YM.CF.Tar.Dome
import YM.CF.Paxos.Rost
import YM.CF.Paxos.Port
import YM.CF.Bloom.Rudel
import YM.CF.Bloom.Port
import YM.CF.Pyx.Sign
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Brace Chaff
variable (EA DA Fp:ℝ→ℝ)(F0:(m:Side)→Scroll m B (Brace.northZ m B)){κ:ℝ}(d0:ℝ)(BZ:Heron V a p i N0 k₀ J q h κ R0 EA DA δ d0)(B0:ℕ)
variable {x':ℕ→ℝ}(t:Tendsto x' atTop atTop){L':ℕ→ℕ} (U':∀ i',CashC V a p i N0 k₀ J q h R0 δ EA DA Fp F0 d0 BZ B0 (x' i') (L' i'))
local notation "N_X"=> rimZ V N0 J (x':=x')
local notation "S_X"=> (fun i=>mid ((rimZ V N0 J (x':=x')) i) B)
local notation "Φ"=> (fun i=>Lr (x' i))
local notation "Kχ"=> (fun i=> (U' i).E 0)
variable(hv:1 ≤ h)
variable {KX b' vL c' l' b a' D E' C0 h1 r:ℝ}{kT d' :ℕ} (P_: Pic.Span W.pearl KX b' vL c' l' b kT)(Q:Roe.Port P_ D E' C0 h1 r d')(hX:C0 ≤ h)
open Graph Onyx Pyx Brioche
local notation "Wκ"=> (V.W.bar)
abbrev seat_P(x:ℝ):= cell (oYY V N0 J x) B R.L 0 -- root domain.H
abbrev leg_B(z b:ℝ)(x:ℝ):ℝ:= let N:= More (seat_P V N0 J x); let L:= hemp (fun i:ℕ=> x) 0; Graph.gainS N L *Real.exp (- Graph.stoutY N x (4*L) K.top.clip.direct (temp x) K.top.paths Wκ)*Roe.horn (seat_P V N0 J x) b*(z/(2*Nova.poseX)/2)
include t P_ Q hX hv
lemma morn_X: ∀ᶠ i in atTop,0<leg_B V N0 J b' b (x' i) ∧ leg_B V N0 J b' b (x' i) ≤ ‖Complex.exp (-((U' i).E 0).v) * partitionZ ((U' i).E 0) U ((U' i).Y 0)‖:=by
 let pY:=sham_T V a p i N0 k₀ J q h R0 δ EA DA Fp F0 d0 BZ B0 t U' hv; let X(i):= (U' i).Y 0; have hT:∀ i,Graph.SkinT ((U' i).E 0) (X i) d:=by
    intro i; let Z:= (U' i).scale; let F:= (Z.mend 0).paid; let F':Roof _ J.k d J.n (X i):={F with paid:=fun i=>(F.paid i).shrink J.hr.le}; exact Mint.Stop.sage _ _ _ F' ((Z.rank.owns 0 (Nat.zero_le _)).width ▸ Z.tale 0)
 have hu:0<b'/(2*Nova.poseX)/2:=by have hv:= P_.pos; have hx:= Nova.pose_p; positivity
 filter_upwards [(Roe.costR P_ pY X (Eventually.of_forall hT) Q hX).1, Roe.fog P_ pY, pY.path.helm] with i p u h
 let Z:= (U' i); let y:=x' i; have hx:(Z.E 0).beta=x' i:= (Z.scale.rank.color).trans Z.scale.day.unit
 unfold leg_B; dsimp only; rw [hx] at u
 constructor
 · have hp:= Ember.pinch_pos (seat_P V N0 J y); rcases h with ⟨g,v,ℓ⟩; have ht:0 < hemp (fun _ :ℕ =>x' i) 0:= g; unfold Graph.gainS Roe.horn; have hy:=P_.rP; positivity -- Natcast domain defeq possible
 exact (mul_le_mul_of_nonneg_right u.1 hu.le).trans p.2.2.2.2.2.2.1
omit t
local notation "κF"=> CashC V a p i N0 k₀ J q h R0 δ EA DA Fp F0 d0 BZ B0
lemma polls_P : ∀ᶠ x:ℝ in atTop,∀ m:ℕ,∀ L:CashC V a p i N0 k₀ J q h R0 δ EA DA Fp F0 d0 BZ B0 x m,0<leg_B V N0 J b' b x∧leg_B V N0 J b' b x≤ ‖Complex.exp (-(L.E 0).v)*partitionZ (L.E 0) U (L.Y 0)‖:=by
 by_contra h
 simp only [eventually_atTop,not_exists,not_forall] at h
 -- Lean filter lemma? test
 choose y u m L g using fun i:ℕ=> h i
 let t:Tendsto y atTop atTop := tendsto_atTop_mono u tendsto_natCast_atTop_atTop -- u i type probably ∃ hj if ge.P.
 obtain ⟨i,hx⟩:= (morn_X V a p i N0 k₀ J q _ R0 δ EA DA Fp F0 d0 BZ B0 t L hv P_ Q hX).exists
 exact g i hx
end YM.CF.Py
