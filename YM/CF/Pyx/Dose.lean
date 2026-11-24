import YM.CF.Pyx.Tree
set_option autoImplicit false
set_option maxHeartbeats 1050000
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
variable{B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a α:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)
-- ultra-weak diagonal. enough for Wick plus true RG any number of scales.
open CF.Mint
variable {N:Side}(q:Chi)(J:Robes N V W) (h:ℝ) (Ta:Warm V U W N0 J.n i p q J.k J.d J.roomX a h)
variable {L':ℕ→ℕ}{x':ℕ→ℝ}
open Graph
variable (P':∀ i',Season V a p i N0 q J h Ta (L' i') (x' i') i')
variable (tP:Tendsto x' atTop atTop)
open Onyx
open Charted MeasureTheory Pyx
variable (pK:K.top.clip.direct≤1)
universe uK
variable (Y: Claro.{uK} V a p i N0 q J h Ta P')
abbrev sob(i:ℕ):=seat_u V J (x' i) N0*N
abbrev LinkR (V:Grace K R L)(m B:Side)(p:ℕ):Measure (Pane (cell m B R.L p)):=prior SU.group _
local notation "λQ"=> sob V N0 J (x':=x')
local notation "S'"=> (fun i j=>cell ((sob V N0 J (x':=x')) i) B R.L j)
variable {αK:Type uK} (F:ℕ→ℝ) (pY:Yard (fun i=>mid (rimZ V N0 J (x':=x') i) B) F) (o:∀ i,Site (mid (rimZ V N0 J (x':=x') i) B))(E:Emu.Plot αK F)(X:List αK)
local notation "L₀"=> (fun i=>Pyx.plume (Roe.optV F i _ (o i) E X))
local notation "Kβ"=> (fun i=>Vale.capP U ((P' i).act (L' i)) ((P' i).out.a (L' i))) -- unused.
-- common color Ward test projected from explicit kernels; transport denominator from same interval.Envelope.is pick top. not claiming scaling locality of K_T.HAny*.
include pK Y pY
lemma tune_t:∃ B_:∀ i,Pyx.Track ((fun i j=>cell ((sob V N0 J (x':=x')) i) B R.L j) i (L' i)),
 (∀ j:ℕ, SeenK V ((sob V N0 J (x':=x')) j) (L' j) (Pyx.plume (Roe.optV F j _ (o j) E X)) (B_ j) (I:=J) (Lx:=(P' j).S) (E:=(P' j).X) (q:=q) ∧ CureP (B_ j)) ∧ Tendsto (fun i:ℕ=>(∫ y:Pane (cell (sob V N0 J (x':=x') i) B R.L (L' i)), B_ i y (Vale.capP U ((P' i).act (L' i)) ((P' i).out.a (L' i)) y)∂LinkR V (sob V N0 J (x':=x') i) B (L' i))/partitionZ ((P' i).X (L' i)) U ((P' i).S (L' i))) atTop (𝓝 (Emu.runes E.rho X)):=by
 let X'(i:ℕ):=Pyx.plume (Roe.optV F i _ (o i) E X)
 choose XQ A using fun i=> Charted.runM V _ _ _ _ _ _ _ _ (P' i).pay (X' i) (Pyx.hosted _); refine ⟨XQ,fun i=> ⟨A i,(A i).live (shield _)⟩, (Y.wick αK F pY o E X).2.congr (fun i=> ?_)⟩
 have he:= area_p V _ _ _ _ _ _ _ _ (P' i).pay pK _ (XQ i) (A i); have hv := Charted.balance V _ _ _ _ _ _ _ _ J q _ _ (P' i).pay 0 (Nat.zero_le _)
 change (∫ y:Orbit (S' i 0),X' i y (denZ ((P' i).X 0) _ _ y)∂city _) / partitionZ ((P' i).X 0) _ _=_ ; exact congrArg₂ (·/·) he hv
end YM.CF.Py
