import Anomaly.Ship.Lender
import Anomaly.Ship.Glass
import Anomaly.Ship.Pod
import Anomaly.Ship.TwinZ
import Anomaly.Apert.Lift
import Anomaly.Apert.Price
import Anomaly.Ship.Salary
import Anomaly.Ship.Tines
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor Mew PowerSeries
open scoped Mew

variable {n:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}
open Neon Bake Rive QuadClock Stilo Roots
-- earned Root-v keyed regulator rep. Analytic both fresh and old together.
-- expose First pins on separated Θ tests
variable {N B:Side}
local notation "Fᴷ" => mid N B
set_option maxHeartbeats 700000
local notation "F₀"=> Orbit (mid N B)
open Py Oise Swell Sault Pastry Rue
variable {R:GramM (mid N B)}{L:Side}{wL:Odd L.val}{i_:ℕ}{X: Pricing i_ L wL (Thread i_)}{e':ℝ}(U:Grasp X B e')(C:Scree.Loom (mid N B))
variable {E:Key I→RegBudget (mid N B)}{F:Key I→ForceBudget (mid N B)}(q₀:E 0=0) (σ:I→Site (mid N B))(v:SiltQ E (Cube.node∘σ))(k:BudK F (Cube.node∘σ))
-- semantic at all Orders using zeroes; σ.Root. Use real commitments after crop.
local notation "Sσ"=>Cube.node ∘ σ
abbrev clearRoot (E:Key I→ RegBudget (mid N B)) := awake (Cube.node ∘ σ) E (νTip E)
local notation "Vq"=>clearRoot σ E
local notation "Vκ"=>bustle (Sσ) F
private lemma νVecE {E:Key I→ RegBudget (mid N B)}(i:I): νΦX E {i}=νTip E i:=by funext x y; change gemI _ _ = tipI _ _; exact  cue_1 (fun z:Key I=> E z x y) i
private lemma νVecF {E:Key I→ ForceBudget (mid N B)}(i:I): νΦK E {i}=emberTip E i:=by funext x y; change gemI _ _ = tipI _ _; exact  cue_1 (fun z:Key I=> E z x y) i
include q₀ v k
lemma cropEra : Notice σ Vq Vκ ∧∀ i,νTip Vq i=νTip E i∧ emberTip Vκ i=emberTip F i:=by
 let G:=νTip E; have he(j):νTip Vq j= G j:= value_E ..
 have hp(i):emberTip Vκ i= emberTip F i:=(value_F (Sσ) F i).trans (νVecF ..)
 refine ⟨⟨cash0 ..,?_,eReady (Sσ) G E,fun i=> quietF Sσ F (fun x=>⟨k.quiet x,k.toll x⟩) i,fReady Sσ F,fun i w=> ?_⟩,fun i=>⟨he i,hp i⟩⟩
 · intro X; exact quietE Sσ G E (fun x=>⟨v.blank x,v.token x⟩) (fun i Y t=>pokePay v Y (fun r=>t (by have hp:=νVecE (E:=E) i; unfold G; rw [←hp]; exact r)) i (mem_singleton_self _)) X
 rw [he,hp]; exact ⟨crest_E .., (crest_K (Sσ) F i w).trans (congrArg _ (νVecF ..))⟩
local notation "ΠX" z:max s:max k:max=> denZ (color_b R R.beta (R.F+z) R.slip s (R.v+k))
variable (p:R.K=F 0)(r:Key I→ℂ)(l:List I)(vQ:ψS (Cube.node∘σ) l)
include vQ p
lemma eat_sweep (x:Orbit (mid N B))(uX:IsStarProjection (Dial.spar i_ R.J.M (C x)))(w:River r): Soft l (fun z=> (ΠX (E z) (F z) (r z)) U C x) (fun z=> (ΠX (Vq z) (R.K+Vκ z) (r z)) U C x):=by
 let Y(z:Key I):= r z • (1:Cipher Fᴷ); have ht:River Y:= κscale w (zeroR _); let S:= pilotH U R C x uX; let Q:Cipher Fᴷ→ₗ[ℂ] Phys Fᴷ:=⟨⟨fun i=> S (Cadre.poseL _ i),fun i j=>(congrArg (fun v=>S v) (act_add ..)).trans (map_add ..)⟩,fun x y=>(congrArg (fun v=>S v) (act_smul ..)).trans (map_smul ..)⟩
 let Xz(E:Key I→RegBudget (mid N B))(K:Key I→ForceBudget (mid N B))(z:Key I):=S (poseL _ (exp (Y z+circE (P:=R.p) x.1 E z)*fueled R.p (K z) x))
 have hu(K':Key I→ RegBudget (mid N B))(K:Key I→ForceBudget (mid N B))(z:Key I): (ΠX (K' z) (K z) (r z)) U C x=Xz K' K z:= switched ..
 rw [funext (hu E F), (funext (hu Vq (fun z=>R.K+Vκ z)): (fun z=> (ΠX (Vq z) (R.K+Vκ z) (r z)) U C x)=Xz Vq (fun z=> R.K+Vκ z))]; let A:=Soft.plus (show Soft l Y Y from ⟨ht,ht,fun _ _=>rfl⟩) (castEra (P:=R.p) Sσ E _ q₀ v.token (fun i U=>congrArg (fun E=>exponentL R.p E U) (νVecE ..).symm) l vQ x.1)
 have hF:F=(fun z=>R.K+(F z-F 0)):=funext fun z=> by change _=R.K+_; rw [p]; abel
 -- only left. avoid recursive rw all
 have hr:= (castFuel (P:=R.p) Sσ F k.toll l vQ R.K x); rw [←hF] at hr; let hw:=uS_b _ vQ; exact ((A.expΩ hw).mul hr hw).graph Q.toContinuousLinearMap
end YM.CF.Vow.TreasuryFog
