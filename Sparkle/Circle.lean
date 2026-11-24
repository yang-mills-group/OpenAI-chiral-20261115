import Sparkle.Land
import Sparkle.Seed
set_option autoImplicit false
set_option maxHeartbeats 2200000
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
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
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
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
-- earnings profiles quant issued b through \ell. Accept permit Rent
open Larch Vow Bake Mew Roots Rive Neon
local notation "BN"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
local notation "Θ"=> X.p.supportExponent
variable {J:Type}[LinearOrder J][Fintype J]
variable (σ:J → Site (mid N B))(K_ E0:Key J →  RegBudget (mid N B))(F_:Key J →  ForceBudget (mid N B))
variable (Xo Yo:Key J →  RegBudget (mid P B))(Zo:Key J →  ForceBudget (mid P B)) {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} (Xi:Op SU.Slot){q:Chi}{h:ℝ}
local notation "Tz"=> Cube.node ∘ σ
local notation "P_"=> X.p
variable (Q:J → ℝ)(qE:J → ArcΦ)(qΨ:J →  ArcΦ)(s:J → ℂ)
variable {Vp Va Bk Cμ Wη Eμ Cx ZΨ QΦ ξQ:ℝ} -- remove
variable (Fκ:Cause_P V U G S G₀ G₁ X Y Xo Yo Zo Xi q kL h Vp Va σ Q qE K_ F_ qΨ s Bk Cμ Wη Eμ Cx ZΨ QΦ)
open Roots Mew Rive Oise
variable {α:Type}[DecidableEq α]
open scoped YM.CF.Mew
local notation "Ω"=> mid N B
local notation "qμ"=> (Cube.node ∘σ)
local notation "Ωk"=> MixT σ
open Drift Oise
attribute [-instance] instDecidableEqLex
open Compass
namespace Dyad
open Swell Compass Taxi Ione Tune Grain
-- indexing universe. B fixed. 
namespace Keeping
variable (A: SiteLedger V U kL q)
#check SiteLedger
local notation "Sc" i:max=>mid (A.side i) B
variable {I:Type}[LinearOrder I][Fintype I]
#check geo
local notation "LogA" i:max=> heir V A I i
local notation "Geo" i:max=> geo (I:=I) V A i
variable (v0 f:ℕ)(hzT κ Vq:ℝ)
local notation "τ" k:max=> A.money k
local notation "bT" k:max=> (A.gram k).p.B
local notation "Spr" i:max=> sap (N:=A.side i) (B:=B) (A.gram i).p (A.money i)
local notation "Cure" i:max=> TraceS (mid (A.side i) B)
-- IR Scope. Makers indexed $C common regardless r, D per-r. n0. i=r store only weak Lawn. Good when pressure-turning (order1 estimate at most Aρ, Uc, use sparse)
variable {C Dσ:ℕ → ℝ}{D:ℕ → ℕ → ℝ}(i0:ℕ)(e0:i0<v0)
variable (hx:∀ (i:ℕ),f ≤  i → i ≤ v0 →  ∀ (I:Type)[LinearOrder I][Fintype I](o:I → Site (mid (A.side i) B)),Very_Ψ o (A.gram i).p.B →  Chew hzT (A.money i) κ Vq R.L (A.gram i) (sap (A.gram i).p (A.money i) false) (sap (A.gram i).p (A.money i) true) o (leafER o (A.gram i).p (A.money i)))
  (kE:∀ i:ℕ,f ≤  i → i<v0 →  KnollStep V U kL hzT (A.gram i) (A.gram (i+1)) (A.job i) (A.ratio i) (A.plant i) (A.plant (i+1)) (A.opT i) q (A.money (i+1)) (A.money i) κ Vq)
  (liftV:∀ i,f ≤  i → i<v0 → ∀ (I:Type)[LinearOrder I][Fintype I](o:I → Site (mid (A.side i) B)), Very_Ψ o (A.gram i).p.B →  Very_Ψ (adapt V A i o) (A.gram (i+1)).p.B)
variable (hH:1 ≤ hzT)(hp:0 ≤ κ)(hb:0 ≤  Vq)(p_:∀ i,f ≤  i → i ≤ v0 → 0 ≤ A.money i)
namespace Office
variable (hx0:f ≤  i0)(hv0:i0 ≤ v0)
variable (M Mp:TraceS (mid (A.side i0) B))(Lh:ℕ →  TraceS (mid (A.side i0) B))
include hx hH p_ hp hb kE liftV
lemma scrollFull (hF:f≤v0):∃ (C:ℕ→ℝ)(D:ℕ→ℕ→ℝ),∀ j,f≤ j→ j≤v0→ Accounts V A v0 hzT κ Vq C D j:=by
 let Y:ℕ→Prop:=fun j=>∃ (C:ℕ→ℝ)(D:ℕ→ℕ→ℝ),∀ k,j≤ k→ k≤v0→ Accounts V A v0 hzT κ Vq C D k
 suffices hf:∀ n:ℕ,n+f≤v0→Y (v0-n) by
    have ht:=hf (v0-f) (by omega); rwa [show v0-(v0-f)=f from (by omega)] at ht
 intro n
 induction n
 case zero=>intro h; rw [Nat.sub_zero]; refine ⟨0,0,fun i h x=>?_⟩; cases le_antisymm x h
            exact primary V A v0 f hzT κ Vq v0 hx hH hp hb p_ hF hF -- #check
 case succ j p=>
    intro hv
    let i:=v0-(j+1); have hs:v0-j=i+1:=by unfold i; omega
    have v':f ≤ i:=by unfold i; omega
    have hV:i<v0:=by unfold i; omega
    obtain ⟨C,D,P⟩:=hs ▸ (p (by omega))
    obtain ⟨M,Mp,L,hM⟩:=P (i+1) le_rfl hV
    obtain ⟨C',D',e,q,s⟩:= film V A v0 f hzT κ Vq i hV hx kE liftV hH hp hb p_ v' M Mp L hM
    refine ⟨C',D',?_⟩
    intro k hv0 v
    rcases eq_or_lt_of_le hv0 with rfl|u
    · exact e
    obtain ⟨a,b,c,y⟩:=P k u v
    exact onward V A v0 hzT κ Vq k _ _ _ y C' D' (fun j v=> q j (u.trans_le v)) (fun k' j v=>s k' j (u.trans_le v)) -- order
#check primary
#check onward
#print axioms scrollFull
end Office
end Keeping
end Dyad
end YM.CF.Py
end
