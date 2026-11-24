import Weft.Gravel
import Weft.Bridge
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
variable (σ:J→Site (mid N B))(K_ E0:Key J→ RegBudget (mid N B))(F_:Key J→ ForceBudget (mid N B))
variable (Xo Yo:Key J→ RegBudget (mid P B))(Zo:Key J→ ForceBudget (mid P B)) {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} (Xi:Op SU.Slot){q:Chi}{h:ℝ}
local notation "Tz"=> Cube.node ∘ σ
local notation "P_"=> X.p
variable (Q:J→ℝ)(qE:J→ArcΦ)(qΨ:J→ ArcΦ)(s:J→ℂ)
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
open Grain
variable {I:Type}[LinearOrder I][Fintype I]
variable (o:I→Site (mid N B))(hrs:Injective (Cube.node ∘ o))
local notation "Pt"=> PairKey I
variable (X' Z':Key (PairKey I)→ RegBudget (mid P B))(K':Key (PairKey I)→ForceBudget (mid P B))(A W:PairKey I → ArcΦ)(D0:PairKey I→ℝ)(t0:PairKey I→ℂ)(E':Key (PairKey I)→ RegBudget (mid N B))(F':Key (PairKey I)→ForceBudget (mid N B))
variable (Cκ:Cause_P V U G S G₀ G₁ X Y X' Z' K' Xi q kL h Vp Va (sameY o) D0 A E' F' W t0 Bk Cμ Wη Eμ Cx ZΨ QΦ)
include V hrs Cκ
local notation "Dq"=> sameY o
omit V hrs Cκ
-- flaw field matrix.Larger.Layout.Camera.K.Clock. gemD basis eval.
open Ione Nacre
variable {E:Type*}[AddCommGroup E][Module ℂ E]
lemma pulse_off(i j:Pt)(h:j≠i): Grain.pulse (yard i) (altQ i) 1 j=0:=update_of_ne h ..
lemma unitStem(i:Pt)(f:Pt→E): (∑ j:Pt,(Grain.pulse (yard i) (altQ i) 1 j) • f j)=f i:=by
 rw [sum_eq_single i (fun b _ p=> by rw [pulse_off i b p,zero_smul]) (by simp),show Grain.pulse (yard i) (altQ i) 1 i=1 from pulse_self ..,one_smul]
lemma pine_φ(i:Pt)(t:Finset Pt)(p:1<t.card): Mew.pine t (Grain.pulse (yard i) (altQ i) 1)=0:=by
 have e: ∃ j∈t,j≠i:=by by_contra! he; have h:=card_le_card (show t⊆{i} from fun j h=> Finset.mem_singleton.mpr (he j h)); exact (not_le.mpr p) ((h.trans_eq (card_singleton _))) -- trans_eq gives ≤
 obtain ⟨j,h,p⟩:=e; exact prod_eq_zero h (pulse_off i j p)
lemma dropq (i:Pt)(a:Finset Pt→E): (∑ j∈ MixT (sameY o), Mew.pine j (Grain.pulse (yard i) (altQ i) 1) • a j)=0:=sum_eq_zero fun j h=>by rw [pine_φ _ _ (mem_filter.mp h).2.2,zero_smul]
lemma entry_one (F:Bool→ℂ)(j:I)(k:Bool):Drift.entry F j (Grain.pulse j k 1)=F k:=by
 cases k<;> simp [Drift.entry,pulse_oth]
lemma fiber_solo (C:Bool→Bool→ℂ)(i:Pt):fiber C (Grain.pulse i.1 i.2 1)=duo i.1 (C false i.2) (C true i.2):=by
 funext j; rcases j with ⟨a,b⟩; by_cases p:a=i.1
 · subst a; cases b
   · exact (entry_one _ _ i.2).trans (duo_selfU ..).symm
   exact (entry_one _ _ i.2).trans (duo_selfV ..).symm
 exact (entry_off a i.1 i.2 p ..).trans (crop i.1 _ _ a p b).symm
abbrev tipκ {n:Side}(f:Key (PairKey I)→ ForceBudget n)(i:PairKey I):ForceBudget n:= fun b u=> Mew.tipI (fun z=>f z b u) [i]
lemma pillE(i:Pt):Gem_U (sameY o) E' (Grain.pulse i.1 i.2 1) = νTip E' i:=by
 unfold Gem_U Gem_Q; rw [unitStem i,dropq o i,add_zero]
lemma pillK(i:Pt):Gem_K (sameY o) F' (Grain.pulse i.1 i.2 1)= tipκ F' i:=by
 unfold Gem_K; rw [unitStem i,dropq o i,add_zero]; funext b u; exact cue_1 ..
include V hrs Cκ
lemma aromaX (k e v:ℝ)(i:Pt): νTip (FlameX (sameY o) E' (cobble I k e v)) i = (stone k e v false i.2) • νTip E' (pick i.1 false)+(stone k e v true i.2) • νTip E' (pick i.1 true):=by
 let G':=Gem_U (sameY o) E'; let c:=stone k e v; funext j u; change tipI (fun z=>FlameX (sameY o) E' (cobble I k e v) z j u) [i] = _ -- syntax? explicit binder
 simp only [FlameX,step_key o hrs]; let F'':=fun z=> G' z j u
 have h:= gemE V Xi o hrs X' Z' K' A W D0 t0 E' F' Cκ j u; change tipI (fun z=> F'' (fiber c z)) [i]= _
 rw [(Grain.horn (h.precomp c) i), fiber_solo]
 let t(b):= pick i.1 b
 have x(b:Bool):Gem_U (sameY o) E' (Grain.pulse i.1 b 1) j u=νTip E' (t b) j u:=congrFun (congrFun (pillE o E' (t b)) j) u
 exact (h.radios i.1 (c false i.2) (c true i.2)).trans (congrArg₂ (·+·) (congrArg (c false i.2 • ·) (x false)) (congrArg (c true i.2 • ·) (x true)))
lemma aromaY (k e v:ℝ)(i:Pt): tipκ (FlameK (sameY o) F' (cobble I k e v)) i = (stone k e v false i.2) • tipκ F' (pick i.1 false)+(stone k e v true i.2) • tipκ F' (pick i.1 true):=by
 let G':=Gem_K (sameY o) F'; let c:=stone k e v; funext j u; unfold tipκ
 simp only [FlameK,step_key o hrs]; let F'':=fun z=> G' z j u
 have h:= gemY V Xi o hrs X' Z' K' A W D0 t0 E' F' Cκ j u; change tipI (fun z=> F'' (fiber c z)) [i]= _
 rw [(Grain.horn (h.precomp c) i), fiber_solo]
 let t(b):= pick i.1 b
 have x(b:Bool):Gem_K (sameY o) F' (Grain.pulse i.1 b 1) j u=tipκ F' (t b) j u:=congrFun (congrFun (pillK o F' (t b)) j) u
 exact (h.radios i.1 (c false i.2) (c true i.2)).trans (congrArg₂ (·+·) (congrArg (c false i.2 • ·) (x false)) (congrArg (c true i.2 • ·) (x true)))
#print axioms aromaX
#print axioms aromaY
end YM.CF.Py
end
