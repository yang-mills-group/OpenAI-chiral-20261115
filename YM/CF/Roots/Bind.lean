import YM.CF.Roots.Sail
import YM.CF.Fans.Cause
import YM.CF.Roots.Flux
import YM.CF.Roots.Melt
import YM.CF.Fans.Emit
import YM.CF.Neon.Park
import YM.CF.Fans.Moon
import YM.CF.Fans.Wake
import YM.CF.Fans.Pose
import YM.CF.Neon.Quay
import YM.CF.Neon.Lux
import YM.CF.Fans.Toll
import YM.CF.Rive.Lob
import YM.CF.Ups.Tree
import YM.CF.Ups.Shea
import YM.CF.Paxos.Pen
import YM.CF.Pso.Tide
import YM.CF.Pso.Wage
import YM.CF.Pso.Azim
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
section proof
open Rive Vow Mew Roots Oise
variable {α:Type}[DecidableEq α]{m₃:Side}(σ:J→α)(C:J→J→ℂ)(Z₀:List J)
local notation "ΓS"=> Storm_C σ C Z₀
variable(pS: Roots.ψS σ Z₀)
-- tank complex linear independent of chirality projection for formal relations.
def tankL (A:Op (Single N)): Cipher N →L[ℂ] FC (Single N):= by
 refine LinearMap.toContinuousLinearMap {toFun:=tank A,map_add':=?_,map_smul':=?_}
 · intro x y; unfold tank; rw [← Finset.sum_add_distrib]; apply sum_congr rfl; intro i _; rw [show crumb (_:Cipher N).val i= crumb x.val i+crumb y.val i from rfl, add_smul]; -- `crumb` linear by rfl?
 intro c x; unfold tank; rw [Finset.smul_sum]; apply sum_congr rfl; intro i _; change _ • _=_; rw [smul_smul]; rfl
def tale_L (a: Phys N) : FC (Single N)→L[ℂ] Phys N:= LinearMap.toContinuousLinearMap {toFun:=fun z=> acts z a,map_add':=fun _ _=>act_add ..,map_smul':=fun _ _=>act_smul ..}
def hollow_L : ℂ →L[ℂ]Cipher N:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) 1
variable (V0:GramM (mid N B))(L0:Scree.Loom (mid N B))(Fp' F1 G0 G1:Key J→ RegBudget (mid N B))(K1 K2: Key J→ForceBudget (mid N B))(q0 q1: Key J→ℂ)
local notation "Ω"=> mid N B
local notation "RΓ" v:max=> color_b V0 V0.beta (Fp' v) (G0 v) (K1 v) (q0 v)
local notation "QΓ" v:max=> color_b V0 V0.beta (F1 v) (G1 v) (K2 v) (q1 v)
variable {f g: Key J→Cipher BN}
abbrev Law_C {J:Type*}[Fintype J][LinearOrder J]{α:Type*}[DecidableEq α]{F:Type*}[NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F](σ:J→α)(C:J→J→ℂ)(L:List J)(f g:Key J→F):= River f∧ River g∧ Storm_C σ C L f g
variable {U':Key J}(W:Orbit (mid N B))
variable(h_:∀ i v, Law_C σ C Z₀ (fun z=>Fp' z i v) (fun z=> F1 z i v))(hR:∀ i v, Law_C σ C Z₀ (fun z=>G0 z i v) (fun z=>G1 z i v))(hK:∀ i v,Law_C σ C Z₀ (fun z=>K1 z i v) (fun z=>K2 z i v)) (hq:Law_C σ C Z₀ q0 q1)
lemma σtag_l {F:Type*}[NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F](c:F):Law_C σ C Z₀ (fun _=>c) (fun _=>c):=⟨zeroR _,zeroR _,constant_C σ C c⟩
include h_
lemma reg_F : Law_C σ C Z₀ (fun z=>exponentL V0.p (Fp' z) W.1) (fun z=> exponentL V0.p (F1 z) W.1):= by
 refine sumY_C σ C univ _ _ ?_; intro j p; by_cases q:pingS V0.p.threshold j.val.2 W.1
 · change Law_C σ _ _ (fun z=>numbE _ _ (Fp' z j) _) (fun z=> numbE _ _ (F1 z j) _); unfold numbE; simp_rw [Set.indicator_of_mem (show W.1∈{W|pingS V0.p.threshold j.val.2 W} from q)]; exact h_ ..
 change Law_C σ _ _ (fun z=>numbE _ _ (Fp' z j) _) (fun z=> numbE _ _ (F1 z j) _); unfold numbE; simp_rw [Set.indicator_of_notMem (show W.1∉{W|pingS V0.p.threshold j.val.2 W} from q)]; exact σtag_l ..
omit h_
include hK pS
lemma for_B : Law_C σ C Z₀ (fun z=> fueled V0.p (K1 z) W) (fun z=> fueled V0.p (K2 z) W):=by
 let f(k:Key J→ForceBudget Ω)(z:Key J)(j:Finset (Force Ω)):= if coverF V0.p j W.1∧Set.PairwiseDisjoint (j:Set _) (fun x:Force Ω=> x.val.1.val.2) then ∏ i∈j, clamp V0.p i (k z i) W else 0; refine sumY_C σ C univ (fun j z=>f K1 z j) (fun j z=>f K2 z j) ?_
 intro i g; unfold f; split; swap; exact σtag_l ..
 refine prodY_C σ C i _ _ pS fun j p=>?_ ; change Law_C σ C Z₀ _ _
 unfold clamp; split; exact hK ..; exact σtag_l ..
include h_ hR hq
lemma pulse_H : Law_C σ C Z₀ (fun z=> Scree.denZ (RΓ z) U L0 W) (fun z=>Scree.denZ (QΓ z) U L0 W):=by
 let p:=V0.p; let f(z):= exponentL p (Fp' z) W.1+exponentL p (G0 z) W.1; let g(z):=exponentL p (F1 z) W.1+exponentL p (G1 z) W.1; let F(z):=(RΓ z).board W; let G(z):=(QΓ z).board W
 obtain ⟨x,v,t⟩:= reg_F σ C Z₀ V0 _ _ W h_; obtain ⟨xp,up,r⟩:= reg_F σ C Z₀ V0 _ _ W hR; let hF:River f:=dub_V x xp; let hG:River g:=dub_V v up; have hn : Law_C σ C Z₀ F G:=by
    obtain ⟨e,k,u⟩:= for_B σ C Z₀ pS V0 K1 K2 W hK; exact ⟨hF.exp_V.mul_T e,hG.exp_V.mul_T k,roof_e σ C hF.exp_V e hG.exp_V k pS (root_e _ _ hF hG pS (Aζ σ C x xp v up t r)) u⟩ -- arg order
 let c:= V0.betaL L0 W-V0.v; let Qx(z):= exp (q0 z+c); let Qy(z):=exp (q1 z+c); have hx : Law_C σ C Z₀ Qx Qy:=⟨(dub_V hq.1 (zeroR _)).exp_V,(dub_V hq.2.1 (zeroR _)).exp_V, root_e _ _ (dub_V hq.1 (zeroR c)) (dub_V hq.2.1 (zeroR c)) pS (Aζ _ _ hq.1 (zeroR _) hq.2.1 (zeroR _) hq.2.2 (constant_C σ C c))⟩ -- c eval
 let KK:ℂ→L[ℂ] Cipher Ω:= hollow_L; let L:= (tale_L (Scree.relV U V0.J (L0 W))).comp (tankL (spar K.j V0.J.M (L0 W))) -- K name shadow fix.
 have hp: Law_C σ C Z₀ ((KK ∘ Qx)* F) ((KK ∘Qy)*G):= by obtain ⟨x,v,t⟩:= hx; obtain ⟨g,h,p⟩:=hn; exact ⟨(sc_V x KK).mul_T g,(sc_V v KK).mul_T h,roof_e _ _ (sc_V x KK) g (sc_V v KK) h pS (scope_C _ _ x v t KK) p⟩
 have hy: Law_C σ C Z₀ (L∘ ((KK ∘Qx)*F)) (L ∘ ((KK ∘Qy)*G)):=⟨sc_V hp.1 L,sc_V hp.2.1 L,scope_C _ _ hp.1 hp.2.1 hp.2.2 L⟩
 have htT(z:ℂ)(F G:RegBudget Ω)(X:ForceBudget Ω):let Wq:=color_b V0 V0.beta F G X z; Scree.denZ Wq U L0 W=L ((KK (exp (z+c)))*(Wq.board W)):=by
    intro Vq; have hw:Vq.betaL L0 W=z+c:=by unfold GramM.betaL GramM.H0 c GramM.betaL GramM.H0 Vq color_b; dsimp only; ring
    unfold Scree.denZ; rw [hw]; change _=L ((exp (z+c)) • 1* _); rw [smul_mul_assoc, one_mul,map_smul]; rw [←Complex.exp_eq_exp_ℂ]; rfl
 change Law_C σ _ _ _ _; simp_rw [htT]; exact hy
end proof
end YM.CF.Py
