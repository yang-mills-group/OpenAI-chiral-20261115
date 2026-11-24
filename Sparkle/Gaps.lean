import Sparkle.Curvature
import Sparkle.Axer
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
namespace Dyad
open Swell Compass Taxi Ione Tune Grain
open Drift Ione Both
local notation "mH"=>mid N B
variable {I:Type}[LinearOrder I][Fintype I](o:I→Site (mid N B))
local notation "Iκ"=>PairKey I
-- block collapse and splice channels.
def duplicate(i _:Bool):ℂ:= if i then 0 else 1
def parasitic(i j:Bool):ℂ:= if i then 0 else if j then 1 else 0
abbrev reinforce (l0 l1:Log I mH):Log I mH:=⟨(fun z=>l0.earn (fiber duplicate z)-l1.earn (fiber parasitic z)),(fun z=>l0.wake (fiber duplicate z))⟩
abbrev gapSeal {m:Side}(T1 T2:TraceS m):TraceS m where
 r(v):=T1.r v-T2.r v
 t:=T1.t
 holds :=⟨fun w v=>by rw [map_sub,T1.holds.rill,T2.holds.rill,smul_sub],T1.holds.mark⟩
variable (Tt Tg Pt Pg:TraceS (mid N B))(br κw Vq:ℝ)(Lq Pq:Log I (mid N B))
  (cq:Chew Hh br κw Vq R.L X Tt Tg o Lq)(cp:Chew Hh br κw Vq R.L X Pt Pg o Pq)
lemma pinDuet(i:Iκ): duo i.1 1 0= Grain.pulse i.1 false 1:= (singleU i.1 false 1).symm
lemma pinVac(i:Iκ): duo i.1 0 0=0:=by
 suffices h:Grain.pulse i.1 false 0=0 from (singleU i.1 false 0).symm.trans h
 funext k; by_cases q:k=pick i.1 false; subst k; exact pulse_self ..; exact update_of_ne q ..
lemma above(i:Iκ)(b:Scree.Hub (mid N B))(v:Pane mH): (reinforce Lq Pq).earn (Grain.pulse i.1 i.2 1) b v = Lq.earn (Grain.pulse i.1 false 1) b v - Pq.earn (if i.2 then Grain.pulse i.1 false 1 else 0) b v:=by
 change (Lq.earn (fiber duplicate (Grain.pulse i.1 i.2 1))-Pq.earn (fiber parasitic (Grain.pulse i.1 i.2 1))) b v=_; rw [fiber_solo duplicate i,fiber_solo parasitic i]; unfold duplicate parasitic; change (Lq.earn (duo _ 1 0)-Pq.earn (duo _ (if i.2 then 1 else 0) 0)) b v=_; cases e:i.2; exact congrArg₂ (·-·) (congrArg (fun t=>Lq.earn t b v) (pinDuet i)) (congrArg (fun t=>Pq.earn t b v) (pinVac i)); exact congrArg₂ (·-·) (congrArg (fun t=>Lq.earn t b v) (pinDuet i)) (congrArg (fun t=>Pq.earn t b v) (pinDuet i)) -- syntax
include cq cp
lemma synergy : SuspectCa o (reinforce Lq Pq).earn ∧ SuspectZa o (reinforce Lq Pq).wake:=by
 constructor
 · intro i v; let D:=grainD o i.val.2; change Grain D (fun z=>Lq.earn _ _ _-Pq.earn _ _ _); simp_rw [sub_eq_add_neg]; exact ((cq.1.age.1 ..).precomp duplicate).add ((cp.1.age.1 i v).precomp parasitic).neg'
 intro i v; exact (cq.1.age.2 i v).precomp duplicate
lemma repLabel(k:Iκ): νTip (reinforce Lq Pq).earn k=νTip Lq.earn (pick k.1 false)-(if k.2 then νTip Pq.earn (pick k.1 false) else 0):=by
 have h:=(synergy o Tt Tg Pt Pg br κw Vq Lq Pq cq cp).1
 funext i v; refine ((h i v).horn k).trans ((above Lq Pq k i v).trans ?_)
 cases e:k.2
 · change _- (Pq.earn 0 _ _)= (νTip Lq.earn _ _ _)-_ ; rw [(cp.1.age.1 i v).dawnQ, ← show tipI _ [pick k.1 false]=_ from (cq.1.age.1 i v).horn _]; rfl
 exact congrArg₂ (·-·) ((cq.1.age.1 i v).horn (pick k.1 false)).symm ((cp.1.age.1 i v).horn (pick k.1 false)).symm
lemma repFo(k:Iκ): tipκ (reinforce Lq Pq).wake k=tipκ Lq.wake (pick k.1 false):=by
 funext i v; let p:=cq.1.age.2 i v
 refine (((p.precomp duplicate).horn k).trans ?_); change Lq.wake _ _ _= tipI _ _
 rw [fiber_solo duplicate k,p.horn]; exact congrArg (fun z=>Lq.wake z i v) (pinDuet k)
lemma reinforcePass (hS:0≤br)(hκ:0≤κw)(hV:0≤Vq)(hH:1≤Hh): Lawn Hh br κw Vq R.L X Tt (gapSeal Tt Pt) o (reinforce Lq Pq):=by
 have hv:=cq.1; have h':=cp.1
 let F(z:Key Iκ)(i:I):=z (pick i false)+z (pick i true)
 have hF(z:Key Iκ)(p:∀ i,‖z i‖≤1)(i:Iκ):‖fiber duplicate z i‖≤2∧‖fiber parasitic z i‖≤2:=by
    have h_:1+1=(2:ℝ):=by norm_num
    cases t:i.2
    · simp [fiber,Drift.entry,parasitic,duplicate,t,altQ]; exact ⟨((norm_add_le ..).trans ((add_le_add (p _) (p _)).trans_eq h_)),(p _).trans (by norm_num)⟩
    simp [fiber,Drift.entry,parasitic,duplicate,t,altQ]
 let t:=κw*br
 have ht:t/4≤t:=by have he:0≤t:=mul_nonneg hκ hS; linarith
 have hz(k:Iκ):=repLabel _ Tt Tg Pt Pg _ _ _ Lq Pq cq cp k
 have h0:soot br true=0:=by
    refine Prod.ext ?_ rfl; change paintS 0 = 0; rw [←zero_mul (1:ℂ),←coat_scale,zero_smul]
 refine ⟨⟨synergy o Tt Tg Pt Pg br κw Vq Lq Pq cq cp,fun z p=>?_,fun i=>?_⟩,?e⟩
 · obtain ⟨a,b⟩:=hv.span (fiber duplicate z) (fun i=>(hF z p i).1)
   obtain ⟨c,d⟩:=h'.span (fiber parasitic z) (fun i=>(hF z p i).2)
   have hc:=Ione.thin_P X.p _ (-1) c; simp only [neg_smul,one_smul,abs_neg,abs_one,one_mul] at hc
   let A:= Vq*br; have hA:0≤ A:=mul_nonneg hV hS
   refine ⟨?_,Provides.liftQ Hh X _ _ b (show A/4 ≤ A by linarith)⟩
   exact Provides.liftE Hh X _ _ (by rw [reinforce]; change IncX _ (_-_) _ _ _; rw [sub_eq_add_neg]; exact Larch.add_v _ _ _ a hc) (show A/4+A/4≤ A by linarith)
 · cases e:i.2
   · rw [hz i,e]; simp only [Bool.false_eq_true,↓reduceIte,sub_zero]
     exact turf_A _ _ _ _ _ (t/4) t ht (cq.1.taste (pick i.1 false))
   rw [hz i,e, if_pos rfl,h0]
   have ht1:=cq.1.taste (pick i.1 false); have ht2:= charge_ν (-1) _ _ _ _ _ _ (zero_le_one.trans hH) (cp.1.taste (pick i.1 false)); simp only [norm_neg,norm_one,one_mul,neg_smul,one_smul] at ht2
   have y:=Axon_add (o i.1) _ _ ht1 ht2 (zero_le_one.trans hH); rw [add_neg_cancel (soot br false)] at y; rw [sub_eq_add_neg]; apply turf_A _ _ _ _ _ _ _ (show t/4+t/4≤t from by unfold t; nlinarith only [mul_nonneg hκ hS]) y
 case e=>
   refine ⟨fun i=>?_,fun i t v z=>?_⟩
   · rw [hz i]; rw [cq.2.gaze,cp.2.gaze]; cases e:i.2 <;> simp only [Bool.false_eq_true,↓reduceIte,sub_zero] <;>rfl
   exact (congrFun (congrFun (repFo _ Tt Tg Pt Pg _ _ _ Lq Pq cq cp i) z) t).trans ((cq.2.foam (pick i.1 false) t v z).trans (by cases e:i.2<;>rfl))
#print axioms reinforcePass
end Dyad
end YM.CF.Py
end
