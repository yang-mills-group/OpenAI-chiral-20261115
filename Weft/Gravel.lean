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
-- Generic totaling differentiation. Root test for table entries exact.
open Grain
variable {I:Type}[LinearOrder I][Fintype I]
variable (o:I→Site (mid N B))(hrs:Injective (Cube.node ∘ o))
local notation "Pt"=> PairKey I
local notation "mE"=> mid N B
abbrev grainE (i:PairKey I)(k:Bool):ℂ:= if i.2=k then 1 else 0
abbrev SuspectCa(o:I→Site (mid N B))(X': Key (PairKey I)→ RegBudget (mid N B)):=∀ (i:Scree.Hub (mid N B))(u:Pane (mid N B)),Grain (grainD o i.val.2) (fun z=>X' z i u)
abbrev SuspectZa(o:I→Site (mid N B))(F':Key (PairKey I)→ForceBudget (mid N B)):=∀ (i:Scree.Force (mid N B))(v:Orbit (mid N B)), Grain (grainD o i.val.1.val.2) (fun z=>F' z i v)
lemma entry_i(i:Pt)(z:Key Pt):Drift.entry (grainE i) (yard i) z=z i:=by
 cases e:i.2<;> simp only [Drift.entry,grainE,e, ↓reduceIte,Bool.true_eq_false,Bool.false_eq_true,mul_zero,zero_mul,zero_add,one_mul,add_zero] <;> exact congrArg z (Prod.ext rfl e.symm)
lemma grain_i{E:Type*}[AddCommGroup E][Module ℂ E](i:Pt){D:Finset I}(p:yard i ∈D)(c:E): Grain D (fun z:Key Pt=>z i • c):= by simpa only [prod_singleton,entry_i] using Grain.chip (D:=D) ({i}:Finset Pt) grainE c (by simp) (by intro x hx y hy _; simp_all) (by simpa using p) -- fix
local notation "Dq"=> sameY o
lemma pineD(i:Finset Pt)(J:Finset (Site (Domain N B)))(p: Set.InjOn (Cube.node ∘ sameY o) (i:Set Pt))(t:i.Nonempty){E:Type*}[AddCommGroup E][Module ℂ E](c:E)(d:poke_F (Cube.node ∘ sameY o) J i):Grain (grainD o J) (fun z:Key Pt=>Mew.pine i z • c):=by
 simpa only [entry_i,Mew.pine] using Grain.chip (D:=grainD o J) i grainE c t (fun _ hx _ hy h=>p hx hy (congrArg (Cube.node ∘ o) h)) (fun i hi=>mem_filter.mpr ⟨mem_univ _,d i hi⟩)
variable (X' Z':Key (PairKey I)→ RegBudget (mid P B))(K':Key (PairKey I)→ForceBudget (mid P B))(A W:PairKey I → ArcΦ)(D0:PairKey I→ℝ)(t0:PairKey I→ℂ)(E':Key (PairKey I)→ RegBudget (mid N B))(F':Key (PairKey I)→ForceBudget (mid N B))
variable (Cκ:Cause_P V U G S G₀ G₁ X Y X' Z' K' Xi q kL h Vp Va (sameY o) D0 A E' F' W t0 Bk Cμ Wη Eμ Cx ZΨ QΦ)
include V hrs Cκ
lemma gemE : SuspectCa o (Gem_U (sameY o) E'):=by
 have h(i:Finset Pt):=tiltP_S V (sameY o) E' F' X' Z' K' Xi D0 A W t0 Cκ i
 intro i u; unfold Gem_U Gem_Q; simp_rw [Pi.add_apply,Finset.sum_apply, Pi.smul_apply]; refine Grain.add (Grain.sum' _ _ (fun a _=> ?_)) (Grain.sum' _ _ (fun t v=>?_))
 · by_cases p:νΦX E' {a} i≠0
   · exact grain_i a (mem_filter.mpr ⟨mem_univ _, (h {a}).2 i p a (by simp)⟩) _
   push_neg at p; rw [show νTip E' a i u=0 from (cue_1 _ _).symm.trans (congrFun p u)]; simp_rw [smul_zero]; exact Grain.zero
 by_cases p:νΦX E' t i≠0
 · obtain ⟨ht,he⟩:=(mem_filter.mp v).2; exact pineD o t i.val.2 ht (Finset.card_pos.mp (by omega)) _ ((h t).2 i p)
 push_neg at p; rw [p]; change Grain _ (fun z=> _ • (0:Cipher (mid N B))); simp_rw [smul_zero]; exact Grain.zero
#check Gem_U
lemma gemY : SuspectZa o (Gem_K (sameY o) F'):=by
 have h(i:Finset Pt):=tiltP_S V (sameY o) E' F' X' Z' K' Xi D0 A W t0 Cκ i
 intro i u; unfold Gem_K; simp_rw [Pi.add_apply,Finset.sum_apply, Pi.smul_apply]; refine Grain.add (Grain.sum' _ _ (fun a _=> ?_)) (Grain.sum' _ _ (fun t v=>?_))
 · by_cases p:νΦK F' {a} i ≠0
   · exact grain_i a (mem_filter.mpr ⟨mem_univ _, (h {a}).1 i p a (by simp)⟩) _
   push_neg at p; rw [p]; change Grain _ (fun z:Key Pt=> z a • (0:Cipher (mid N B))); simp_rw [smul_zero]; exact Grain.zero
 by_cases p:νΦK F' t i≠0
 · obtain ⟨ht,he⟩:=(mem_filter.mp v).2; exact pineD o t i.val.1.val.2 ht (Finset.card_pos.mp (by omega)) _ ((h t).1 i p)
 push_neg at p; rw [p]; change Grain _ (fun z=> _ • (0:Cipher (mid N B))); simp_rw [smul_zero]; exact Grain.zero
lemma serve (C K D:ℝ) : SuspectCa o (FlameX (sameY o) E' (cobble I C K D))∧ SuspectZa o (FlameK (sameY o) F' (cobble I C K D)):=by
 constructor
 · intro i u; simp only [FlameX,step_key o hrs]; exact (gemE V Xi o hrs X' Z' K' A W D0 t0 E' F' Cκ i u).precomp _
 intro i u; simp only [FlameK,step_key o hrs]; exact (gemY V Xi o hrs X' Z' K' A W D0 t0 E' F' Cκ i u).precomp _
#print axioms serve
end YM.CF.Py
end
