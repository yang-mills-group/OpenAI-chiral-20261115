import Bay.C.Blush
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Bay.C
open QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise



set_option synthInstance.maxHeartbeats 160000

private lemma duties (k p:ℕ): 1≤duty_Q k p ∧ 1 ≤ strive_E k:=by
 have h:1≤ (k.factorial:ℝ) :=Nat.one_le_cast.mpr (Nat.factorial_pos _)
 have j:1≤(k+1:ℝ):=le_add_of_nonneg_left (Nat.cast_nonneg _)
 exact ⟨one_le_mul_of_one_le_of_one_le (mul_one (_:ℝ) ▸h)
   (one_le_pow₀ (le_add_of_nonneg_right (by positivity))),
  one_le_mul_of_one_le_of_one_le j
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h h) (one_le_pow₀ (by norm_num)))⟩

variable {N B:Side}{P:BudgetPoint}{h E D C:ℝ}
local notation "HubS"=>mid N B

private lemma icq {u:RegBudget HubS}
 (p:IncX primeU u P h E)(h0:0≤h): IncX primeU u P h (duty_Q P.order P.power * E):=by
 obtain ⟨⟨q,g,v⟩,a⟩:=p
 refine ⟨⟨q,g,fun i=>(v i).trans (le_mul_of_one_le_left ?_ (duties ..).1)⟩,a⟩
 refine (sum_nonneg ?_).trans (v i)
 intro j _
 have w:0≤q j:=by
   obtain ⟨b,y,_,u⟩:=(g j).worth
   exact (sum_nonneg fun k _=>mul_nonneg (by unfold Scree.tariff; positivity) (y k)).trans u
 split
 · unfold BudgetPoint.mass
   positivity
 exact le_rfl

private lemma deepen {L:ℕ}{x:Site HubS}
 {w:Copy HubS}{u:RegBudget HubS}{v:Cusp HubS}{z:ℂ}{r:ArcΦ}
 (p:Neon.Ice L x P h E D C w u v z r)(h0:0≤h):
 Neon.Ice L x P h (duty_Q P.order P.power * E) (strive_E P.order * D) C w u v z r:=by
 obtain ⟨⟨a,b,d⟩,f,k,⟨q,w,p,e⟩,i⟩:=p
 refine ⟨⟨icq a h0,b,d⟩,f,k,⟨q,w,fun j=>(p j).trans (le_mul_of_one_le_left ?_ (duties _ 1).2),e⟩,i⟩
 exact (sum_nonneg fun y _=>mul_nonneg (w.1 y) (Real.exp_pos _).le).trans (p j)

section
variable {P₁:Side}{l:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}
  (V:Grace K l L) {e:ℝ}(P_:Grasp V.U B e)
  (G:Ratio (mid N B) (mid P₁ B))(S:StepData (Domain N B) (Domain P₁ B))
  (G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P₁ B))(X:GramM (mid N B))(Y:GramM (mid P₁ B))(Xp:Op SU.Slot)
  (q:Chi)(d Vp Vf T W Ce BQ Rt Zt κp:ℝ)
variable (Be:Observatory G X.p)(Vk:Cusp (mid N B))(Ca:ArcΦ→ℝ→ℝ)(nf:ℕ)
variable {J:Type}[LinearOrder J][Fintype J](r:J→Site (mid N B))(E0:Key J→RegBudget (mid P₁ B))
 (Y0:Key J→ForceBudget (mid P₁ B))(u:J→ArcΦ)(A:J→ℝ)
 (Fv:Key J→Cusp (mid N B))(E':J→RegBudget (mid N B))(G':J→Cusp (mid N B))(τ:J→ℂ)(v':J→ArcΦ)

local notation "Qν" => fun z=>rust_L X.p (Fv z) (Vk+Φstack G' z)
structure Namesakes (R': Key J→RegBudget (mid N B)):Prop where
 source:∀ z∈hill J,Be.source (E0 z) (Y0 z) (Fv z)
 table:∀ i x,River (fun z=>heat_P X.p Fv z i x)
 fee : ∀i:J,let k:=nun_ω Y.F (heel G (r i)); let R:=κprobe mintR l.L h (A i) T k (u i)

   Neon.Ice l.L.val (r i) X.p h (W*R) (Ca (u i) (A i)) (Ce*R)
     (feeTip X.p Fv i) (E' i) (G' i) (τ i) (v' i)
 sent:Cause_P V P_ G S G₀ G₁ X Y E0 0 Y0 Xp q d h Vp Vf r A u R' (Qν) v' τ T
   (duty_Q X.p.order X.p.power*W) Ce BQ Rt Zt κp
 size:∀z∈hill J,FlagWidth X.p ((Qν) z) nf
 outlet:∀i,νTip R' i=E' i


structure Ignition (r:J→Site (mid N B)) where
 Fv:Key J→Cusp (mid N B)
 E':J→RegBudget (mid N B)
 G':J→Cusp (mid N B)
 τ:J→ℂ
 κ:J→ArcΦ
 R':Key J→RegBudget (mid N B)

abbrev Passage (D':Ignition r):Prop:=
 Namesakes (h:=h) V P_ G S G₀ G₁ X Y Xp q d Vp Vf T W Ce BQ Rt Zt κp Be Vk Ca nf
   r E0 Y0 u A D'.Fv D'.E' D'.G' D'.τ D'.κ D'.R'

-- keep Observatory common: ∀ layouts after its choice.
lemma heatRun {cost g:ℝ}{M:ℕ}
 (p:OrbitJet V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W Ce BQ Rt Zt cost g κp Be Vk Ca nf M)
 (ha:0≤h)(f:OrbitPulse G X Y h cost g l.L r E0 Y0 u A M):
 ∃o,Passage (h:=h) V P_ G S G₀ G₁ X Y Xp q d Vp Vf T W Ce BQ Rt Zt κp Be Vk Ca nf r E0 Y0 u A o:=by
 obtain ⟨F,t,k,y,e⟩:=p.heat _ _ _ _ _ f
 dsimp only at y
 choose R Z w κ v a using y
 obtain ⟨Y,c,m,s⟩:=e R Z κ w (fun i=>⟨deepen (v i) ha,a i⟩)
 exact ⟨⟨F,R,Z,w,κ,Y⟩,⟨t,k,v,c,m,s⟩⟩
