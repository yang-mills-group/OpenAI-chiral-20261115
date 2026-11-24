import Palm.Trek
import Knotwise.Spawns
import Finance.Price
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

lemma boltLift (Y:J→ArcΦ)(M:J→RegBudget (mid N B))(Γφ tU:ℝ)(tT:ℕ)(qM:∀ i,Axon R.L.val (σ i) X.p (M i) h Γφ (Y i))(z:Key J)(u:∀ j,‖z j‖≤tU)(q:0≤tU)(pc:Force_M X.p.B (Cube.node ∘ σ) tT)(hX:1≤h)(hB:0≤ Γφ): IncX primeU (∑ i:J,z i • M i) X.p h (tT*(tU*Γφ)):=by
 let E:= M
 choose G p w using fun i=>(qM i).vest.weight; let L(j:J)(x:Η):= if x.val.1=node (σ j) then G j x else 0
 have hv:=zero_le_one.trans hX; have hz(i:J)(x:Η):PressB X.p x (E i x) h (L i x):=by unfold L; split; exact p ..; next t=> rw [show E i x=0 from (qM i).site _ t]; exact Vale.rinse ..
 let v(x:Η):=∑ i:J,‖z i‖ * L i x; refine ⟨⟨v,fun x=>?_,fun r=>?_ ⟩,fun _ p=>p.elim⟩
 · rw [Finset.sum_apply]; exact Larch.prop_sum univ _ _ _ _ x (fun j _=>súe _ _ (hz ..) (z j)) -- tune
 let I:=univ.filter fun i : J=> node (σ i)=r; have he:I.card ≤tT:=(card_le_card (show I⊆ _ from ?_)).trans (pc.2 r)
 swap; · intro k t; refine mem_filter.mpr ⟨mem_univ _,?_⟩; rw [Function.comp_apply,(mem_filter.mp t).2,separation_self]; omega
 rw [←sum_filter]; let U:= univ.filter fun x:Η=>r=x.val.1
 have hp(x:Η)(b:x∈ U): v x= ∑ i∈ I,‖z i‖* L i x:= Eq.symm (Finset.sum_subset (filter_subset ..) fun i _ q=> by unfold L; rw [if_neg (fun e=> q (mem_filter.mpr ⟨mem_univ _, e.symm.trans (mem_filter.mp b).2.symm⟩)),mul_zero])
 refine (le_trans ?_ (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) (mul_nonneg q hB))); rw [← nsmul_eq_mul, ←sum_const]; calc
    (∑ i∈ U,X.p.mass i.val.2 (v i)) = ∑ i∈U,∑ j∈I,‖z j‖* X.p.mass i.val.2 (L j i):=by
       refine sum_congr rfl fun i p=>?_ ; unfold BudgetPoint.mass; rw [hp i p,Finset.mul_sum]; exact sum_congr rfl fun j _=>mul_left_comm ..
    _ ≤ _:=by
       rw [Finset.sum_comm]; refine sum_le_sum fun i x=>?_ ; rw [←Finset.mul_sum]; have ht:∑ j∈ U,X.p.mass j.val.2 (L i j) ≤ Γφ:=by
          apply le_trans ?_ (w i r); rw [←sum_filter]; apply sum_le_sum; intro j p; rw [show L i j= G i j from if_pos ((mem_filter.mp p).2.symm.trans (mem_filter.mp x).2.symm)]
       exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans (mul_le_mul_of_nonneg_right (u i) hB)

variable {b HH Lν:ℝ}(C:J→J→ℂ)(tK:ℕ)
variable(hX:1 ≤ h)(wu:8≤ X.p.B)(pc:Force_M X.p.B (Cube.node ∘ σ) tK)
include Fκ pc hX wu
lemma full_S (hk:1≤Lν)(wχ:Roots.Nice_B X.p.B tK Lν (1/8))(z:Key J)(Y':J→ArcΦ)(hz:∀ i,‖z i‖≤ HH)(p:0≤ HH)(g:0≤b)(u:∀ i,‖toV_C (Cube.node ∘σ) C z i‖≤ Lν)
    (qT:∀ j:J, Axon R.L.val (σ j) X.p (νTip (FlameX σ K_ C) j) h b (Y' j)):
    IncX primeU (FlameX σ K_ C z) X.p h ((tK:ℝ)*(HH*b)+wish_E X.p.B QΦ) ∧ Dark primeU (FlameK σ F_ C z) X.p h (χCut X.p.B tK Lν Va):=by
 obtain ⟨Φ,Qv⟩:= κFire V σ K_ F_ Xo Yo Zo Xi Q qE qΨ s Fκ tK Lν hk wu pc.1 pc.2 wχ (zero_lt_one.trans_le hX) (toV_C (Cube.node ∘σ) C z) u
 rw [melt_H V σ K_ F_ Xo Yo Zo Xi Q qE qΨ s Fκ C z]; exact ⟨Larch.add_v _ _ _ (boltLift (X:=X) (R:=R) σ Y' (fun i=>νTip (FlameX σ K_ C) i) b HH tK qT z hz p pc hX g) Φ,Qv⟩
#print axioms boltLift
#print axioms full_S
end YM.CF.Py
end
