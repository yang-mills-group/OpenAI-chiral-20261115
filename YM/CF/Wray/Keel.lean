import YM.CF.Wray.Waltz
import YM.CF.Wray.Pose
import YM.CF.Pig.Foil
import YM.CF.Iva.Plink
import YM.CF.Wray.Shop
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
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
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Iva Eire Font
local notation "Z_"=> Domain N B
local notation "c'"=> Single N
local notation "Φ"=> Branch.ledgerV
-- COLOR set occupancy(real). No unproven host exceptions
local notation "P"=> Raid (LeanV (Single N))
namespace SupportP
variable {M_ N_:ℝ→ℝ}(a b c H:ℝ)
lemma beam_t(p:Litt R k M_)(v:Litt R l N_):Litt R (k+l) (fun x=>M_ x*N_ x):=by unfold Litt; simp_rw [pow_add, mul_div_mul_comm]; exact BoreP.grip p v
lemma beam_h(p:BoreP M_): Litt R 0 M_:=by unfold Litt; simp_rw [pow_zero,div_one]; exact p
lemma beam_v (p:BoreP M_)(v:Litt R l N_): Litt R l (fun x=>M_ x*N_ x):=Nat.zero_add l ▸ beam_t (beam_h p) v
lemma storm(L:ℕ)(p:Litt R k M_)(v:Litt R k N_): Litt R k (fun x=>Bx L x (M_ x) (N_ x) H):=by
 let u(V:ℝ→ℝ)(p:Litt R k V): Litt R k (fun x=>Kplan L (V x)):= Litt.scale_v (p.scale_l _) _
 unfold Bx; exact (((u _ p).scale_l _).add_e (((beam_v (boring.self 2) (u _ v)).scale_l _).scale_l _))
lemma leanP(p:Litt R 1 M_):BoreP (fun x=> Real.exp (M_ x)):=by
 let v:=p.height_r.spine; apply (BoreP.still (Real.exp 1)).tune; filter_upwards [v.eventually (ge_mem_nhds zero_lt_one)] with x h; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; exact Real.exp_monotone h
variable {T₁:ℝ→ Wages}(p: TideR R T₁)
local notation "W"=> T₁
include p
lemma circle_p : Litt R 1 (fun x=> PnT k x (T₁ x) H) ∧ Litt R 2 (fun x=> VoltP k x (T₁ x) H):=by
 have he:=storm H k p.hunt p.vigor; let p':=leanP he; have ht:Litt R 2 (fun x=>PowerP k x (T₁ x) H):=by unfold PowerP; simp_rw [pow_two]; exact beam_v p' (beam_t he he)
 exact ⟨beam_v p' he, ((ht.add_e ht).add_e (storm H k p.mama p.visa))⟩
lemma cupS:Litt R 2 (fun x=>ST k*VoltP k x (W x) H) ∧ Litt R 2 (fun x=> cuP (T₁ x).ego k (PnT k x (T₁ x) H) (VoltP k x (T₁ x) H)):=by
 obtain ⟨v,w⟩:= circle_p (k:=k) H p; let U:= v.scale_l (ST k); let P':= w.scale_l (ST k); let Y(x):=(2:ℝ)*(T₁ x).ego
 have ht:= beam_v ((BoreP.still (k+1:ℝ)).grip (BoreP.inert (p.ego.scale 2))) P'
 exact ⟨P', ((((ht.add_e ht).add_e (beam_t U U)).add_e (beam_t U U)))⟩
end SupportP
end YM.CF.Wray
