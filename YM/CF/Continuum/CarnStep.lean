import YM.CF.Continuum.CarnSpin
import YM.CF.Fallow.Tope
import YM.CF.Tar.Joust
import YM.CF.Fallow.Sway
import YM.CF.Tar.Roan
import YM.CF.Chaff.Advent
import YM.CF.Chaff.Diet
import YM.CF.Paxos.Amber
import YM.CF.Tar.Rein
import YM.CF.Tar.Silt
import YM.CF.Paxos.Seed
set_option autoImplicit false

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
open Oath Feu Feu.Corset Beau Haro Ione Salt
set_option maxHeartbeats 1000000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(nK B1:ℕ)(k₀:ℕ)
local notation "NK"=> trunkY nK B1
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht (trunkY nK B1) B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht (trunkY nK B1) B0
local notation "μh"=> hat R.L x
variable (φ:ℝ→ℝ)(T_:ArmorK)(Λp:Stock_V){Zζ Wκ VΦ KΦ:ℝ→ℝ}
variable (R0 E C δ:ℝ→ℝ){wα:ℝ}(y:ℝ)(D':Loom_K V a p i N0 k₀ J q h T_ φ Zζ Wκ VΦ KΦ wα R0 E C δ y)(hy:y ≤ x)
variable (V0 Jx:ℕ→ℝ)(Fp:ℝ→ℝ)(Hμ:SnapPS V a p i N0 M k₀ J q h φ T_ Λp δ R0 E C y D' hy Fp nK B1 Jx V0)
local notation "S'"=> StarPS NK
open Oise
variable (W0:Cape M B R.L)(Wp:∀ j:ℕ,RocketV V (mesh M R.L j) (mesh M R.L (j+1)) U W J (W0 j) (apt M B R.L j) q)
local notation "HR"=> (fun i=>(Hμ.rateB i).le)
local notation "Vq"=> θ_guess (l0:=trunkY nK B1) Jx (fun i=>(Hμ.rateB i).le)
local notation "Ωs"=> fun j:ℕ=> wage_B nK B1 j R.L x
variable (Ue: RegBudget (cell M B R.L (trunkY nK B1)))(sE:ℂ) (pS:∀ b:ℝ,Provides R.L K.j (color_b (hueR V a p i N0 T M ht (trunkY nK B1) B0 (trunkY nK B1)) b Ue 0 0 sE) h (V0 (trunkY nK B1)) (zone_F (trunkY nK B1) (post_H nK)))
open Chaff Gloss Maize Tye RP RP.Str
variable {dG:ℝ→ℝ}{X':Vestal M B R.L}{Wc:ℕ→ℝ}{Gq:ℕ→Haro.SpaceM}(Hx:Pull_K V a p i N0 T M ht nK B1 B0 J q h δ V0 Jx W0 Ue sE X' Gq Wc)(ηP:∀ i',Rue.IsleB SU.group (T.a i').threshold)

open Brace
local notation "Sz"=> fun i=> hat R.L x i
variable (F0:(m:Side)→Scroll m B (Brace.northZ m B))(s':ℝ)(vκ: Lives_B (H:=h) V (F0 (mesh M R.L (trunkY nK B1))) Ue (radiusB (hat R.L x (trunkY nK B1))) (Fp (hat R.L x (trunkY nK B1))) (T.a (trunkY nK B1)) (W0 (trunkY nK B1)) U s')(t':B=R.L^B1)(hp:1≤h)(htZ:∀ j,(T.a j).threshold ≤ J.k)
include htZ D Wp ηP vκ t' Hμ hp
lemma ride_ad (ψ:ℕ→ℝ)(px:DutyBill V a p i N0 M nK B1 J q h φ T_ Λp δ (x:=x) V0 Jx ψ)(u_:∀ j, Θpane V a p i N0 M k₀ J q h φ T_ R0 E C δ y D' hy j≤ ψ j)(hn:61 ≤ M.val) : ∃ X Gq Wc,Canter_E V a p i N0 T M ht nK B1 k₀ B0 J q h φ T_ Λp R0 E C δ y D' hy V0 Jx Fp W0 F0 s' Ue X Gq Wc ∧ ∀ j<buoy nK,‖Complex.exp (X (j+1)).v‖*ψ j ≤ ‖Complex.exp (X j).v‖:=by
 have he:zone_F NK (post_H nK)=some B1:=by unfold zone_F trunkY; rw [if_pos (by omega),Nat.add_sub_cancel_left]
 let L:=NK
 have hP(b): Provides R.L K.j (color_b (Fh L) b Ue 0 0 (s':ℂ)) h (V0 L) (zone_F L (post_H nK)):=by
    have hA:= vκ.weight; unfold L; rw [he];  -- goal
    have hc : IncX (Chaff.LabelB (mesh M R.L NK) B) Ue (T.a NK) h (V0 NK):= Provides.liftE h (Fh NK) _ _ hA Hμ.cost
    refine ⟨⟨hc.weight,fun s v=>hc.face s (by subst B; exact ply_J _ _ s v)⟩,rfl,?_⟩
    have ht':0≤ Fp (hat R.L x NK):=by
       obtain ⟨A,u,w⟩:= hA.weight; refine (sum_nonneg fun j _=>?_).trans (w 0); split; exact mul_nonneg (Real.exp_pos _).le ((Taxi.eraF _ _ (u j) (zero_le_one.trans hp) 1 (ping_f (T.a NK) _)).grade); exact le_rfl
    exact Provides.liftQ h (Fh L) _ _ (Vale.lye (ply_U R.L B1) _ _).2 (ht'.trans Hμ.cost)
 obtain ⟨X,Gq,Wc,Hx,Uκ,u⟩:= root_duty V a p i N0 T M ht nK B1 k₀ B0 D J q h φ T_ Λp R0 E C δ y D' hy V0 Jx Fp Hμ W0 Wp Ue (s':ℂ) hP hp hn ψ px
 have he(j:ℕ)(hj:j<buoy nK):‖Complex.exp (X (j+1)).v‖*ψ j ≤ ‖Complex.exp (X j).v‖:=by
    have ht':j < NK:= hj.trans_le (by unfold trunkY post_H; omega)
    have hU:= u _ ht'; rwa [tide_W,if_pos hj] at hU
 refine ⟨X,Gq,Wc,⟨Hx,Hμ,D,Wp,vκ,ηP, htZ,Uκ,fun j p=>(mul_le_mul_of_nonneg_left (u_ j) (norm_nonneg _)).trans (he j p),?_⟩,he⟩
 intro j tK; have hu(k d:ℕ)(s:d≤k)(t:k ≤ NK): partitionZ (X d) U (W0 d) = partitionZ (X k) U (W0 k):=by
    induction k with|zero=>rw [show d=0 by omega]|succ k ih=> rcases s.eq_or_lt with r|r; rw [r]; exact (ih (by omega) (by omega)).trans (purse V a p i N0 T M ht nK B1 B0 D J q h δ V0 Jx W0 Wp Ue _ Hx ηP k t)
 exact hu NK j tK le_rfl
end YM.CF.Py
