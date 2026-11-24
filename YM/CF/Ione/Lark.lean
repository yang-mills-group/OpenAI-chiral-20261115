import YM.CF.Ione.Tick
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Vow Salt Reef
open ProjectorNext.Equivariance
variable(P:BudgetPoint)(s:Sweep n)(V:Pane n)(U:tangD n)
local notation "p'"=>((assembly n).embed s.b)
def cape_v (t:Bool): tangD n→L[ℝ]tangD n:=if t then Reef.cloak _ else ContinuousLinearMap.id ℝ _
def door_b : DN→L[ℝ]DN:=(cape_v s.charge).comp (pulledDirection s.s ((assembly n).embed s.b) V).toContinuousLinearMap
local notation "Zd"=> door_b s V
lemma high_c (V:Pane n)(i:DN)(b:Bool): (polarT b ∘ increment V i)=increment (polarT b∘ V) (cape_v b i):=by
 cases b; rfl
 funext j; change Reef.qG (_*_)= SU.group.lieExp (frolic _) * _; rw [cool_a,map_mul]; rfl -- possibly extra
lemma tour_p: flashA s (increment V U)=increment (flashA s V) ((Zd) U):=by rw [revoke,revoke,pull_increment,high_c]; rfl
lemma den_q (b:Bool)(e:Edge (Seat n))(u:DN): ‖(cape_v b u e)‖=‖u e‖:=by cases b; rfl; exact frolic.norm_map _
lemma cod_E (e:Edge (Seat n)): ‖(Zd U) e‖= ‖U (lane s e)‖:=by change ‖cape_v s.charge _ e‖=_; rw [den_q]; exact (ProjectorNext.Equivariance.roll s.s ((assembly n).embed s.b) V e).norm_map _
lemma cape_l (b:Bool)(u v:DN)(e:Edge (Seat n))(p:u e=v e): cape_v b u e=cape_v b v e:=by cases b; exact p; exact congrArg frolic p
lemma price_t(i:Edge (Seat n))(Z:Support (More n)):Disjoint (ends (lane s i)) (halo (5*P.B) Z) ↔ Disjoint (ends i) (halo (5*P.B) (actY s Z)):=by
 have hp:(halo (5*P.B) (actY s Z)).map (boxA s).toEmbedding=halo (5*P.B) Z:=by rw [←paysT]; apply congrArg; ext; simp [actY] -- tune
 rw [laneX,←hp]; exact Finset.disjoint_map _
lemma local_q (t x:tangD n)(i:Edge (Seat n))(p:t (lane s i)=x (lane s i)): Zd t i=Zd x i:=cape_l _ _ _ _ (congrArg (ProjectorNext.Equivariance.roll s.s ((assembly n).embed s.b) V i) p)
lemma cheap_z(Z:Support (More n)): Zd (openG P Z U)=openG P (actY s Z) (Zd U):=by
 funext i; by_cases h:Disjoint (ends (lane s i)) (halo (5*P.B) Z)
 · -- rw unfolded FIRST occurrence, careful
   change Zd (openG P Z U) i=openG P (actY s Z) (Zd U) i; exact (local_q s V _ _ i (if_pos h)).trans (if_pos ((price_t P s i Z).mp h)).symm
 change Zd (openG P Z U) i=openG P (actY s Z) (Zd U) i
 exact (local_q s V _ 0 i (if_neg h)).trans ((show Zd 0 i=0 from by rw [map_zero]; rfl).trans (if_neg (mt (price_t P s i Z).mpr h)).symm) -- Pi zero
lemma parl_v(Z:Support (More n)): flashA s (pressQ P Z V U)=pressQ P (actY s Z) (flashA s V) (Zd U):=by
 unfold pressQ; change flashA s (RG.increment V _) = RG.increment _ _; simp_rw [←padP]; rw [tour_p,cheap_z,map_smul] -- tune
lemma tall_y(e:Edge (Seat n)): separation (lane s e).1 (boxA s e.1)≤1:=by
 let x:= lane s e; have hp: boxA s e.1∈ ends x:=by rw [show ends x= _ from laneX ..]; exact mem_map_of_mem _ (mem_insert_self e.1 _)
 cases mem_insert.mp hp; next p=> rw [p]; exact (separation_self _).trans_le (by decide)
 next p=> rw [mem_singleton.mp p, separation_comm,separation, add_comm _ (step _), add_sub_cancel_right]; exact pdist_step _ -- tune defeq
local notation "Cq"=> ((2:ℝ)^P.power)
lemma worth_Q(e:Edge (Seat n))(o:Seat n):width P (boxA s o) (lane s e)≤ width P o e * Cq:=by
 unfold Lyre.width; let k:=separation e.1 o; have hx:= separation_triangle (lane s e).1 (boxA s e.1) (boxA s o); rw [sitT] at hx
 have hp:(1:ℝ)+(separation (lane s e).1 (boxA s o):ℝ) ≤ (1+k)*2:=by
    have hh: (separation (lane s e).1 (boxA s o):ℝ) ≤ 1+k:=by exact_mod_cast (hx.trans (Nat.add_le_add_right (tall_y s e) k))
    linarith [Nat.cast_nonneg (α:=ℝ) k]
 rw [mul_assoc,←mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp _) P.threshold_pos.le
lemma toll_Q(o:Seat n): ‖(silo P o).comp ((Zd).comp (trunk P ((boxA s) o)))‖ ≤ Cq:=by
 refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun i=> (pi_norm_le_iff_of_nonneg (show 0 ≤ Cq*‖i‖ from by positivity)).mpr fun e=>?_ -- composition directions
 let K:=trunk P (boxA s o); change ‖(width P o e)⁻¹ • (Zd (K i) e)‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (Lyre.width_pos ..)).le,cod_E,inv_mul_le_iff₀ (Lyre.width_pos ..)]
 change ‖width P (boxA s o) (lane s e) • i (lane s e)‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (Lyre.width_pos ..).le] -- tune actual RHS width or reversed
 apply le_trans (mul_le_mul (worth_Q P s _ o) (norm_le_pi_norm ..) (norm_nonneg _) (mul_nonneg (Lyre.width_pos ..).le (by positivity))); apply le_of_eq; ring
lemma port_l{o:Seat n}{A: DN→ℂ}{t:ℝ}(h:Signs P o A t): Signs P (boxA s o) (A∘Zd) (composeCost P.order t Cq):=by
 let L:=(silo P o).comp ((Zd).comp (trunk P (boxA s o)))
 apply skills; rw [show (A ∘ Zd) ∘ trunk P ((boxA s) o)=(A ∘ trunk P o) ∘ L from ?_]; exact ((map_zero L).symm ▸ (skin h):Allows P.order (A ∘ trunk P o) (L 0) t).comp (allows_linear (toll_Q P s V o) (by rw [map_zero,norm_zero]; positivity))
 funext x; exact congrArg A ((trench _).symm)
end YM.CF.Ione
