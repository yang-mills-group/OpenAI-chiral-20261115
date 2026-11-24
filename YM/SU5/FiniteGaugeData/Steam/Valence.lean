import YM.SU5.FiniteGaugeData.Steam.Basket
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
/- Heights already paid at actual Course such that `Steam.Club` and any inputs in scope. Tool for toll estimates over the genuine physical period/cutoff. -/
namespace Steam
open Window LocalLimit Steve Next.Rank Preparation
abbrev τ(W:GivenX V U) (x:ℝ) (n:Side):= flagBill n (dleaf R.L x) (dleaf R.L x) (cashU W.C)
abbrev υ(F:Clip) (x:ℝ) {c:Side} (Y:Pane c) := ((Steve.misses Y (temp x)).card:ℝ)* frost F x
abbrev τplus(W:GivenX V U) (x:ℝ) {c:Side} (Y:Pane c) := τ W x c + υ K.top.clip x Y
-- this is a POINTWISE bill. Doesn't assume any estimates away from actual LoomS, but can use all from `Flacon`; no cash weighting on second-coordinate argument needed. Different from price with sup. Flacon furnishes at tall s those entropies AND all penalties. So one can try to pay just by bounding CAR data (with receipts at bad plaquettes). Often worth using `Toll` before expanding in scalar marks (centering!). Can always require `Suite` strong; supports maintain.
def Toll (r:ℝ)(W:GivenX V U)(A:GramM (mid m B))(L:Scree.Loom (mid m B))(x:ℝ)(F:Marks.Tagged (mid m B)): Prop:=∀ i:Orbit (mid m B), ‖Marks.read F i (Graph.beam A U L i)‖ ≤ r * Real.exp (τplus W x i.1)
lemma frost_nn (F:Clip)(x:ℝ)(p:0≤x):0≤frost F x:= by unfold frost Window.oneFlag; have h:= F.tail_pos; positivity
variable {X:GivenX V U}{T:GramM (mid m B)}{K':Scree.Loom (mid m B)}{F:Marks.Tagged (mid m B)}{r:ℝ}
variable {y:ℝ}(Q:Flacon X T K' x h oracle)
abbrev focusG (X:GivenX V U):= Period.costPlan V (cashU X.C) oracle
local notation "θ"=> focusG X
local notation "NetA" => unlit T K.top.paths V.W.bar
local notation "δ"=> τ X x (mid m B)
include Q
lemma Toll.rested (p:0≤ r)(q:Toll r X T K' x F):
  ‖Marks.evaluate (Rate.field U T K') F‖ ≤ r * Real.exp (Fare x (mid m B) θ) := by
 let y := field U T K'; let g:= soaked T.beta
 have he:0<g:=(amplifier _ (Q.stamp.budget _ Q.member).2.2.1).2.2.1
 let Z:= Real.exp (δ+NetA)
 let A(i:Orbit (mid m B)):=Real.exp (-basal T g i.1)
 obtain ⟨K0,t⟩:= repays oracle T he -- K shadows K!
 have hb: ∀ i:Orbit (mid m B), ‖Marks.read F i (y i)‖ ≤ (r*Z)*A i:=by
    intro i; let c:=υ K.top.clip x i.1
    let v := Graph.past T i.1; change ‖Marks.read F i (Graph.recX U T K' i)‖ ≤ _; rw [Graph.porch,show v • _= (v:ℂ) • Graph.beam T U K' i from RCLike.real_smul_eq_coe_smul (K:=ℂ) ..,map_smul,norm_smul] -- tactic tune
    rw [Complex.norm_real,Real.norm_of_nonneg (show 0≤v from (Real.exp_pos _).le)]
    apply (mul_le_mul (Q.outside i) (q i) (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).trans_eq; change Real.exp (NetA-c)*A i*(r*Real.exp (δ+c))=_
    rw [show Real.exp (NetA-c)*A i*(r*Real.exp (δ+c)) = r*(Real.exp (NetA-c)*Real.exp (δ+c))*A i by ring,←Real.exp_add]; unfold Z; ring_nf
 refine le_trans ((norm_integral_le_of_norm_le ((K0).const_mul (r*Z)) (Eventually.of_forall hb))) ?_; rw [integral_const_mul]; apply (mul_le_mul_of_nonneg_left t (mul_nonneg p (Real.exp_pos _).le)).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ p
 rw [Real.exp_add, mul_assoc]; exact Q.full_z
abbrev slopeF (X:GivenX V U)(k:ℝ) := |focusG X| + 2*k +1
lemma Toll.upper_ratio (p:0≤r)(q:Toll r X T K' x F)(y:ℝ)(hp:Real.exp (Fare x (mid m B) (-(2*y+1))) ≤ ‖compensated U T K'‖) : ‖Marks.ratio V U T K' F‖ ≤ r * Real.exp (slopeF X y * (sites (mid m B))) := by
 let P:= Complex.exp (-T.v); have hP:P≠0:=Complex.exp_ne_zero _; let v:= Marks.evaluate (field U T K') F; let q' := compensated U T K'
 have he:Marks.ratio V U T K' F = v/q':=by unfold q' v compensated field Marks.ratio; rw [Marks.scale_ket F]; exact (mul_div_mul_left _ _ hP).symm -- orientation
 have hq: 0< ‖q'‖:=(Real.exp_pos _).trans_le hp
 rw [he, norm_div]; refine (div_le_iff₀ hq).mpr (le_trans (q.rested Q p) ((mul_le_mul_of_nonneg_left hp (mul_nonneg p (Real.exp_pos _).le)).trans' ?_)); rw [mul_assoc, ←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ p; apply Real.exp_monotone; unfold Fare slopeF; nlinarith only [mul_le_mul_of_nonneg_right (le_abs_self θ) (zero_le_one.trans (sites_pos (mid m B)))] -- orientation

lemma Toll.supplies (p:∀ i,‖F i‖≤r): Toll r X T K' x F:=by
 have hr:0 ≤ r:= (norm_nonneg _).trans (p (1,Classical.arbitrary _)); intro i; have ht:0≤ frost K.top.clip x:= frost_nn _ x (le_trans (by norm_num) Q.stamp.live)
 apply (Marks.read_within ..).trans; apply mul_le_mul (p _) _ (norm_nonneg _) hr; apply (Q.budget i).trans; apply Real.exp_monotone; refine le_add_of_nonneg_right ?_; exact mul_nonneg (Nat.cast_nonneg _) ht

variable {u:Preparation} {l i s k:ℕ}{H:(s:Side)→Scree.Loom s→ Prop}{Y:Course u H}(Vh:Club Y r s)
local notation "G₁"=> ((Y.voyage i).X (Y.uv k)).gram s
local notation "S₁"=> (Y.voyage i).CapeT s
variable (X:Marks.Tagged (u.Ctor (Y.ir i) s))
-- abs read over authorized UV beyond kick. applies w/o restricting to cone, IF paying this cutoff threshold.
omit Q
include Vh
lemma Club.toll (t:0 ≤ y) (p:(Y.voyage i).kick ≤ k)(u':s ≤ Y.uv k) (b:Toll y u.W (((Y.voyage i).X (Y.uv k)).gram s) ((Y.voyage i).CapeT s) (hat u.R.L u.x s) X):
 ‖Marks.ratio u.V u.U G₁ S₁ X‖ ≤ y * Real.exp (slopeF u.W r * (sites (u.Ctor (Y.ir i) s))) := Toll.upper_ratio (Vh.full _ _ u') t b r (Vh.lower _ _ p u')
end Steam
end YM.CF.Py.Rate
