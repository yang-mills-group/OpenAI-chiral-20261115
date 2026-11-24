import YM.CF.DPress.Dens.Kelp
import YM.CF.BPress.Test
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Thrift RoomF
variable {F: RoomF J Λ M Δ}(D:Crib F n)
namespace Crib
open Silo
local notation "jS" j:max=> Dh V M B (n-1-j) j
local notation "jA" j:max=> cell M B R.L j
local notation "jO" j:max=> Λ.O (hat R.L x j)
local notation "jC" j:max=> Tew.tiny R (hat R.L x j)
local notation "Xt" j:max=> venue D j
open Cap Graph Window Mint Period
namespace Quant
local notation "Hx"=> hat R.L x
variable (Z: Lore M B R A.μ)
open BPress
local notation "Vm"=> cell M B R.L i
local notation "U_A"=> Λ.w (hat R.L x i)
-- universal volume not depth. $s^4 exponent stays uniform while M grows. hat x. transfer application at fixed t even if capital certificate newly granted. True use Φ_Ω. Values assigned Session. frameK.
abbrev ιH (W:GivenX V U):= cashU W.C
-- footprint expressed sΠ=More.V. door per L. $X`
abbrev TaxKe (x t:ℝ)(T:Teller SU.group)(Y:ℝ):= (2*x)*(T.top.paths*t^3+T.top.paths*t^4)+Y*t^2
abbrev CostE (W:GivenX V U)(v:ℝ):ℝ:= 2^2 * cashU W.C / (2^4) + (3*v) + ((180:ℝ)*45*((2+2^2)*cashU W.C))/(2^4)
abbrev CHeight (i:ℕ)(v:ℝ):= TaxKe (hat R.L x i) (Δ.a i).threshold K V.W.bar + CostE W v
include D in
lemma height (v:ℝ): meterY (Δ:=Δ) (i:=i) (M:=M) v= Real.exp (CHeight (Δ:=Δ) i v * ((More (cell M B R.L i)).val:ℝ)^4):=by
 unfold meterY CHeight Tc0 Cm flagBill pittance doorF CostE Graph.lark taxY TaxKe; ring_nf; -- N_H cast.
 have he:∀ k:Side, ((More k).val:ℝ)=(k.val:ℝ)*2:= by intro k; exact_mod_cast (show (More k).val=_ from rfl)
 simp_rw [he]; ring_nf -- tune
variable {Y:StarPS n}{Yc:VestM M B R}
lemma envelope(L0: LogH (cell M B R.L i))(v:ℝ) {b:ℝ}(w:AccountY (Δ.a i) C.h L0.fuel b): RG.Envelope (denZ (render D i L0 v) U (F.Y i)):= Girt.sailW _ (ward_m (ℓp D L0 v) (⟨w.E,rfl,w.K⟩:LotR (render D i L0 v) C.h b b)) W.pearl V.note W.health P_.tk J.n _ (baseR J F i) (J.gran.trans (F.rocket i).size)
include D
variable (p: LedgerL D Z Y Yc)(t: i≤ n)
include p t
lemma low : AccountY (Δ.a i) C.h ((Yc i).fuel) (Tew.tiny R (hat R.L x i)):= ((D.rank_none ..).2 (p.paid _ t)).1.toAccountY
lemma true_trace(z:Orbit (cell M B R.L i)): ‖recX U (vint D Y Yc i) (F.Y i) z‖ ≤ Real.exp (CHeight (Δ:=Δ) i (jC i)*((More (cell M B R.L i)).val:ℝ)^4):= le_trans (Quant.true_ D _ (variant D Y t) (Quant.low D Z p t) z) (height D _).le
lemma Envelope : RG.Envelope (denZ (vint D Y Yc i) U (F.Y i)):= envelope D (Yc i) _ (Quant.low D Z p t)
omit p t D
abbrev CostT (M:Side)(i:ℕ) := Classical.choose (Studio.banker (Δ.a i) (cell M B R.L i) (Λ.w (hat R.L x i)))
noncomputable def CostP(M:Side)(i:ℕ):= Real.exp (Tc0 (Δ:=Δ) (M:=M) i) * ώr (W:=W) (M:=M) (i:=i) * CostT (Λ:=Λ) (Δ:=Δ) M i -- explicit
lemma ksig:0≤CostP (Λ:=Λ) (Δ:=Δ) M i:= mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Classical.choose_spec (Studio.banker (Δ.a i) (cell M B R.L i) (U_A))).1
include F in
lemma enough : Tew.tiny R (hat R.L x i) ≤ Λ.w (hat R.L x i):= by rw [Λ.getW]; exact (F.epoch i).tax.Dust0.coins
include D p t
set_option maxRecDepth 4096 in
lemma densityD {v:LogH (cell M B R.L i)}(b:Born (k:=k) (i:=i) D v Yc)(x0:Orbit (cell M B R.L i)): ‖recX U (render D i v (D.b_T Y i)) (F.Y i) x0- recX U (vint D Y Yc i) (F.Y i) x0‖ ≤ CostP (Λ:=Λ) (Δ:=Δ) M i * μx Λ x k i:= by
 let g:= variant D Y t; let v':= AccountY.more C.uB (Quant.low D Z p t) (enough (F:=F)); refine (Quant.recB D (Yc i) g (Quant.low D Z p t) x0 v).trans ((mul_le_mul_of_nonneg_left (c:=CostT (Δ:=Δ) (Λ:=Λ) M i* μx Λ x k i) ?_ (show 0 ≤ (Real.exp (Tc0 (Δ:=Δ) (M:=M) i))*ώr (W:=W) (i:=i) (M:=M) from mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).trans_eq ?_) -- Lean [?] implicit.
 · exact (Classical.choose_spec (Studio.banker (Δ.a i) (cell M B R.L i) (U_A))).2 _ _ C.uB v' b.leg.1.toAccountY _ b.money _ _ (ιv D x0)
 unfold CostP; ring
end Quant
end Crib
end FitD
end YM.CF.Py.Kay
