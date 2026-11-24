import YM.CF.Vp929.Rails.Field
import YM.CF.Vp929.Rails.Flame
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
namespace Pitching
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "y"=> Scales.y SU.group R.L x
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Bs" v:max F:max => base (q:=q) (J:=J) (w:=w) p' v F
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "Xs" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
local notation "F₁"=> Folk S' z' (Words S')
local notation "V_"=> Troupe S' z' (Words S')
local notation "Xo" => Hos S' z'
local notation "Θ"=> vast (k:=D.Z.N1*radiusB x) o.muster
open Lich Iva
variable {F:Corr (Scree.mid n B)}
variable {Pν: ↥(Sil (w.step V) (coming D.Z 105 5*radiusB x))}{N0:ℕ}
local notation "Δ"=> (o.muster.post+90)*radiusB x
local notation "Ξ"=> (o.muster.loft+o.muster.post+200)*radiusB x
local notation "D'"=> Dwell ι
local notation "Xp"=> (stake (n:=LeanV (Tulip.Single (Scree.mid m B))) h)
local notation "FX"=> F₁→Raid (Dwell (Scree.mid m B))
variable (Aq:Dialect o p' f F Pν) {baseV:ℝ}
local notation "Ξ'"=> Fintype.card
local notation "Lo"=> Palot.leaf (Site (Domain m B))
abbrev realDisc (K0:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))) (b:ℝ):= b^(K0.toRight.toRight.toLeft).card
local notation "Dα"=> radiusB x
namespace Dialect
local notation "KZ"=> F₁
abbrev extra (δ:ℝ) (i:Folk (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))) := Trees.currency (radiusB x) δ (Aq.req i).val
variable {I:Type}[Fintype I] {Lq:I→ℝ} (S:(i:I)→Vote o (Lq i) c) (b:ℝ)
abbrev deck (Aq:Dialect o p' f F Pν)(Bv δ:ℝ)(S:(i:I)→Vote o (Lq i) c)(b:ℝ) : KZ→Raid D':=fun i=> Aq.extra δ i • Bv •∑ j:I,(S j).body b i
variable (Bv δ :ℝ)
lemma priced : Aq.rail (Aq.deck Bv δ S b) = tallR Aq.req (fun i:I=>Aq.rail ((S i).body b)) (radiusB x) Bv δ:= by
 unfold deck tallR rail railsB; rw [scale_dawn,scale_dawn,sum_dawn]; funext i; dsimp only; rw [Finset.sum_apply]
variable (K0:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V)))
local notation "ℓ"=> Aq.list K0

abbrev rev (b:ℝ)(K0:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))) := b^(steep (Aq.list K0)).card
lemma reversal : payH (Aq.rail (Aq.deck Bv δ S b)) (Aq.list K0)= Aq.rev b K0 • payH (Aq.rail (Aq.deck Bv δ S 1)) (Aq.list K0):= by
 apply Wray.tall_k ℓ _ b _ (Aq.listing _); swap
 · intro i; rw [priced,priced]; unfold tallR; dsimp only; have he(j:I):Aq.rail ((S j).body b) (ignite i)= b • Aq.rail ((S j).body 1) (ignite i):= by
     let Y:= (S j); let Rv(v:ℝ):=Aq.rail (Y.body v)
     have h(t:ℝ): (Rv t) (ignite i) = Pi.single (beamH ((Θ (.inl i))).val) (t*mM P' D.Z D.I D.E x 6) := Wray.frosty_s (H:=o.tinted (Lq j)) (k:=6) (j:=105) P' D.Z D.I D.E o.bags Aq.covers Aq.swap Y.big₀ Y.big₁ Y.small₁ Y.small₀ c.blips Aq.Qx Aq.Qv Aq.value _ (Vote.pad o) t i; change Rv b (ignite i)= b • Rv 1 (ignite i); rw [h,h,one_mul]; funext i; simp only [Pi.single_apply,Pi.smul_apply,smul_eq_mul]; split_ifs; rfl; rw [mul_zero]
   simp_rw [he]; rw [←Finset.smul_sum,smul_comm b,smul_comm b];
 intro i h; rw [priced,priced]; unfold tallR; dsimp only; let e(j:I)(v:ℝ):Aq.rail ((S j).body v) i=Aq.rail ((S j).body 1) i:= (Wray.cold_a (H:=o.tinted (Lq j)) (k:=6) (j:=105) P' D.Z D.I D.E o.bags Aq.covers Aq.swap (S j).big₀ (S j).big₁ (S j).small₁ (S j).small₀ c.blips Aq.Qx Aq.Qv Aq.value _ (Vote.pad o) v 1 (Vote.pad o) i h).2; simp_rw [fun j=>e j b]
-- carry unspent exponential-on-token budget into the invoice (for cut-difference).
abbrev prize (K0:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))) (δ:ℝ):= ((Aq.list K0).map (Aq.extra δ)).prod
lemma load (κ:ℝ) : payH (Aq.rail (Aq.deck Bv (κ+δ) S b)) ℓ= Aq.prize K0 κ • payH (Aq.rail (Aq.deck Bv δ S b)) ℓ:=by
 unfold rail railsB; rw [show Aq.deck Bv (κ+δ) S b = fun i=>Aq.extra κ i • (Aq.deck Bv δ S b) i from ?_,pay_dawn_price];  funext i; unfold deck extra Push.AbsoluteSums.Trees.currency; rw [add_mul,Real.exp_add,mul_smul]
 -- price reduction
variable {Bv δ b} (Z:Cellar N0 o p p' c f ag Cg) (hF:Location.gross p' D f F) (he:∀ i,Lq i∈ Year R x)
include Z hF he
lemma deck_pos (g:0≤Bv)(hv:0≤b):0≤ Aq.deck Bv δ S b:= by
 intro i; exact smul_nonneg (Real.exp_pos _).le (smul_nonneg g (Finset.sum_nonneg fun j _=> (S j).body_pos ((Z.full _ (he _) F hF).fire) hv i))
local notation "bκ"=> Wray.boT R 5 105 c.blips (ag/32) Cg x
local notation "astar_"=> (23/4:ℝ)
local notation "Dslit_"=> (1/8:ℝ)
local notation "DalphaDelta" c:max=> degreePrice (radiusB x) c 1
variable {κ b0:ℝ} (hκ:0<κ) (hq:degreePrice (radiusB x) κ 1 ≤ 1/2) (hm: Footprint.payment 1 (6*(radiusB x+1)) 0 (1/4) 1 (Bv*(Fintype.card I*c.Pc x)) ((23/4)+1) 0 ≤ κ) (uB:0 ≤ Bv)
include hκ hq hm uB
lemma stellar (x':Site (Domain m B)) (j:ℕ) : (∑ i:V_ with Palot.outC j i, invoiceB (radiusB x) astar_ x' (payH (tallR Aq.req (fun i:I=>Aq.rail ((S i).body bκ)) (radiusB x) Bv Dslit_) (Aq.list i))) ≤ κ*(DalphaDelta κ)^j*(1-DalphaDelta κ)⁻¹:= by
 refine uprootP Aq.req awake (fun i:I=>Aq.rail ((S i).body bκ)) (fun i:I=>Aq.amount (S i) bκ) (fun i j=> Aq.solvent (S j) Z hF (he _) i) ?_ (fun x i=> Aq.hit (S i) Z hF (he _) x) uB (by positivity) (by positivity) zero_lt_one Aq.tokens Aq.listing ?_ hm hκ le_rfl (lt_of_le_of_lt hq (by norm_num)) _ _
 · intro i; exact Wray.destiny ..
 norm_num [Footprint.reserve,Py.tollE]
lemma invoice (hc:δ+b0=Dslit_)(hb:0<bκ)(S1:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Lo→Raid D')(pC:0≤ S1)(hC:∀ i y', joinV Xp (S1 i y') ≤ payH (Aq.rail (Aq.deck Bv b0 S 1)) (Aq.list i) (beamH y'.val)): Merit (radiusB x) astar_ Xp (fun i=>Aq.prize i δ * Aq.rev bκ i) (fun j=> κ*(DalphaDelta κ)^j*(1-DalphaDelta κ)⁻¹) S1:= by
 refine ⟨pC,fun o' m=> le_trans ?_ (Aq.stellar S Z hF he hκ hq hm uB o' m)⟩; unfold tallY; refine sum_le_sum fun i _=>?_ ; unfold invoiceB; rw [sum_filter]; apply sum_le_sum; intro j _; split; swap; · exact le_rfl
 apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
 rw [←priced,← hc,Aq.load,Aq.reversal]; rw [Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,←mul_assoc]; exact mul_le_mul_of_nonneg_left (hC _ j) (mul_nonneg (List.prod_nonneg (by intro i h; obtain ⟨u,p,rfl⟩:=List.mem_map.mp h; exact (Real.exp_pos _).le)) (pow_nonneg hb.le _))
omit Z hF he hκ hq hm uB

lemma prize_pos(δ:ℝ): 0 < Aq.prize K0 δ:= List.prod_pos (by intro i h; obtain ⟨u,p,rfl⟩:=List.mem_map.mp h; exact Real.exp_pos _)
lemma steep_k : steep (Aq.list K0)=K0.toRight.toRight.toLeft:=by unfold Wray.steep; rw [Aq.tokens]
end Dialect
end Pitching
end YM.CF.Py.Rate
