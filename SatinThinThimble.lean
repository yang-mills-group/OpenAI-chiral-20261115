import SatinThinBeacon

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
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


/- Single step: put the letters on the same line again. -/
variable {J I: Type} [Fintype J][Fintype I][LinearOrder J][LinearOrder I]
variable {N P B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{d u q qh s t T h Vp Va M Yp BQ Rt Zt κp W VZ VX VY A H x:ℝ}
local notation "Ω"=>mid N B
local notation "Ξ"=>mid P B
attribute [-instance] instDecidableEqLex
lemma read_up (s:ℝ): readFee s 0=s∧readFee s 1=0:=by simp [readFee]

variable (X:GramM (mid N B))(σ:I→Site (mid N B))
local notation "σ'"=>treeO σ
local notation "Ψc"=>Cube.node ∘ treeO σ
local notation "Jk"=>Article I
local notation "Hσ"=>Key Jk
variable {o:TopicScheme (mid P B) (mid N B)}
variable (V:Grace K R L)
variable {U:Grasp V.U B d} {G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} {Y:GramM (mid P B)}{Xp:Op SU.Slot}{q':Chi}
variable (p:Fin 2→Topic (mid P B))
def GroupPay (o:TopicScheme P N)(p:Fin 2→Topic P) (a q:ℝ) (i:Fin 2):ℝ:= rated o (p i) (readFee q i) (a*q)
def groupTopic (o:TopicScheme P N)(p:Fin 2→Topic P) (a q:ℝ) (i:Fin 2):Topic N:= surname o (p i) (readFee q i) (a*q)
local notation "rank'''"=> GroupPay o p A q
local notation "tag''"=> groupTopic o p A q
local notation "fΨ"=> fun i:Article I=> readFee q (layer i)
local notation "fΦ"=> fun i:Article I=> readFee s (layer i)
def warpLine (o:TopicScheme P N)(p:Fin 2→Topic P)(L:Side)(a q s:ℝ):Funds L := get_F L s (GroupPay o p a q 0) (GroupPay o p a q 1)
/-! Keep principal topic independent!! `join` with (zero • gapTopic) isn't safe for this. -/
local notation "D"=>warpLine o p R.L A q s
def hatchTopic (L:Side)(o:TopicScheme P N)(p:Fin 2→Topic P)(a q s:ℝ)(i:Fin 2):Topic N:=
 let Dμ:= warpLine o p L a q s; let A:=groupTopic o p a q 0; if i=0 then A.scale Dμ.ticket else (A.scale (moveCost L Dμ 0 1)).join ((groupTopic o p a q 1).scale (zoomM L))
lemma hatch_principal {L0:Side}{o:TopicScheme P N}{p v:Fin 2→Topic P}(q:p 0=v 0) (a b c:ℝ) : hatchTopic L0 o p a b c 0 = hatchTopic L0 o v a b c 0 ∧ (warpLine o p L0 a b c).ticket=(warpLine o v L0 a b c).ticket := by
 simp only [hatchTopic,warpLine,get_F,GroupPay,groupTopic,q,ite_true,true_and]
variable (Xo:Key (Article I)→RegBudget (mid P B))(Zo:Key (Article I)→ForceBudget (mid P B))
local notation "A'"=>fun _:Article I=> A*q
local notation "p_F"=> PointSk ∘ fun i:Article I=> readFee q (layer i)
variable {E:Key (Article I)→ RegBudget (mid N B)}{Yf:Key (Article I)→ForceBudget (mid N B)}
variable (Fz: Cause_P V U G S G₀ G₁ X Y Xo 0 Zo Xp q' u h Vp Va (treeO σ) (fun _=> A*q) (PointSk ∘ fun i:Article I=> readFee q (layer i)) E Yf (fun i=>PointSk (GroupPay o p A q (layer i))) 0 M W Yp BQ Rt Zt κp)
-- Q ingredients after Lens onboarding
structure Thimble (W BQ A q s M Va Z:ℝ)(L:Side)(P:BudgetPoint):Prop where
 q_pos:0<q
 span:q ≤ s
 fair:s ≤2*q
 s1:s≤1
 bought:ChoiceCost W BQ A L
 sky:|M|≤ ((L.val:ℝ)⁻¹)^5*q
 xb:8≤P.B
 niceA: Nice_B P.B 2 (compassκ L) (1/8)
 niceE: Nice_B P.B 2 (compassκ L*s⁻¹) (1/8)
 ebb: wish_E P.B Z ≤ s
 cut:χCut P.B 2 (compassκ L) Va ≤ s
 emin: Va ≤ s/(compassκ L)
 belt: ((L.val+1)*(4*P.B+2)+2*P.B)≤ P.B+cape_B P.B
local notation "φq"=> Tune.qCorset X.p.threshold Y.p.threshold (R.L.val:ℝ)
variable (g:Thimble W BQ A q s M Va κp R.L X.p)(hΩ:Very_Ψ σ X.p.B)
variable (vQ: Tune.qCorset X.p.threshold Y.p.threshold (R.L.val:ℝ) ≤ 4*((R.L.val:ℝ)⁻¹)^4) (vk: ((R.L.val:ℝ)⁻¹)^4/4 ≤ Tune.qCorset X.p.threshold Y.p.threshold (R.L.val:ℝ))
variable (u0:1 ≤ h)(hω:∀ x:Site (mid P B), nun_ω Y.F x=(t:ℂ))(ht0:Real.exp (-1) ≤ |t|)(ht:|t|≤ Real.exp 1)
variable (T_:∀ i:Article I,(groupTopic o p A q (layer i)).face (treeO σ i) (νTip E i) (emberTip Yf i))
local notation "Aq"=> Topic
local notation "Xκ"=> FlameX σ' E (TicketM R.L D)
local notation "Wκ"=> FlameK σ' Yf (TicketM R.L D)
local notation "Λκ"=> moveCost R.L D
local notation "Wax"=> hatchTopic R.L o p A q s
local notation "Λc"=> TicketM R.L D
include Fz g hΩ -- argument order? from section include
lemma flame_tip (i:I)(j:Fin 2) : νTip Xκ (phaseMark i j)= Λκ 0 j • νTip E (phaseMark i 0)+ Λκ 1 j • νTip E (phaseMark i 1) ∧ emberTip Wκ (phaseMark i j)= Λκ 0 j • emberTip Yf (phaseMark i 0)+ Λκ 1 j • emberTip Yf (phaseMark i 1):=by
 have hp:=part_Φ V σ' E Yf Xo 0 Zo Xp _ _ _ _ Fz Λc; have he:=partK σ' V Xo 0 Zo A' p_F E Yf _ _ Fz Λc
 rw [hp,he,doubler σ hΩ.1,doubler σ hΩ.1]; unfold TicketM; simp only [Complex.coe_smul]; exact ⟨rfl,rfl⟩
omit g hΩ
include hω vQ vk ht0 ht g
lemma flame_both (i:I) (j: Fin 2):
 Axon R.L.val (σ i) X.p (νTip E (phaseMark i j)) h (4*|W| *((R.L.val:ℝ)⁻¹)^4*q) (PointSk (rank''' j)) ∧ αPrice R.L h (A*q) M BQ Rt Zt (PointSk (readFee q j)) (PointSk (rank''' j)) X.p Y.p (t:ℂ):=by
 have hv:= Fz.pulse (phaseMark i j); dsimp only at hv; rw [hω] at hv
 have hd: |readFee q j| ≤ q:=by unfold readFee; have hz:=g.q_pos; split <;>simp [abs_of_pos hz,hz.le]
 exact ⟨turf_A _ _ _ _ _ _ _ (mint_cost g.bought g.q_pos ht g.sky hd) hv.1,hv.2.2⟩
lemma funds_active (i:I) : (D).ticket*(rank''' 0)=s ∧ (D).adjustment*(rank''' 0)+rank''' 1=0:=by
 let h0:=g.q_pos.trans_le g.span; let v:= GroupPay o p A q; have hψ:= flame_both X σ V p Xo Zo Fz g vQ vk hω ht0 ht i 0; have hx:= flame_both X σ V p Xo Zo Fz g vQ vk hω ht0 ht i 1
 have hc:=fixed_cost g.bought g.q_pos ht0 ht g.sky (by exact (read_up q).1 ▸ hψ.2) _ s rfl vQ vk g.span g.fair -- expected type metavars
 have hu:=gap_cost g.bought g.q_pos ht g.sky (v 1) s ((read_up q).2 ▸ hx.2) g.span hc
 exact ⟨fund_a _ _ _ _ h0 hc,fund_b _ _ _ _ h0 hc hu⟩
include hΩ T_ u0
lemma spark_emit (i:Article I): Axon R.L.val (treeO σ i) X.p (νTip Xκ i) h ((A/8)*s) (PointSk (readFee s (layer i))) ∧ (Wax (layer i)).face (treeO σ i) (νTip Xκ i) (emberTip Wκ i):=by
 have hz:= g.q_pos; let h0:=zero_le_one.trans u0; let L:=R.L; let t:= D; let u(j:Fin 2):=rank''' j; let v:=tag''; let hw:=Λκ; let hC:=move_zeroes L t
 rw [recover_art i]; generalize layer i=j; generalize host i=i; have ⟨y,wk⟩:=funds_active X σ V p Xo Zo Fz g vQ vk hω ht0 ht i; let x(j:Fin 2):=phaseMark i j
 let XE(j:Fin 2):=νTip E (x j); let XF(j:Fin 2):=emberTip Yf (x j); let G(j:Fin 2):= hw 0 j • XE 0+ hw 1 j • XE 1; let H(j:Fin 2):=hw 0 j • XF 0 + hw 1 j • XF 1
 have hh(t:Fin 2):=flame_tip X σ V p Xo Zo Fz g hΩ i t; rw [(hh j).1,(hh j).2]; change Axon L.val (σ i) X.p (G j) h _ (PointSk (readFee s j)) ∧ (Wax j).face (σ i) (G j) (H j)
 let f:=4*|W| *((L.val:ℝ)⁻¹)^4*q; let hζ(k:Fin 2)(a:ℝ):Axon L.val (σ i) X.p (a • XE k) h (|a| * f) (PointSk (a*u k)):= by rw [←point_Z]; exact real_E _ _ (flame_both X σ V p Xo Zo Fz g vQ vk hω ht0 ht i k).1 h0
 have ht(k:Fin 2):(v k).face (σ i) (XE k) (XF k):= T_ (x k)
 constructor
 · have hK:=Axon_add (σ i) X.p L.val (hζ 0 (hw 0 j)) (hζ 1 (hw 1 j)) h0; rw [point_Zadd] at hK
   have hm: hw 0 j * u 0+ hw 1 j *u 1=readFee s j:=by
      obtain ⟨η,η1,η2,η3⟩:=hC; fin_cases j
      · change moveCost L t 0 0*u 0 + moveCost L t 1 0*u 1=readFee s 0; rw [η,η1,(read_up s).1,zero_mul,add_zero]; exact y
      change moveCost L t 0 1*u 0+ moveCost L t 1 1*u 1=readFee s 1; rw [η2,η3,(read_up s).2]; rw [mul_assoc,←mul_add,show t.adjustment * u 0 + u 1=0 from wk,mul_zero]
   apply turf_A _ _ _ _ _ _ _ _ (hm ▸ hK); let z:= zoomM L*f
   have he(i:Fin 2): |hw i j| * f ≤ z:=by
      have hp:0 ≤ f:=by unfold f; positivity
      exact mul_le_mul_of_nonneg_right (cost_bound L t i j) hp
   refine (add_le_add (he 0) (he 1)).trans ?_; have hx:z=2048*|W| *q:= by unfold z zoomM f; field_simp; ring; -- tune ring
   have hA:0 ≤ A/8:=by have hf:=g.bought.root; linarith; -- tune
   rw [hx]; refine le_trans ?_ (mul_le_mul_of_nonneg_left g.span hA); linarith only [mul_le_mul_of_nonneg_right g.bought.arch hz.le,mul_nonneg (abs_nonneg W) hz.le] -- domination
 obtain ⟨η,η1,η2,η3⟩:=hC; fin_cases j
 · have hv: G 0=t.ticket • XE 0:=by change moveCost L t 0 0 • _ + moveCost L t 1 0 • _=_; rw [η1,η,zero_smul,add_zero]
   have hg: H 0=t.ticket • XF 0:=by change moveCost L t 0 0 • _ + moveCost L t 1 0 • _=_; rw [η1,η,zero_smul,add_zero]
   change (Wax 0).face _ (G 0) (H 0); rw [hv,hg,hatchTopic]; rw [if_pos rfl]; exact topic_scale t.ticket (ht 0)
 let y':= topic_join (topic_scale (hw 0 1) (ht 0)) (topic_scale (moveCost L t 1 1) (ht 1)); change (Wax 1).face (σ i) (moveCost L t 0 1 • _+moveCost L t 1 1 • _) (moveCost L t 0 1 • _ + moveCost L t 1 1 • _); rw [η2,hatchTopic]; rw [if_neg (by decide)]; -- keep substitutions
 exact Eq.mp (by rw [η2]) y'
end YM.CF.QuadClock
