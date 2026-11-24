import YM.CF.Song.Beat
import YM.CF.Sere.Uinta
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
open Sour Haro Tap Ione Larch Nor Glyph SupportP
variable (P_:BudgetPoint)(F G H:ℝ→ℝ)
local notation "Pz"=> hall_P P_
abbrev united_K (k:ℕ)(f:ℝ→ℝ)(x:ℝ):= k*f x
abbrev u0(P:BudgetPoint):=cap1 P (BondL.øK 1) 1
lemma cap1_g(i d r:ℝ): Glyph.cap1 (hall_P P_ i) (BondL.øK r) d=u0 P_*r*d^2:=by obtain ⟨p,h,e⟩:= let_X P_ i; unfold u0 Glyph.cap1 BondL.øK numV κY; rw [p,h,e]; ring
lemma cap2_g(i d a b r:ℝ): Glyph.cap2 (hall_P P_ i) (b*r) d a= cap2 P_ b 1 a*r*d^2:=by obtain ⟨p,h,e⟩:= let_X P_ i; unfold Glyph.cap2 numV κY; rw [p,h,e]; ring
lemma φc_Q(x r d a b c:ℝ): φcape (Pz x) a (b*r) (c*r) d=(cap2 P_ c 1 a*d^2+cap2 P_ b 1 a)*r:=by unfold φcape; rw [cap2_g,cap2_g]; ring
lemma spg_B:sizeK R.L 0 (fun i=> spanV (Pz i).B):=by
 let V(i:ℝ):=spanV (radiusB i); refine (show sizeK R.L 0 V from ?_).cost_d ?_
 · unfold V spanV; push_cast; exact (((sizeK.Bcash R.L).accrue (sizeK.Bcash R.L)).accrue (sizeK.mild _ _)).powC _
 filter_upwards [hall_l P_] with i p; rw [p]
lemma fee_f (a b c d:ℝ)(hf:sizeK R.L 2 F):sizeK R.L 2 (fun x=> feeΨ (Pz x) a (b* F x) (c*F x) d):=by
 let k(i):=Real.exp (i*Fief.tileN 1)*(∑' j:ℕ, Real.exp (-a/2*j)*(Tenant.quota*((j:ℝ)+1)^4)); let V(x:ℝ):=spanV (Pz x).B*k (wu P_ +2)
 have ht(x:ℝ): P_.order=(Pz x).order:= (let_X P_ x).1.symm
 refine (((spg_B (R:=R) P_).tint (sizeK.mild _ (k (wu P_ +2)))).scale ((P_.order+1:ℝ)*d^2) |>.tint ((hf.scale (5*b)).accrue (hf.scale c)) |>.cost_d ?_)
 filter_upwards with x; unfold feeΨ aimV wu; rw [(let_X P_ x).1,(let_X P_ x).2.2]; apply Eq.le; congr 1; unfold k spanV; ring
lemma pole_Q(hG:sizeK R.L 1 G)(hH:sizeK R.L 2 H):sizeK R.L 3 (fun x=> rentΦ (Pz x) (G x) (H x)):=by
 exact ((((spg_B P_).tint hH).tint hG).accrue ((((spg_B P_).tint (sizeK.mild R.L wΨ⁻¹)).tint hG).tint hH))
abbrev zeST (Θ:BudgetPoint)(H:ℝ→ℝ)(x:ℝ):=degreePrice (hall_P Θ x).B (H x) wΨ
lemma fee_Q (hf:sizeK R.L 1 F) : let V:=zeST P_ F; sizeK R.L 1 V:=by refine (apollo_d wΨ hf).cost_d ?_; filter_upwards [hall_l P_] with i p; unfold zeST; rw [p]
lemma σΩ (hG:sizeK R.L 1 G)(hH:sizeK R.L 3 H): sizeK R.L 3 (fun x=> tintK (Pz x) (H x) (G x) (rainX R 1 x)):=by
 let Z:= zeST P_ G; have hp:sizeK R.L 1 Z:= fee_Q P_ G hG; let K(x):=(1-Z x)⁻¹
 have hz:sizeK R.L 0 K:=by
    have hx:Tendsto K atTop (𝓝 1):=by simpa using ((tendsto_const_nhds (x:=(1:ℝ))).sub hp.spine |>.inv₀ (show (1:ℝ)-0≠0 by simp)); -- tune
    exact (sizeK.mild R.L 2).cost_d (hx.abs.eventually (ge_mem_nhds (by norm_num : |(1:ℝ)| < |(2:ℝ)|)))
 have hm(m:ℕ):sizeK R.L (1+m) (fun x=> G x*Z x^m*K x):=by exact (hG.tint (by simpa using hp.square m)).tint hz -- tune
 have he:sizeK R.L 3 (fun x=>uk_b (H x) (rainX R 1 x) (G x) (Z x)):= (hH.accrue (((rain_l R 1).scale 2).tint (hm 1))).accrue ((hm 2).scale _)
 have hu:sizeK R.L 0 (fun x=> reserveT (Pz x).power (Pz x).order (Pz x).B 1):= by
    apply ((Nor.vale_u P_.power P_.order 1).creditK R.L).cost_d; filter_upwards [hall_l P_] with i k; rw [k,(let_X P_ i).1,(let_X P_ i).2.1] -- tune
 exact hu.tint he
local notation "uΦ"=> (tendsto_const_nhds)
variable {v D:ℝ}
local notation "ζV"=> rainX R 1
local notation "yK"=> Scales.y SU.group R.L
lemma pill_R (hk:0 <d)(h:sizeK R.L (k+1) F):∀ᶠ i in atTop,F i < d*(Scales.g SU.group R.L i)^k :=by -- extra instance remove
 have hv:= ((rockP k (iFX h))).spine; filter_upwards [hv.eventually (Iio_mem_nhds hk), (year SU.group R.L).eventually_gt_atTop 0] with i t y; have he:=Scales.gauge _ _ y; apply lt_of_le_of_lt (le_abs_self _); change ( ((Scales.g SU.group R.L i)^k)⁻¹ * _) < _ at t; rw [inv_mul_lt_iff₀ (by positivity)] at t; simpa only [mul_comm d] using t
lemma spice_R :∀ᶠ i in atTop,0 < rainX R 1 i ∧1 ≤ rainX R 2 i∧ 0 < Scales.g SU.group R.L i:=by
 filter_upwards [(sizeK.main R.L).spine.eventually (ge_mem_nhds zero_lt_one),(year SU.group R.L).eventually_gt_atTop 0] with i p t; have he:=Scales.gauge _ _ t; exact ⟨zero_lt_one.trans_le (rain_one _ _ t p),rain_one _ _ t p,he⟩
-- C PRE.Lens.Fτ. Radius normalization budget and P parameter. A1 positive actually. provide match ± energies later. 
local notation "nk"=> (Glyph.numV P_+1)
local notation "ηs"=> tiltB A P_
abbrev νC(P:BudgetPoint)(A:ℝ):= 3+4*|u0 P| * tiltB A P
abbrev Rone (a P x d:ℝ):ℝ:=4*a*(|P|+x^2)/d^2
lemma desire (h:0<A): 0 < tiltB A P_:= by unfold tiltB; positivity
lemma point_g(R:Patch) (h: sizeK R.L 2 F)(d:ℝ):sizeK R.L 2 (fun x=>Rone ηs (F x) (Scales.g SU.group R.L x) d):=by
 unfold Rone; simp_rw [div_eq_mul_inv]; let Z:= (h.accrue h); exact ((((iFX h).accrue ((sizeK.main R.L).square 2)).scale _).tint (sizeK.mild R.L _)) -- tune quotes
-- fees explicit.Binding.A.Pre
variable {a b c D U W η g1 ζ0:ℝ}(hA:0 < A)(hu:0 ≤ F x)
abbrev γ₀(P:BudgetPoint)(a b c d W:ℝ):=cap2 P c 1 a*W^2+cap2 P b 1 a
abbrev lobe (A W c:ℝ)(P:BudgetPoint):Prop:= c ≤ W^2/(4*tiltB A P)
abbrev Lamm (p:BudgetPoint)(x d b:ℝ):= φcape p x d b -- noop
lemma probate_0(hA:0<A)(hp:1≤W)(u:0 < g1)(hX: lobe A W (γ₀ P_ a b c d W) P_)(y:ℝ)(hs:y≤ g1^2):let P':=Pz x; let K:= Rone ηs (F x) g1 W; let v:= φcape P' a (b*K) (c*K) W; v≤ |F x|+ g1^2 ∧ tiltB A P'*(F x+v+y)/W^2 ≤ K ∧(0 ≤ F x → F x+v+y+Glyph.cap1 P' (BondL.øK K) W ≤ νC P_ A*(F x+g1^2)):=by
 intro P' K v; have ht: v≤|F x|+g1^2:=by
    unfold v; change φcape (Pz x) _ _ _ _ ≤ _; rw [φc_Q]; change γ₀ P_ a b c d W *K≤_; have ht:0 < ηs:=desire P_ hA; have hk:0≤ K:=by unfold K Rone; positivity
    refine (mul_le_mul_of_nonneg_right hX hk).trans (le_of_eq ?_); change W^2/(4*ηs)*_= _; unfold K Rone; field_simp -- tune ring
 have h:=desire P_ hA; have hx:P'.power=P_.power:=(let_X ..).2.1; refine ⟨ht,?_,?_⟩
 · rw [show tiltB A P'=ηs from (by unfold tiltB; rw [hx])]; unfold K Rone; apply div_le_div_of_nonneg_right _ (by positivity); calc
     _ ≤ ηs*(4*(|F x|+g1^2)):=mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (F x),le_abs_self (F x),sq_nonneg g1]) h.le
     _ = _ :=by ring
 intro p; have hq:u0 P_* K * W^2= u0 P_*(4*ηs*(|F x|+g1^2)):=by unfold K Rone; field_simp
 have he:= cap1_g P_ x W K; change F x+ v +y+cap1 (Pz x) (BondL.øK K) W≤_; rw [he,hq, abs_of_nonneg p]; rw [abs_of_nonneg p] at ht; have hr:0 ≤ 4*ηs*(F x+g1^2):=by positivity
 let C:=νC P_ A; have hg:= mul_le_mul_of_nonneg_right (le_abs_self (u0 P_)) hr; unfold νC; nlinarith [sq_nonneg g1]
end YM.CF.Py
