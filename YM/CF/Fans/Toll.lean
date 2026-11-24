import YM.CF.Neon.Pack
import YM.CF.Song.Past
import YM.CF.Song.Crest
import YM.CF.Song.Height
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
set_option maxHeartbeats 800000
variable (P_:BudgetPoint)(F G H:ℝ→ℝ)
local notation "Pz"=> hall_P P_
local notation "gL"=> Scales.g SU.group R.L
local notation "zP"=> rainX R 1
local notation "zD"=> rainX R 2
abbrev ψM (P:BudgetPoint)(d μ:ℝ):= spanV P.B*d*μ+spanV P.B*wΨ⁻¹*μ*d
abbrev μpulse (P:BudgetPoint)(x ν:ℝ)(n:ℕ):=ν⁻¹ * (grain_q P.B P.order P.power 1 x n) + ν⁻¹ * (grain_q P.B P.order P.power 1 x n)
abbrev σ₁ (P:BudgetPoint)(x ν d μ:ℝ):=μpulse P x ν 1+ψM P d μ+ψM P d μ
abbrev ΦM (P:BudgetPoint)(x ν d Γ μ:ℝ):ℝ:= σ₁ P x ν d μ+2*ν⁻¹*(Γ*(degreePrice P.B Γ wΨ)^1*(1-degreePrice P.B Γ wΨ)⁻¹)+2*(Γ*(degreePrice P.B Γ wΨ)^2*(1-degreePrice P.B Γ wΨ)⁻¹)
local notation "Pδ"=> grain_q P_.B P_.order P_.power (1:ℝ)
structure κPass (a b c d ν y κ HH Γ μ D E :ℝ):Prop where
 note :0 ≤ d
 pole : 2*(wu P_+2)*Fief.tileN 1 ≤ a/2/2*P_.B
 pin : feeΨ P_ a b c HH≤ d
 carry : grain_q P_.B P_.order P_.power 1 y 0+ κ*(κ⁻¹*(grain_q P_.B P_.order P_.power 1 y 0))< μ
 cost: spanV P_.B*μ ≤1 ∧ spanV P_.B *d ≤wΨ ∧ d + spanV P_.B*d*μ-(wΨ-spanV P_.B*d)*μ < 0
 pay: μ+μ+ν*(μpulse P_ y ν 0+σ₁ P_ y ν d μ)≤ Γ
 ip:0 ≤ μ ∧ 0< Γ ∧ degreePrice P_.B Γ wΨ<1
 karma :ΦM P_ y ν d Γ μ = D ∧ μpulse P_ y ν 0=E
structure κLast (Γ qF M0 v1 κ μB K:ℝ):Prop where
 worth : 0<qF ∧ degreePrice P_.B qF 1 ≤ 1/2
 high : M0 + v1 + Beau.rateΓ P_ Γ wΨ ≤1 ∧ κ*μB + Real.exp 1*(Beau.rateΓ P_ Γ wΨ+(M0+v1)) ≤qF
 gain: reserveT P_.power P_.order P_.B (1/2:ℝ)*(κ⁻¹*(qF*((1:ℝ)/2)^0*(1-1/2)⁻¹)) = K -- fixed numerical
variable {v u A W a b c:ℝ}{k₀ M₀:ℕ}{hp:1 ≤ W}
lemma lL_p (n:ℕ)(h:sizeK R.L n F):sizeK R.L n fun i=>|F i|:=(iFX h)
lemma grains (n:ℕ)(f:sizeK R.L 1 F)(hk:warmK F): sizeK R.L (n+1) (fun i=> grain_q (hall_P P_ i).B (hall_P P_ i).order (hall_P P_ i).power 1 (F i) n):=by
 apply (ample_b hk f P_.order P_.power n 1).cost_d; filter_upwards [hall_l P_] with i t; rw [(let_X P_ i).1,(let_X P_ i).2.1,t]
-- grant: reserve μ,d, spectra.For PH normalization car before x.Latest returns raw EXACT d,d_hint order.Math.
lemma focal_ξ (f:sizeK R.L 1 F)(g:sizeK R.L 2 G)(hF: warmK F)(ha:0 < a)(W b c:ℝ):∃ (Γ Q μ D E:ℝ→ℝ),sizeK R.L 1 Γ∧sizeK R.L 2 Q∧sizeK R.L 3 (γK R μ) ∧ sizeK R.L 1 μ∧ sizeK R.L 3 D ∧ sizeK R.L 2 E ∧∀ᶠ x in atTop,0 < Γ x ∧ κPass (Pz x) a (b*G x) (c*G x) (Q x) (rainX R 1 x) (F x) (rainX R 2 x) W (Γ x) (μ x) (D x) (E x):=by
 let Q(x):=|feeΨ (Pz x) a (b*G x) (c*G x) W|; have h:sizeK R.L 2 Q:= lL_p _ 2 (fee_f P_ G a b c W g)
 let M(x):=grain_q (hall_P P_ x).B (Pz x).order (Pz x).power 1 (F x) 0; let V(x):=M x+ zD x*((zD x)⁻¹ * M x); -- inv field typo fix
 have hM:sizeK R.L 1 V:= (grains P_ F 0 f hF).accrue (rockP 2 ((rain_l R 2).tint (grains P_ F 0 f hF)))
 let μ(x):= |V x|+gL x; have hu:sizeK R.L 1 μ:=(lL_p _ _ hM).accrue (sizeK.main R.L)
 let P(n:ℕ)(x:ℝ):=μpulse (Pz x) (F x) (zP x) n
 have hP(n):sizeK R.L (1+(n+1)) (P n):=by have ht:=(rain_l R 1).tint (grains P_ F n f hF); exact ht.accrue ht
 let L(x):= σ₁ (Pz x) (F x) (zP x) (Q x) (μ x); have ht:sizeK R.L 3 (fun x=>ψM (Pz x) (Q x) (μ x)):=pole_Q P_ μ Q hu h -- namespace
 have hL:sizeK R.L 3 L:= ((hP 1).accrue ht).accrue ht
 let E(x):= μ x+μ x+ zP x*(P 0 x+L x); let Γ(x):= |E x|+gL x; have hΓ:sizeK R.L 1 Γ:=(lL_p _ _ ((hu.accrue hu).accrue (rockP 1 ((hP 0).accrue (hL.low (by omega)))))).accrue (sizeK.main _)
 let Z:= zeST P_ Γ; have he:sizeK R.L 1 Z:= fee_Q P_ Γ hΓ; let K(x):=(1-Z x)⁻¹
 have hk:sizeK R.L 0 K:=by
    have hx:Tendsto K atTop (𝓝 1):=by simpa using ((tendsto_const_nhds (x:=(1:ℝ))).sub he.spine |>.inv₀ (show (1:ℝ)-0≠0 by simp)); -- tune
    exact (sizeK.mild R.L 2).cost_d (hx.abs.eventually (ge_mem_nhds (by norm_num : |(1:ℝ)| < |(2:ℝ)|)))
 have hm(m:ℕ):sizeK R.L (1+m) (fun x=> Γ x*Z x^m*K x):=by exact (hΓ.tint (by simpa using he.square m)).tint hk
 let D(x):= ΦM (Pz x) (F x) (zP x) (Q x) (Γ x) (μ x); have hz:sizeK R.L 3 D:=(hL.accrue (((rain_l R 1).scale 2).tint (hm 1))).accrue ((hm 2).scale _)
 refine ⟨Γ,Q,μ,D,P 0,hΓ,h,(rain_l R 2).tint hu,hu,hz,hP 0,?_⟩
 let s (x:ℝ):=spanV (Pz x).B; have hm:=spg_B (R:=R) P_; have hw:0 < wΨ:=by norm_num [wΨ]
 filter_upwards [spice_R (R:=R), (hm.tint hu).spine.eventually (ge_mem_nhds zero_lt_one), ((hm.tint h).low (k:=1) (by omega)).spine.eventually (ge_mem_nhds (show 0 < wΨ/4 from by positivity)),pill_R (k:=1) Q (show 0<wΨ/4 from by positivity) h,buy_B P_ (2*(wu P_+2)*Fief.tileN 1) (show 0<a/2/2 from by positivity),he.spine.eventually (Iio_mem_nhds zero_lt_one)] with x t xq pq ph v ψ
 have huv:gL x≤ μ x:= le_add_of_nonneg_left (abs_nonneg _); have hx:= t.2.2.trans_le huv; have hG:0<Γ x:= add_pos_of_nonneg_of_pos (abs_nonneg _) t.2.2; rw [pow_one] at ph
 refine ⟨hG,⟨abs_nonneg _,?_,le_abs_self _,(le_abs_self _).trans_lt (lt_add_of_pos_right _ t.2.2),⟨xq,pq.trans (by linarith only [hw]),?_⟩,(le_abs_self _).trans (le_add_of_nonneg_right (t.2.2.le)),⟨hx.le,hG,ψ⟩,rfl,rfl⟩⟩ -- explicit parse
 · unfold wu; rw [(let_X P_ x).2.2]; exact v
 change s x* Q x ≤ _ at pq; have hu:= mul_le_mul_of_nonneg_right pq hx.le; have ht: Q x< wΨ/4*μ x:= ph.trans_le (mul_le_mul_of_nonneg_left huv (by positivity)); change Q x+s x* Q x*μ x-(_-s x*Q x)*μ x <0; unfold wΨ at *; linarith only [ht,hx,hu]
local notation "gV"=> Scales.g SU.group R.L
lemma Φearn (p:Chill_v H)(h:sizeK R.L 1 F)(g:sizeK R.L 3 G)(hZ:∀ᶠ x in atTop,0< F x)(v1:ℝ→ℝ)(l: Chill_v v1): ∃ K V:ℝ→ℝ,Litt R 2 K ∧ Chill_v (fun x=> K x/(Scales.g SU.group R.L x)^2) ∧ Chill_v V ∧∀ᶠ x in atTop, κLast (Pz x) (F x) (V x) (H x) (v1 x) (rainX R 2 x) (G x) (K x):=by
 obtain ⟨V,hV,hp,Lt,k⟩:= crown_T P_ R F G (fun x=> H x+v1 x) h hZ g P_.order P_.power (p.noteR l)
 let Y(x):=reserveT (Pz x).power (Pz x).order (Pz x).B (1/2); let f(x):=V x*((1:ℝ)/2)^0*(1-1/2)⁻¹; let K(x):= Y x * ((zD x)⁻¹ * f x);
 have hh:BoreP Y:=(Nor.vale_u P_.power P_.order (1/2:ℝ)).tune (by filter_upwards [hall_l P_] with x t; unfold Y; rw [(let_X P_ x).2.1,(let_X P_ x).1,t]) -- check order: vale
 have hv:Chill_v f:=(hV.cheap ((1-(1:ℝ)/2)⁻¹)).trend (Eventually.of_forall fun i=>by unfold f; exact Eq.le (congrArg abs (by ring)))
 have hu: Chill_v (fun x=> K x/gV x^2):= (hv.leanB hh).trend (by
    filter_upwards [spice_R (R:=R)] with x p; apply Eq.le; congr 1; have he:gV x>0:=p.2.2; unfold K rainX; rw [inv_inv]; field_simp)
 refine ⟨K,V,hu.pane,hu,hV,?_⟩ -- Order names conflict
 filter_upwards [hp,k,hall_l P_] with x p t q; exact ⟨⟨p.1,q.symm ▸ p.2⟩,t,rfl⟩
end YM.CF.Py
