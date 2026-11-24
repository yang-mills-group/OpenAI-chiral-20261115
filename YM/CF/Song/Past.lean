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
abbrev warmS (P:BudgetPoint)(F:ℝ→ℝ):Prop:=∀ᶠ i in atTop,0<F i ∧ degreePrice (hall_P P i).B (F i) wΨ<1
local notation "gL"=> Scales.g SU.group R.L
local notation "zP"=> rainX R 1
local notation "zD"=> rainX R 2
lemma buy_B (M:ℝ)(u:0 < d) : ∀ᶠ x:ℝ in atTop, M ≤ d*(hall_P P_ x).B:=by
 obtain ⟨t,v⟩:=exists_nat_gt (M / d); filter_upwards [hall_l P_,Work.E01.radiusB_tendsto.eventually_ge_atTop t] with x h p; rw [h]; have he:= (div_lt_iff₀ u).mp v; rw [mul_comm]; exact he.le.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr p) u.le)
variable (A W a b c:ℝ)(ha:0 < a)(hu:0<A)(hW:1 ≤ W)(hl:lobe A W (γ₀ P_ a b c 0 W) P_)
include ha hu hW hl
abbrev Rtor(P:BudgetPoint)(R:Patch)(A W:ℝ)(F:ℝ→ℝ)(x:ℝ):ℝ:=Rone (tiltB A P) (F x) (Scales.g SU.group R.L x) W
local notation "ρ"=> Rtor P_ R A W F
local notation "βG"=> (fun x=> (gL x)^2)
abbrev γK(R:Patch)(Γ:ℝ→ℝ)(x:ℝ):=(rainX R 2 x)⁻¹*Γ x
lemma nova_X (f:sizeK R.L 2 F)(g:sizeK R.L 1 G)(h:sizeK R.L 3 H) : ∃ (Γ Θ ε:ℝ→ℝ),sizeK R.L 1 Γ ∧sizeK R.L 1 Θ∧ sizeK R.L 2 ε ∧ sizeK R.L 2 ρ ∧sizeK R.L 3 (γK R Γ) ∧∀ᶠ x in atTop,0 < ρ x ∧ 0 < Θ x ∧ degreePrice (hall_P P_ x).B (Θ x) wΨ < 1 ∧ Sour.Pace (Pz x) a (b*ρ x) (c*ρ x) W (ρ x) (Γ x) (ε x) (G x) (H x) (F x) (Θ x) (zP x) (zD x) A ∧ (0 ≤ F x→Dq (Pz x) a (b*ρ x) (c*ρ x) (F x) (Θ x) (zP x) W (Γ x) (ε x) (ρ x) ≤ νC P_ A*(F x+ (Scales.g SU.group R.L x)^2)) :=by
 have he:= point_g (A:=A) P_ F R f W; let V':= Rtor P_ R A W F; let D(x):=feeΨ (Pz x) a (b*V' x) (c*V' x) W; have hd :sizeK R.L 2 D:=fee_f P_ V' a b c W he; let ε(x):=|D x|; have hp:sizeK R.L 2 ε:=iFX hd
 let Γ(x):= |G x+rainX R 2 x*H x| + gL x; have hx:sizeK R.L 1 Γ:=(iFX (g.accrue (rockP 2 h))).accrue (sizeK.main R.L); let V₀(x):=rentΦ (Pz x) (Γ x) (ε x); have h0:sizeK R.L 3 V₀:= pole_Q P_ Γ ε hx hp; let C'(x):= G x+Γ x+zP x*(ε x+V₀ x); let Θ(x):=|C' x|+gL x; have ht:sizeK R.L 1 Θ:=(iFX ((g.accrue hx).accrue (rockP 1 (hp.accrue (h0.low (by omega)))))).accrue (sizeK.main _)
 let Λ(x):=tintK (Pz x) (V₀ x) (Θ x) (zP x); have hf:= σΩ P_ Θ V₀ ht h0
 refine ⟨Γ,Θ,ε,hx,ht,hp,he,(rain_l R 2).tint hx,?_⟩
 let s (x:ℝ):=spanV (Pz x).B; have hm:=spg_B (R:=R) P_; have hw:0 < wΨ:=by norm_num [wΨ]
 filter_upwards [(hm.tint hx).spine.eventually (ge_mem_nhds zero_lt_one), ((hm.tint hp).low (k:=1) (by omega)).spine.eventually (ge_mem_nhds (show 0 < wΨ/4 from by positivity)), pill_R (k:=1) ε (show 0<wΨ/4 from by positivity) hp,pill_R (k:=2) Λ zero_lt_one hf,(fee_Q P_ Θ ht).spine.eventually (Iio_mem_nhds zero_lt_one), spice_R (R:=R),buy_B P_ (2*P_.supportExponent*Fief.tileN 1) (show 0<a/2 from by positivity),buy_B P_ (2*(wu P_+2)*Fief.tileN 1) (show 0<a/2/2 from by positivity)] with x b₁ pZ vZ hZ z' v l hl'
 have hu0:gL x≤ Γ x:= le_add_of_nonneg_left (abs_nonneg _); have hΓ:=v.2.2.trans_le hu0; have hΘ:0<Θ x:= add_pos_of_nonneg_of_pos (abs_nonneg _) v.2.2; let P:=Pz x; rw [pow_one] at vZ; simp only [one_mul] at hZ
 obtain ⟨w,tq,xq⟩:= probate_0 P_ F hu hW v.2.2 hl (Λ x) hZ.le; have hα:0 < V' x:=by have he:=desire P_ hu; have ht:gL x>0:= v.2.2; unfold V' Rtor Rone; positivity
 have hs:P.supportExponent=P_.supportExponent:= (let_X ..).2.2
 refine ⟨hα,hΘ,z',⟨?_,?_,abs_nonneg _,le_abs_self _,(le_abs_self _).trans_lt (lt_add_of_pos_right _ v.2.2),hΓ.le,b₁, pZ.trans (by linarith), ?_,(le_abs_self _).trans (le_add_of_nonneg_right (v.2.2.le)),hΘ,z',tq⟩,fun t=>xq t⟩ --- hx, d0
 · rw [(let_X P_ _).2.2]; exact l
 · unfold wu; rw [(let_X P_ _).2.2]; exact hl'
 change s x* ε x ≤ _ at pZ; change ε x+s x*ε x* Γ x - (_ - s x*ε x)*Γ x<0; have ht: ε x< wΨ/4*Γ x:= (vZ.trans_le (mul_le_mul_of_nonneg_left hu0 (by positivity))); have lt:=mul_le_mul_of_nonneg_right pZ hΓ.le; change 0< Γ x at hΓ; unfold wΨ at *; linarith only [ht,hΓ,lt]
omit ha hu hW hl
-- small K afterL.M taken d shrinks further. Mood pre design eps from shape before L, uses fee.Telescope
lemma era_x(A :ℝ)(hu:0 < A): ∃ ε:ℝ,0< ε ∧∀ {a b c:ℝ},0<a→0 ≤ c → oom (numV P_+1) a*c ≤ ε→ ∀ᶠ W:ℝ in atTop, lobe A W (γ₀ P_ a (Tenant.quota^2*b) (Tenant.quota^2*c) 0 W) P_ :=by
 let k:=numV P_+1; let B:=cap2 P_ (Tenant.quota^2) 1 1; let V:= tiltB A P_; have he:= desire P_ hu; change 0<V at he; let y:=1/(4*V); have hp:0< y:=by unfold y; positivity
 refine ⟨y/(4*(1+|B|)),by positivity,fun {a b c} p h u=>?_⟩
 have hq:cap2 P_ (Tenant.quota^2*c) 1 a ≤ y/2:=by
    have ht: cap2 P_ (Tenant.quota^2*c) 1 a=B*(oom k a*c):=by unfold B k cap2 oom; ring
    let X:= oom k a*c; have hh:X ≤ y/(4*(1+|B|)):=u; rw [ht]; have hv:0 ≤ X:=by unfold X oom; positivity
    refine le_trans (mul_le_mul (le_abs_self B) hh hv (abs_nonneg _)) ?_; have hx:(4:ℝ)*(1+|B|)>0:=by positivity
    rw [←mul_div_assoc,(div_le_iff₀ hx)]; nlinarith [abs_nonneg B]
 let B':=cap2 P_ (Tenant.quota^2*b) 1 a
 filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (B'/(y/2))] with W p v; rw [div_le_iff₀ (show 0 < y/2 from by positivity)] at v
 unfold lobe γ₀; change _ ≤ W^2/(4*V); rw [div_eq_mul_one_div]; change _+B' ≤ W^2*y; refine (add_le_add (mul_le_mul_of_nonneg_right hq (sq_nonneg W)) (v.trans (mul_le_mul_of_nonneg_right (by nlinarith : W≤ W^2) (by positivity : 0 ≤ y/2)))).trans_eq (by ring)
end YM.CF.Py
