import YM.CF.BProof.Start.Sage
import YM.CF.BProof.Gates.Mcost

set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Start
open Function Filter MeasureTheory Finset
open Lattice Tenant Lat Cube Skye RG Angular Wilson Rhythm Hero Mark Branch
open scoped Topology BigOperators Classical
open Gates Gates.Stage Gates.Stage.Setup Mapping House
open Stint Tape Hearth Prime Estate Cliff
open Jet Paige Drapes Vault Oasis Bias Weights Cabinet Mint Contour
variable {N:Side}{d K:ℕ}{c:Clip}{w R v:ℝ}(S:Gates.Stage c w R v)
variable {m m' L B:Side}{j:ℕ}{a b l r:ℝ}{D:Spin.Ready j a b l r}{u:ℝ}(E:Essence D u)
variable {rₜ a':ℕ}(Δ: Rhythm.Note E (gap L a') rₜ)
variable {p:Odd L.val} {Y:Pricing j L p (Vault.Thread j)} {δ:ℝ}{F:Grasp Y B δ}
variable {E Δ S}{U H:ℝ} (J:Mote S E Δ F U H)
open Veil Anthem
namespace Mote
variable (B':ℝ→ℕ)(Fp:ℝ→ℝ)
local notation "κζ"=> gap L a'
local notation "μz"=> μ (Δ:=Δ)
open Pods Brick Act Seam Trek
abbrev quotaχ := Contour.Tower.feeχ 4 200
abbrev mB (y:ℝ):= Charge.mCost c R (2*y) (Weights.rent y S.M R w v) (DP L a' y) -- S parameter implicit!
abbrev kA (y:ℝ):=10*y^10
abbrev boughtP := acV S μz
abbrev τ(k:ℝ)(s:ℕ) := Pricing.skyLog S.P k c R s (S.M k) -- maybe delete
structure Licence (W:ℕ)(y:ℝ)(h:ℝ) where
 baseL : Entice S L a' W y
 routeL : Rhythm.Season E rₜ L a' Δ y W (S:=S)
 statL : Inside S E δ (Cliff.Economy.lipBill S.K.C) y
 gasL {N:Side}{D₀:Scree.GramM N}(p:D₀.p.supportExponent=1)(g:D₀.p.B=B' y): Oasis.Tube D₀ J.oak h (BProof.g y) (Fp y) (Oasis.feeα B' J.oak y) (J.ζy B' Fp y)
 solidL : Brick.Solid y κζ W
 tagL : (J.mode y W).Buy quotaχ (meters W) W κζ y
 seekL : Factor W (House.up 8) (acV S (μ (Δ:=Δ)) y) J.z 4
 gas : Factor W (House.up 8) (acV S (μ (Δ:=Δ)) y) (J.ζg B' y) 4
 roof : dome E.H Δ.clock+20<DP L a' y/32
 cap : dome E.H Δ.clock+20≤W
 clock :10*(TimePlus J.k (J.sizeC y) (μ (Δ:=Δ)))+10≤ DP L a' y/32
 roomV : TimePlus J.k (J.sizeC y) (μ (Δ:=Δ))+10≤W
 sumF : demand J B' Fp y W ≤ 1/8
 fuel : (J.mode y W).bias + root_port κζ (J.k+J.sizeC y) W*(2*(Primer.expL J.z (J.sizeC y)*J.payZ)) ≤ J.fuel/64*(W:ℝ)^3
 markPrice : Score.capS (DP L a' y) (J.priceA B' Fp y) (mB (S:=S) (L:=L) (a':=a') y) (piT (DP L a' y) y) ≤ kA y
 hit : 2+Pricing.skyLog S.P y c R κζ (S.M y)+ J.payZ≤kA y
-- combined powers. supply any future stretch V. reveal V function. 

variable {W: ℝ→ℕ}(pw: NAT W)(pB: NAT B')(hp: NPL Fp)
include J pB
abbrev needed (J:Mote S E Δ F U H)(B':ℝ→ℕ)(y:ℝ) := 1+S.bound y (gap L a')+Gates.stretch 4 J.z (acV S (μ (Δ:=Δ)) y) + Gates.stretch 4 (ζg J B' y) (acV S (μ (Δ:=Δ)) y) + TimePlus J.k (J.sizeC y) (μ (Δ:=Δ)) +10
lemma price_time : NAT fun y=> TimePlus J.k (J.sizeC y) μz := NAT.add (NAT.add (PL.const _) (NAT.mul (PL.const _) J.budgetClock)) (PL.const _)
lemma buysL : NAT (needed J B'):= by unfold needed; let a:= acV S μz; have he:= ac_pat S μz; refine NAT.add (NAT.add (NAT.add (NAT.add (NAT.add (PL.const _) (bound_p S _ (GP L a'))) (Gates.stretch_pl he (fun _=>J.hp) (PL.const _) _ (by norm_num))) (Gates.stretch_pl he (fun y=> (gas_p B' J.oak y).1) (αPL J.oak pB) _ (by norm_num))) (price_time J B' pB)) (PL.const _) -- tune include pB in price_time order
include hp
lemma quotes : ∀ᶠ y:ℝ in atTop, Score.capS (DP L a' y) (J.priceA B' Fp y) (mB (S:=S) (L:=L) (a':=a') y) (piT (DP L a' y) y) ≤ kA y:=by
 let f(y:ℝ):=(Score.capS (DP L a' y) (J.priceA B' Fp y) (mB (S:=S) (L:=L) (a':=a') y) (piT (DP L a' y) y)); have T:PL (priceA J B' Fp):=(PL.const _).add ((age_p J B' Fp pB hp).weak); let P:= Real.log Garden.sitePrice; let Λ:=2*Real.log 5
 filter_upwards [scale_domain L a',coin_strongLt (a:=1) (b:=0) (by norm_num) T,buyM S L a',eventually_ge_atTop (4:ℝ),eventually_ge_atTop P,eventually_ge_atTop Λ] with y h u ⟨v,w⟩ Y p₁ p₂
 let X:ℝ:=DP L a' y; have hy:0<y:=by positivity
 have ht:X≤2*y:=by
    apply le_trans (b:= (LP L y:ℝ)); exact Nat.cast_le.mpr (by unfold DP; omega); have hp:sizeP y ≤ y:=(le_trans (Real.exp_monotone (by nlinarith only [sq_nonneg (Real.log (Real.log y))] : Real.log y*1+Real.log (Real.log y)^2*(-2)+Real.log (Real.log y)*0≤ Real.log y)) (Real.exp_log hy).le); linarith only [hp,h.2.2.1.upper]
 rw [coinY hy] at u; have he:0≤X+1:=(by unfold X; positivity); unfold Score.capS Score.capP; change Λ+(_+_+(X+1)* (J.priceA B' Fp y)+(X+1)*P)≤_; let Z:= y^10; have ha : y^2 ≤ Z:= pow_le_pow_right₀ (by linarith :1≤y) (by omega); have hb : y^4 ≤ Z:=pow_le_pow_right₀ (by linarith :1≤y) (by omega); have hc : y+y+y≤y^2:=(by nlinarith); unfold kA
 nlinarith only [ha,hb,hc,Y,v,w,p₂,mul_le_mul_of_nonneg_left ((le_abs_self _).trans u.le) he,mul_le_mul_of_nonneg_left p₁ he,mul_le_mul_of_nonneg_right ht hy.le] -- unfold Z/mB tune
include pw
lemma availability (p: Tendsto W atTop atTop)(wT:∀ᶠ y in atTop,needed J B' y ≤ W y) (g:∀ᶠ y in atTop, 0≤Fp y)(h:ℝ)(u:coins J.oak≤h)(t:0<δ): ∀ᶠ y:ℝ in atTop, Nonempty (Licence J B' Fp (W y) y h):=by
 let t₀(y):= TimePlus J.k (J.sizeC y) μz; let D:= dome E.H Δ.clock+20; have ht:0≤quotaχ:=by unfold quotaχ Tower.feeχ; positivity -- tune
 let A:=quotaχ
 filter_upwards [wT,entice S L a' W pw (wT.mono fun y v=>by unfold needed at v; omega), Rhythm.measures E rₜ L a' Δ S W p, interior S E t, law_fee J.oak pB hp h u,g, coldStore κζ W pw (fun _=>Real.log (1/2)) (PL.const _),warmth S W (GP L a') pw _ (stampPrice J pw) p _ J.fuel_p A ht, (lengths L a').eventually_ge_atTop (32*(D+1)), p.eventually_ge_atTop D, pl_D L a' (fun y=>32*(10*t₀ y+10)) (NAT.mul (PL.const _) (NAT.add (NAT.mul (PL.const _) (price_time J B' pB)) (PL.const _))), (demandΩ J B' Fp pB hp pw).limit.eventually (ge_mem_nhds (by norm_num : 0 < (1:ℝ)/8)),weightCore J W,quotes J B' Fp pB hp,eventually_ge_atTop J.payZ] with y v ⟨H⟩ U cK K D₁ τW E1 l₁ η C' K₀ P₀ H' r -- fix Rhythm explicit
 have hp:0<κζ:=GP ..; unfold needed at v
 refine ⟨⟨H,U,cK,(fun p w=>K (Fp y) D₁ le_rfl p w.le),⟨H.dull.smallXi,H.dull.p.height.wallet,le_trans τW (Real.exp_log (by norm_num : (0:ℝ)<1/2)).le⟩,E1,stretch_p _ (by norm_num) J.hp (by omega),stretch_p _ (by norm_num) (gas_p ..|>.1) (by omega), by change D< _; omega,η,?_ , (by omega),K₀,P₀,H',?_⟩⟩
 · change 32*(10*t₀ y+10)<_ at C'; change 10*t₀ y+10 ≤ _; omega
 have hv:= H.dull.threshY; have hu: y ^ 2 ≤ y^10:= pow_le_pow_right₀ (by linarith) (by omega); unfold kA; nlinarith only [r,hv,hu,H.dull.cost_out]
-- compute prior warrant L_c: can use any PL further, take grow at least log y.
abbrev council (J:Mote S E Δ F U H)(B':ℝ→ℕ)(y:ℝ) := needed J B' y+Gates.r_F y S.scene.size
omit hp pw
lemma council_pt : NAT (council J B') ∧ Tendsto (council J B') atTop atTop:= ⟨NAT.add (buysL J B' pB) (F_pl _ (one_pos.trans_le S.scene.target)), tendsto_atTop_mono (fun y=> show Gates.r_F y S.scene.size ≤ J.council B' y from by unfold council; omega) (F_grows S.scene.size (one_pos.trans_le S.scene.target))⟩ -- p param missing mono
end Mote
end YM.CF.BProof.Start
