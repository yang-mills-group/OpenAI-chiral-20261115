import YM.CF.Robin.Hind
import YM.CF.Song.Height
import YM.CF.Neon.Spring
import YM.CF.Swell.VitaK
import YM.CF.Swell.Vote
import YM.CF.Swell.Chill
import YM.CF.Swell.Beam
import YM.CF.Swell.Hush
import YM.CF.Swell.Harp
import YM.CF.Swell.Lawn
import YM.CF.Swell.Bark
import YM.CF.Swell.Tap
import YM.CF.Swell.Fist
import YM.CF.Mew.Tube
import YM.CF.Pso.Pick
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow Py
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
open Push.AbsoluteSums Trees Wray Ione Fief
variable {N B m L:Side}
variable {r:ℕ}
variable {I:Type}[Fintype I][LinearOrder I]
variable {P:BudgetPoint}(E':GramM (mid m B))
open Neon Hom Vale Vale.Grace Kea Nova RP RP.Str Spark Wilson Precision Next.Free Gauge Paige Vault Brace Spire Pressure Jade Oise
variable {A:Teller SU.group}{W:ChartRatio SU.group}{Zp:Patch}(D:Grace A Zp W){d e g x b a t u0 K Kt f l α s':ℝ}
open Roots Chaff Next.SectorChange Next.SectorChange.Schur SectorNext.Remainder SectorNext.Remainder.Scales Pail Lor
local notation "λo" => (allotΨ Zp.L)
variable(P_: BudgetPoint) (F:ℝ→ℝ)
local notation "zp" => (hall_P P_)
local notation "vχ" => (Scales.g SU.group Zp.L)
variable {c a0 h K0 M ΨH A0:ℝ} {k:ℕ}
local notation "A_" i:max => Nano_W ((hall_P P_ i)) e a (allotΨ Zp.L i) h c -- potential
lemma ppΔ: 0 ≤ Δv P b:=by unfold Δv; positivity
lemma ppK:0 ≤ 2*peka_H P.power:=by unfold peka_H κP ξP pruneQ; have h:=Hove.mpe true; have h':= Hove.mpe false; positivity
lemma θlong (z:ℝ)(hz:0<z):0 < ΘS_F z:= by unfold ΘS_F; have h:=tt0; positivity
variable {Q':ℝ}
lemma ppη(v:0 ≤ Q') (u:0 ≤ e): 0 ≤ KarmaΓ P e a Q' h:=by unfold KarmaΓ Eraρ νt chipZ chal; have h1:=hcP_ge; have h2:=hPπ; have he:=Haro.p0; positivity
lemma ppNs(v:0≤ Q')(u:0≤e)(p0:0 < a)(p1:0 ≤ c):0 ≤ Nano_W P e a Q' h c ∧ 0≤ Nano_T P e a Q' h c:=by
 have hp:=ppη (P:=P) (a:=a) (h:=h) v u
 have hk(k:ℕ):0 ≤ Sour.aimV k a (θG P):=by unfold Sour.aimV; apply mul_nonneg (by positivity); apply mul_nonneg (Real.exp_pos _).le; exact tsum_nonneg fun i=>by unfold Tenant.quota; positivity
 have ht:0 ≤ νmeta P a:=by unfold νmeta reserveT coin_n stilK; positivity
 exact ⟨mul_nonneg (mul_nonneg (show 0≤ nold P a (θG P) h from by unfold nold; exact mul_nonneg (by positivity) (hk _)) hp) (show 0 ≤ ζ_fee c a from by unfold ζ_fee; positivity), mul_nonneg ht (mul_nonneg (by norm_num) (mul_nonneg p1 hp))⟩
lemma ppU (p:0 ≤ b)(q:0 ≤ e):0 ≤ BillV P k b e:=by
 have hx:=κRepoH; have hu:0≤ Cu_μ P k b:=by unfold Cu_μ feeU; positivity
 have he(i):0 ≤ Ξ₂ P i k b:= mul_nonneg (by unfold μReq Sour.spanV; positivity) hu
 unfold BillV reserveT coin_n stilK μhcp; have h:0 ≤ Sour.spanV P.B:=by unfold Sour.spanV; positivity
 exact mul_nonneg (by positivity) (add_nonneg (add_nonneg (mul_nonneg (he 1) q) (mul_nonneg (mul_nonneg (he 2) q) q)) (mul_nonneg (add_nonneg hu (mul_nonneg (by positivity) (he 1))) (mul_nonneg h q)))
lemma thu (v:0 ≤ b)(u:0 ≤ K) : 0 ≤ Yρ P b K:=by unfold Yρ κplant deck_K composeCost chipZ chal trotΦ Taxi.tollV stakeH flavor Oath.γD; have hκ:= AnalyticBridge.VerifiedReset.pair_nonneg SU.group P; have hx:= Haro.wheels_p (n:=P.order); have ht:= Haro.p0; positivity
lemma lift_Needs (p:∀ᶠ x in atTop,0 ≤ F x)(M k:ℕ)(G:ℝ→ℝ)(f:sizeK Zp.L 2 F)(g:sizeK Zp.L 2 G) :∀ᶠ x in atTop, let t:=hall_P P_ x; NeedU t (F x) (G x) (Scales.g SU.group Zp.L x) M:=by
 obtain ⟨vE,H⟩:= credit_ζ (k:=M) P_ _ f
 have hx:= (vE.low (show 1 ≤ 2 by omega)).spine
 filter_upwards [hx.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2)),pill_R _ (k:=1) zero_lt_one (χpay P_ _ g),p,pill_R _ (k:=1) (by norm_num : (0:ℝ)<1/2) H,spice_R (R:=Zp)] with x p u p0 h h_ t -- signature adjust
 have ht:0 < vχ x := h_.2.2; rw [pow_one,one_mul] at u; rw [pow_one] at h
 refine ⟨p0,u,ht,p.trans (by norm_num),h.trans_le ?_⟩
 refine mul_le_mul_of_nonneg_right ?_ ht.le
 change 1/2≤ 1-DebtP ((hall_P P_ x)) M (F x) (vχ x); linarith
#check pill_R
abbrev vitaE(P_:BudgetPoint)(a:ℝ):= Yρ P_ a (hc_P*Hπ)
abbrev needE(P_:BudgetPoint)(a:ℝ):ℝ:=vitaE P_ a+1
lemma vest_Z(b:ℝ) :∃ s:ℝ,0<s ∧ s+s ≤ ΘS_F hc_P ∧ 2*peka_H P.power*(s+s) ≤ ΘS_F hc_P∧Δv P b*(s+s) ≤ 1:=by
 let W:=2*peka_H P.power; let A:=ΘS_F hc_P; have he:0<A:=θlong _ hcP_ge
 let F:ℝ→ℝ:=fun x=> x+x; have hx:F 0=0:=zero_add _; let G:=Δv P b; let t:=nhdsWithin (0:ℝ) (Set.Ioi 0); have hf:Tendsto F t (𝓝 0):= by simpa only [zero_add] using (show Tendsto F t (𝓝 (0+0)) from (show Tendsto id t (𝓝 0) from nhdsWithin_le_nhds).add nhdsWithin_le_nhds)
 have ht(R:ℝ): Tendsto (fun x=> R*F x) t (𝓝 0):=by simpa only [mul_zero] using hf.const_mul R
 obtain ⟨x,(h:0<x),p,hz,g⟩:=Eventually.exists ((show ∀ᶠ y in t, y∈Set.Ioi (0:ℝ) from self_mem_nhdsWithin).and ((hf.eventually (ge_mem_nhds he)).and (((ht W).eventually (ge_mem_nhds he)).and ((ht G).eventually (ge_mem_nhds zero_lt_one)))) : ∀ᶠ i:ℝ in t, i∈ Set.Ioi 0 ∧ F i ≤ A ∧ W*F i ≤ A ∧ G*F i ≤ 1)
 exact ⟨x,h,p,hz,g⟩
lemma ppTaxes {k₀ k₁:ℝ}(p:needE P_ b ≤ k₀)(p':mΘ*k₀+1 ≤ k₁)(u:0 ≤e)(p0:0 < a)(p1:0 ≤ c)(z:0 ≤ b) :∀ᶠ h:ℝ in atTop,∀ F:ℝ→ℝ,sizeK Zp.L 2 F →∀ᶠ x:ℝ in atTop, let P:=hall_P P_ x; let Q:= allotΨ Zp.L x; Taxes P (Nano_W P e a Q h c) (Nano_T P e a Q h c) (Scales.g SU.group Zp.L x) b Q (Yρ P b (Eraρ Q* Hπ)) (F x) k₀ k₁ mΘ 0 0:=by
 obtain ⟨s,x0,x1,x2,x3⟩:=vest_Z (P:=P_) b
 filter_upwards [(ζnk (P:=P_) (e:=e) (a:=a) (c:=c) 1).eventually (ge_mem_nhds x0)] with h q F w
 let A(x):= Nano_W (hall_P P_ x) e a (allotΨ Zp.L x) h c; have hf:sizeK Zp.L 2 A:=Nano_w ..; let T (x):=BillV (hall_P P_ x) mΘ (A x) (Scales.g SU.group Zp.L x); have hp:sizeK Zp.L 3 T:= Ζbuf _ _ hf _
 have hx:∀ᶠ x in atTop, 0 ≤ A x:=by filter_upwards [spice_R (R:=Zp)] with x hx; have h:0 ≤ allotΨ Zp.L x:= sq_nonneg _; exact (ppNs h u p0 p1).1
 filter_upwards [hx,pill_R -- tune
      _ x0 (k:=2) (apexT_k _ _ hp), pill_R _ zero_lt_one (k:=2) (hp.accrue (δfee P_ _ hp mΘ)),lift_Needs P_ _ hx mΘ 1 _ hf w] with x pV pA pc qU t Q
 let K:=Scales.g SU.group Zp.L x; have hK:0<K:=qU.high; have hQ:0 ≤ Q:=sq_nonneg K; let Z:=T x; let V:= Nano_T t e a Q h c; let W:= P_U t V Z; have he:V =Nano_T P_ e a 1 h c*Q:=μg ..
 have hz:W ≤ (s+s)*Q:=by unfold W P_U; apply (add_le_add pA.le (le_trans he.le (mul_le_mul_of_nonneg_right q hQ))).trans; rw [← add_mul]
 obtain ⟨s1,s2,s3⟩:=let_X P_ x; let Δ:=Δv t b
 have hΔ:Δ=Δv P_ b:=Ves _ _ s1 s2 s3 _
 have h_C: Yρ t b (Eraρ Q* Hπ)=vitaE P_ b*Q:=(vρ (a:=b) _ _ Q _).trans (mul_comm ..)
 have h_0: Yρ t b (Eraρ Q*Hπ)+Τσο t b V Z ≤ k₀*Q:=by
    rw [h_C]; apply (add_le_add_right (le_trans (mul_le_mul_of_nonneg_left hz (ppΔ (P:=t))) (show Δ*((s+s)*Q)≤1*Q from by rw [hΔ,← mul_assoc]; exact mul_le_mul_of_nonneg_right x3 hQ)) _).trans; rw [←add_mul]; exact mul_le_mul_of_nonneg_right p hQ
 have hu:ΘS_F (Eraρ Q)= ΘS_F hc_P*Q:=by unfold ΘS_F Eraρ; ring
 have hk': 2*peka_H t.power=2*peka_H P_.power:=by rw [show t.power=P_.power from s2]
 refine ⟨qU,⟨thu z (mul_nonneg (mul_nonneg hQ hcP_ge.le) hPπ),(ppNs hQ u p0 p1).2,ppU pV hK.le⟩, hz.trans ((mul_le_mul_of_nonneg_right x1 hQ).trans_eq hu.symm), (mul_le_mul_of_nonneg_left hz (ppK (P:=t))).trans ?_ ,h_0,(add_le_add (mul_le_mul_of_nonneg_left h_0 (show 0 ≤ (mΘ:ℝ) from Nat.cast_nonneg _)) pc.le).trans ?_ ⟩
 · rw [hk',← mul_assoc]; exact (mul_le_mul_of_nonneg_right x2 hQ).trans_eq hu.symm
 change mΘ*(k₀*Q)+ 1*Q ≤ _; rw [← mul_assoc,←add_mul]; exact mul_le_mul_of_nonneg_right p' hQ
end YM.CF.Swell
#print axioms YM.CF.Swell.ppTaxes
