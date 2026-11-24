import GaugeFieldConstruction.AcrossRehearse
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 4100
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Tapestry.Altitude Tapestry.Exhibition
open TopologicalSpace
namespace Spine
variable {P : Spine} {s i k : ℕ}
open AcrossLands
open Py.Rate.AcrossShots VolumeRate
variable (P) (v:ℕ→ℝ)
local notation "Γ" => P.par
local notation "Y" => P.run
local notation "B" => P.large
open AcrossLands Tapestry Preparation AcrossShots
variable {n:ℕ}
open Heat Buffered Dial Tapestry.Fashion Py.Rate.Branch Haro
local notation "Κ" i:max=> P.run.voyage i
local notation "Τ" k:max=> P.run.uv k
local notation "Πβ" i:max k:max => Actual (Y).meter (Κ i).funds (Κ i).CapeT (Preparation.gaugeFreq Γ ((Y).tile*(Γ).M)) (Τ k)
local notation "ΤT" i:max k:max s:max => (totalTickets P i k s)

noncomputable abbrev canyonPriceSt (i k s:ℕ)(r:Bet (Τ k))(A:P.Effect):ℂ:= P.carryCostSt (i:=i) r s (attire (P.roadScriptSt i k s r A))
noncomputable abbrev canyonTopSt (i k:ℕ)(r:Bet (Τ k))(A:P.Effect):ℂ:= P.canyonPriceSt i k (Τ k) r A
variable {ε:ℕ→ℝ} {r:Bet (P.run.uv k)}{t:ℝ}(Q:P.WalletDebtSt (ε:=ε) v i k t r)(w:ReserveTape (P:=P) n i k)
include Q w
-- `verifySt` stronger resolution-Mark construction: at ALL scales unfolding the roadDressing. Can purchase at charged supports on each participating height, and literally evaluate on the new common tape at top. Explicit.
lemma bookSt_license (S:BillOfWork)(b:ℝ)(A:P.Effect)(h:Pocket P.calibration S s b A)(p:s≤ Τ k) : let U(d:ℕ):= (followBox («Λ»:= P.par) («l»:=P.width))^[d-s] (frameBudget S P.par P.width s); let F(d:ℕ):= attire (P.roadScriptSt i k d r A); P.PromptsTape (i:=i) r (F s) (frameBudget S P.par P.width s) F U ∧ let T:Mark (side Y i ((Y).uv k)):= F ((Y).uv k); let a(v:Pane (side Y i ((Y).uv k))):=T (v,v); Envelope a ∧ (P.canyonTopSt i k r A)= AcrossLands.position (mesh ((Y).ir i) (Γ).R.L ((Y).uv k)) (Γ).U ((Y).meter.a ((Y).uv k)) (v ((Y).uv k)) a :=by
 let T:= followBox («Λ»:=P.par) («l»:=P.width); intro U F
 let V:= frameBudget S P.par P.width s
 have hu: U s=V:=by unfold U; rw[Nat.sub_self]; rfl
 have hf: AtSupport false (Satin.region V (side Y i s)) (F s):= P.coverSt v Q w p h
 have hg(j)(d:s≤j): U (j+1)=T (U j) ∧ F (j+1)= P.climbTape j r (F j):=⟨by unfold U; rw [Nat.succ_sub d,iterate_succ_apply'],overheadSt P A (climbs P.Test d h.funded)⟩
 have q: PromptsTape P r (F s) V F U:=by
    refine ⟨⟨rfl,hu⟩,fun i t _=> hg i t,fun j t t'=>?_⟩
    induction j,t using Nat.le_induction with
    | base=> rw[hu]; exact ⟨hf,rfl⟩
    | succ j t H=>
      obtain ⟨u,z⟩:= H (by omega); let hx:=raisedReadingSt P v w Q j t' _ _ u
      rw [(hg j t).1,(hg j t).2]; exact ⟨hx.1,hx.2.trans z⟩
 obtain ⟨G,Y₁,u,f⟩:= P.names_at_tape v r w Q p V (F s) hf
 have he (j)(t:s≤j)(g:j≤Τ k): G j=F j:=by
    induction j,t using Nat.le_induction with
    | base=> exact u.origin.1
    | succ j t h=> rw [(u.grows j t g).2,h (by omega),(hg j t).2]
 let a:=Τ k; let t':=(q.owned (Τ k) p le_rfl).2; refine ⟨q,?_⟩; change Envelope (fun z:Pane (side Y i a)=>F a (z,z)) ∧ P.carryCostSt (i:=i) r (Τ k) (F (Τ k))= _; let hv:G a=F a:= he _ p le_rfl; rw [t', ←hv]; exact f

-- continuity tolerance per appointment, no quantitative complexity here.
variable (e:IntervalsSchedule P n v ε)
omit w
lemma walletRateSt (s:ℕ)(a:s< Τ k) (h:0 ≤ ε (Τ k)) : dist (roadFareSt P i k s r) (rawTariff Y s i k) ≤ ε (Τ k):=by
 apply ((P.deltaSt v Q a.le).2 a).trans; apply div_le_self h; exact le_add_of_nonneg_right (zero_le_one.trans (P.tickets_hi ..))

omit Q
-- can demand simultaneous costs at any such permitted shoulder (not requiring geometric agreement with a second volume). These estimates ∀ s ≤ k work on the varying-Halos. Doesn't assume compact-input support.
lemma payMeterStepsSt (i k s:ℕ)(u:s ≤ Τ k)(b:ℝ)(h:0<b): ∀ᶠ δ:ℝ in 𝓝[>] (0:ℝ), ∀ (ε v:ℕ→ℝ), ε (Τ k)≤ δ → 0 ≤ ε (Τ k) → ∀ (t:ℝ)(r:Bet (Τ k)), P.WalletDebtSt v (ε:=ε) i k t r → ∀ j<s, ‖P.roadArtSt i k j r-Tapestry.music Y j i k‖ ≤ b:=by
 let T (j:ℕ):= rawTariff Y j i k; choose d e p using fun j:ℕ=> Metric.continuousAt_iff.mp ((Tapestry.streaming Y j i).continuousAt (x:=T j)) b h
 filter_upwards [(eventually_all_finset (range s)).mpr fun j v=> (gt_mem_nhds (e j)).filter_mono (nhdsWithin_le_nhds)] with δ a ε v hp hv t r h j hj
 rw [←dist_eq_norm]; exact (@p j _ (((P.walletRateSt v h j (lt_of_lt_of_le hj u) hv).trans hp).trans_lt (a j (mem_range.mpr hj)))).le

lemma primeMeterSt (i k:ℕ)(θ:ℝ)(z:0<θ):∃ d> (0:ℝ),∀ ε v:ℕ→ℝ, (0< ε (Τ k) ∧ ε (Τ k)<d)→∀ t (r:Bet (Τ k))(s:ℕ), ((Y).voyage i).kick ≤ k→ P.WalletDebtSt v (ε:=ε) i k t r→ s≤ Τ k → ∀ S b A,Pocket P.calibration S s b A→
    ‖P.canyonPriceSt i k s r A-taking Y B i k A‖ ≤ θ*(cloudSpan s S*b) :=by
 let T:= totalTickets P i k (Τ k); have hT:0 <T:= zero_lt_one.trans_le (P.tickets_hi ..)
 let C (s:ℕ):=‖savings Y s i k‖; let d(s:ℕ):=min 1 ((θ/2)/(1+C s))
 have hV(s:ℕ):0 ≤ C s:= norm_nonneg _
 have hD(s:ℕ):0 < d s:= lt_min zero_lt_one (by unfold C; positivity)
 choose L gF hF using fun s:ℕ=> P.roadSpendStL s i k _ (hD s)
 obtain ⟨δ,gδ,hδ⟩:= ((eventually_all_finset (Iic (Τ k))).mpr fun j hj=>P.payMeterStepsSt i k j (mem_Iic.mp hj) _ (gF j)).and self_mem_nhdsWithin |>.exists
 refine ⟨min δ (θ/2), lt_min (show 0<δ from hδ) (half_pos z), fun ε v hp t r s hm W U S b A h=>?_⟩
 let D:= cloudSpan s S*b; have hd:0 ≤ D:= mul_nonneg (cloudSpan_pos ..) h.priced
 let X' := breathing Y B s i k A; let Y' := P.roadScriptSt i k s r A
 have hs:T≥ Tapestry.ticketTape Y i k s:=P.totalMono i k U
 let Z₁:= savings Y s i k
 have hb: ‖Y'-X'‖≤ d s*D:=by unfold D; rw [←mul_assoc]; exact hF s r (gδ s (mem_Iic.mpr U) ε v (hp.2.le.trans (min_le_left ..)) hp.1.le t r W) S b A h
 have hv:‖Y'‖≤ (1+T)*D:=by
    have he:‖Y'‖ ≤ ‖Y'-X'‖+‖X'‖:=(by nth_rw 1 [←sub_add_cancel Y' X']; exact norm_add_le ..)
    rw [add_mul]; refine he.trans (add_le_add (hb.trans (mul_le_mul_of_nonneg_right (min_le_left ..) hd)) (le_trans ?_ (mul_le_mul_of_nonneg_right hs hd))); rw [show D=cloudSpan s S*b from rfl, ←mul_assoc]; exact P.cardBoundSt S s b A h i k
 have he : ‖P.canyonPriceSt i k s r A - Z₁ Y'‖ ≤ θ/2*D:=by
      rw [show Z₁ Y'= Journey.compass Y i k s (attire Y') from trueSavings _ _ _ _ _ ⟨hm,U⟩]
      refine (apply_stable (Γ).U _ ((P.run.voyage i).ownership s).paid.bill _ _ (Env.integrableX (W.trueMark.2.2.2.2 s U).2.1 _) (Marks.can_read (Γ).V _ _ _ ((Y).each_level i k s hm U)) (attire Y') (Tapestry.Ward.signs Y').env ((1+T)*D) (fun x=> (Ward.pay Y' x).trans hv) _ (W.owes s U).1).trans ?_
      let U:= ε (Τ k); change (1+T)*D*(U/(1+T))≤ θ/2*D; refine le_trans (b:=U*D) (Eq.le ?_) (mul_le_mul_of_nonneg_right (hp.2.le.trans (min_le_right ..)) hd); field_simp
 have hc:C s*d s≤θ/2:=by let e:=min_le_right 1 ((θ/2)/(1+C s)); have z0:d s*(1+C s)≤ θ/2:=(le_div_iff₀ (by unfold C; positivity)).1 e; linarith [hD s]
 rw [breathing_fin Y B s i k A ⟨hm,U⟩ h.funded]; refine (norm_sub_le_norm_sub_add_norm_sub _ (Z₁ Y') _).trans ?_
 let x:=P.canyonPriceSt i k s r A

 change ‖x-Z₁ Y'‖+‖Z₁ Y'-Z₁ X'‖≤ θ*D
 have ht':‖Z₁ Y'-Z₁ X'‖ ≤ θ/2*D:=by
    rw [←map_sub]; refine ((Z₁.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (hV s))).trans ?_; change C s*(d s*D)≤_; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hc hd
 linarith

#print axioms primeMeterSt
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
