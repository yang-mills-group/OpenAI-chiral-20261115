import SatinThinCentury
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
variable (x : P.Spectrum0 3)
open Regis.Circuit SatinJets
local notation "Φ"=> P.Spectrum0 3
local notation "χ"=> P.pillars 3

/-!
# Comparing coefficients across polarization & cutoff choices

An ingredient for thermal polynomial pricing. Lender coefficients at the
*same* three heights must agree up to a narrow window, no matter which
path subsequences were used. To see this we compare normalized vectors
in one auxiliary representation where all errors can be taken small
simultaneously and the main term certified nonzero by the rank test.
-/

lemma reliable_forces_lower {d:ℝ}(hd:P.reliableP x f r d) :
    d < ‖P.invoiceV x f r r 1‖ := by
  by_contra! he
  exact (hd 0 (by rwa [dist_zero_left])).ne_zero (i:=0) (map_zero _)

private lemma pickThree (g h k:Φ → ℝ) (u:Continuous g)(v:Continuous h)
    (w:Continuous k) (a:0≤g)(b:0≤h)(c:0≤k)(d:(∫ x, g x ∂χ) ≤ 1/4)
    (e:(∫ x, h x ∂χ) ≤ 1/4) (p:(∫ x, k x ∂χ) ≤ 1/4) :
    ∃ x : Φ, g x ≤ 1 ∧ h x ≤ 1 ∧ k x ≤ 1 := by
  have U(t:Φ → ℝ)(l:Continuous t):Integrable t χ :=
    l.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  suffices A: ∃ x : Φ, g x+h x+k x < 1 by
    obtain ⟨x,hx⟩:=A
    exact ⟨x,by have s:0≤g x:=a x; have t:0≤h x:=b x; have z:0≤k x:=c x; refine ⟨?_,?_,?_⟩<;>linarith only [hx,s,t,z]⟩
  by_contra! he
  have q:= integral_mono (integrable_const (1:ℝ)) (U (fun x=>g x+h x+k x) ((u.add v).add w)) he
  rw [integral_const, probReal_univ,one_smul,
      integral_add (f:=fun x=> g x+h x) (g:=k) (U _ (u.add v)) (U _ w),
      integral_add (f:=g) (g:=h) (U _ u) (U _ v)] at q
  linarith only [d,e,p,q]

variable {A C a b β:ℝ}{l l':ℕ→ℕ}{α τ:ℕ→ℝ}
variable (G₀:P.NightCop)(Book:P.repeatBill (twiceT (P.baseRoot f) 3) f)
  (F₀:f<r) (Z: r ≤ v)
  (Q0:(∫ x,P.lantern x f r ∂(P.pillars 3))≤ (min7 /4)/4)(u:P.reached f r)
  (S:0< slotFee P.par f)(D:0<P.rewardK f r)
  (T:0<P.tallWorth r)
  (m:marginD (max7+min7+1) β min7)
  (m₀:0<β)
  (Z0:2*lensValue A * (P.rewardK f r * slotFee P.par f /zoomM P.par.R.L^(r-f)) ≤ β/16)
include R G₀ Book F₀ Z Q0 u S D T m m₀ Z0
lemma lender_tied (L:lender A C f r v α a l P)
    (L':lender A C f r v τ b l' P) :
    |a|≤2*|b|:=by
  let fee := lensValue A*slotFee P.par f
  have h2:0 < fee^2:=pow_pos (mul_pos (lensBasis A) S) _
  let cap := min7/4
  have hp:0 < cap:= div_pos min_positive (by norm_num)
  let root:= P.baseRoot f
  let anchor := P.lent_anchor f
  let price(z:ℝ)(x:Φ):= ‖P.compared_state 3 root anchor Z F₀.le z x‖^2
  let g(x:Φ):= P.lantern x f r/cap
  let k(z:ℝ)(x:Φ):=price z x/(fee^2)
  have hp' : 0≤g:=fun i=>div_nonneg ((show 0≤ P.glareF f r 1 1 0 i from norm_nonneg _).trans (P.lantern_available i f r).1) hp.le
  have hg:(∫ x,g x ∂χ) ≤ 1/4:=by
    unfold g; rw [integral_div]; exact (div_le_iff₀ hp).mpr (Q0.trans_eq (show cap/4=1/4*cap by ring))
  have ht(z:ℝ) : Continuous (k z):= (P.state_cont_cost _ _).div_const _
  have hv(z:ℝ) : 0≤k z:=fun _=>div_nonneg (sq_nonneg _) h2.le
  have h (z:ℝ) (l:ℕ→ℕ)(α:ℕ→ℝ)(t:lender A C f r v α z l P):
      (∫ x,k z x ∂χ) ≤ 1/4:=by
    unfold k price; rw [integral_div]
    exact (div_le_iff₀ h2).mpr (((P.caucus 3 root t anchor Z F₀.le Book G₀).trans (P.officeCost A f)).trans_eq (show fee^2/4=1/4*fee^2 by ring))
  obtain ⟨x,p,q,y⟩:=P.pickThree g (k a) (k b) ((P.lantern_cont ..).div_const _)
      (ht a) (ht b) hp' (hv a) (hv b) hg (h _ _ _ L) (h _ _ _ L')
  have hl:=P.reliable_forces_lower x
      (P.reliable_pp x u T ((div_le_one hp).1 p) ((P.ellisP 3 x R).some) m m₀.le)
  let B:= P.invoiceV x f r r 1
  let I:= fun z:ℝ=> P.invoiceV x f r v (z:ℂ)
  change β < ‖B‖ at hl
  have e(z:ℝ)(n:k z x≤1): |‖I z‖-‖B‖|≤ β/16:=
    (abs_norm_sub_norm_le _ _).trans ((dist_eq_norm (I z) B).symm.trans_le
     ((P.compare_distance x Z F₀.le z (lensValue A) (lensBasis _) D u ((div_le_one h2).1 n) S).trans Z0))
  obtain ⟨_,hU⟩:=abs_le.mp (e a q)
  obtain ⟨hD,_⟩:=abs_le.mp (e b y)
  have hn: ‖I a‖ < 2*‖I b‖ := by linarith only [hl,hU,hD,m₀]
  let y:=P.invoiceV x f r v 1
  have hN(z:ℝ): ‖I z‖=|z| *‖y‖:=by
    unfold I y invoiceV
    rw [one_smul,smul_comm,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  rw [hN,hN,←mul_assoc] at hn
  exact (lt_of_mul_lt_mul_right hn (norm_nonneg y)).le
omit R G₀ Book F₀ Z Q0 u S D T m m₀ Z0
/-- Uniform leverage cap (at fixed large short height, independent of
endpoint). -/
def CloseRates (P:Spine)(A C:ℝ)(f r v:ℕ):Prop:=
  ∀ {l l':ℕ→ℕ} {α τ:ℕ→ℝ}{a b:ℝ},
    lender A C f r v α a l P →
    lender A C f r v τ b l' P → |a|≤2*|b|

include R G₀
lemma close_rates_late (A C:ℝ)
    (Y₀:∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k) :
    ∀ᶠ r in atTop, ∀ v ≥ r,P.CloseRates A C (P.pointEra r) r v:=by
 obtain ⟨b,β',_,t₀⟩:= SatinJets.common_margin (max7+min7+1) min7 min_positive
 let A₀:=2*lensValue A; have h8:Tendsto (fun s:ℕ=>A₀ * P.repeatLoss s) atTop (𝓝 0):=by simpa only [mul_zero] using P.era_complete.const_mul A₀
 let νp:= P.pointEra; let δv:=P.future_payment
 filter_upwards [P.payment_late, P.ready_granule (P.roomy), δv.eventually (P.offers_plans 3 1 zero_lt_one), δv.eventually (P.seat_many 3 1 zero_lt_one), (P.lantern_go Y₀).eventually (ge_mem_nhds (show 0< min7 /4 /4 from (by linarith only [min_positive]))), δv.eventually P.size_honors,P.reward_positive,h8.eventually (ge_mem_nhds (show 0<b/16 by positivity))] with s Hs t δ n G0 w0 W K0 v z l l' α τ a b0
 let f:= νp s; have hp: f < s:= Hs.2.1
 have he:P.reached f s:= t
 have ht:Spine.twiceT (P.baseRoot f) 3 ≤ Yoke.scout P.par 1 f:= by
    have e:twiceT (P.baseRoot f) 3=twiceT (P.plateau f) 3:=by unfold twiceT; simp only [nodeC, Pi.add_apply,Pi.smul_apply]
    rw [e];exact n
 have hx':= δ.1 (P.baseRoot f) ht
 exact P.lender_tied R G₀ hx' hp z G0 he w0.1 (W.2 f) W.1 t₀ β' K0
omit R G₀

/-- Seeing the coefficient on the *whole tail* of the actual volume &
terminal path up to a factor three. -/
lemma fundTail {g:ℕ→ℝ} (L:lender A C f r v α a l P)
  (w:P.CloseRates A C f r v)
  (d:∀ᶠ i in atTop,P.cradle r v (g i) ∧ P.fundsDay (A:=A) L.treasury.price.le L.treasury.step i (g i)):
    ∀ᶠ i in atTop, |a| ≤ 3*|g i| := by
 by_contra hs
 have h1:∃ᶠ i in atTop,3*|g i| < |a|:=by
   exact (Filter.not_eventually.mp hs).mono fun _ h=>lt_of_not_ge h
 obtain ⟨k,t,p⟩:=extraction_of_frequently_atTop h1
 let B:=2*fareMax P.par.R.L (v-r)
 obtain ⟨z,vq,k',t',hz⟩:= (isCompact_Icc (α:=ℝ) (a:=-B) (b:=B)).isSeqCompact.subseq_of_frequently_in (((t.tendsto_atTop.eventually d).mono fun i h=> show (g ∘ k) i∈Set.Icc _ _ from abs_le.mp (show P.cradle r v _ from h.1).1).frequently)
 have he:Tendsto (g ∘ (k ∘ k')) atTop (𝓝 z):=hz
 have h: P.cradle r v z:= ⟨abs_le.mpr vq, ge_of_tendsto (he.abs.const_mul _) (((t.comp t').tendsto_atTop.eventually d).mono fun _ h=>h.1.2)⟩
 have L': lender A C f r v g z (k ∘ k') P:= ⟨L.treasury,h,t.comp t',d,he⟩
 have hp:= w L L'
 have t'':3*|z| ≤ |a| := le_of_tendsto (he.abs.const_mul _) (Eventually.of_forall fun i=>(p (k' i)).le)
 have t1:=h.2
 have ez:|z|=0:= by linarith only [t'',hp,abs_nonneg z]
 rw [ez] at t1; norm_num at t1

lemma tail_rates (L:lender A C f r v α a l P)
    (w:P.CloseRates A C f r v)
    (n:fareMin P.par.R.L (r-f) ≤ 1):
    ∀ᶠ i in atTop, ∃ b z t:ℝ, ReadDensity P.run (P.nomadic i) (P.engine i) A
      L.treasury.price.le L.treasury.step b z t ∧ |a| ≤ 4 * |t*b|:=by
  let goal (i:ℕ)(c:ℝ):Prop:=P.cradle r v c ∧ ∃ b z t:ℝ, |z-1|≤1/4 ∧ 
       ReadDensity P.run (P.nomadic i) (P.engine i) A L.treasury.price.le L.treasury.step b z t ∧
       Premier P.par.R.L (r-f) t ∧ c=z*b
  let c (i:ℕ):ℝ:= if h:∃ c,goal i c then h.choose else 1
  have hv:∀ᶠ i in atTop, goal i (c i):=by
    filter_upwards [L.treasury.room] with i h
    obtain ⟨g,p,z',v,x,l,f',u⟩:= h.1.reading
    have ht: goal i (p*g):= ⟨P.crests_mark x.aims v,g,p,z',v,f',l.breath,rfl⟩
    unfold c; rw [dif_pos ⟨p*g,ht⟩]; apply Exists.choose_spec
  have hk:=P.fundTail (g:=c) L w (hv.mono fun i h=> by
    obtain ⟨e,b,z,t,y,p,x,v⟩:=h
    exact ⟨e,b,z,t,y,p,v⟩)
  filter_upwards [hv,hk] with i h h'
  obtain ⟨_,b,z,t,y,p,x,v⟩:=h
  refine ⟨b,z,t,p,h'.trans ?_⟩
  have hb: 3*|z| ≤ 4*|t|:=by
    have ht:1 ≤ |t|:=by
      have e:0< |t|:=abs_pos.mpr x.nz
      have hq:= (abs_inv _).symm.trans_le (x.small.trans n)
      rw [inv_le_one₀ e] at hq; exact hq
    have hy:= abs_le.mp y
    rw [abs_of_nonneg (show 0≤ z by linarith)]
    linarith
  rw [v,abs_mul,abs_mul, ←mul_assoc,←mul_assoc]
  exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
