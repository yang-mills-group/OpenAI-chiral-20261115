import YM.SU5.Same.TemperMeasure
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
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
/-! # Allocate one ballot schedule with geometric growth at small heat
    heights in H.
-/
private abbrev binDial (c:ℕ) (i:ℕ):ℕ:=2^c*(2*i+1)
local notation "Trial" => Axis×List Axis
-- Axis = Fin 4, definitional? using fixed encodable.
noncomputable abbrev indexDial : Trial × ℕ → ℕ := fun x=> binDial (Encodable.encode x.1) x.2
lemma dial_injective : Injective indexDial:=by
 have he(a b:ℕ): padicValNat 2 (binDial a b)=a:=by unfold binDial; rw [padicValNat_base_pow_mul (by norm_num) (by omega),padicValNat.eq_zero_of_not_dvd (by omega),zero_add]
 rintro ⟨a,b⟩ ⟨c,d⟩ q
 unfold indexDial at q; change binDial (Encodable.encode a) b=binDial (Encodable.encode c) d at q
 have hx : c=a:= Encodable.encode_injective (by rw [← he (Encodable.encode a) b,← he (Encodable.encode c) d,q]); subst c
 have hb:= Nat.eq_of_mul_eq_mul_left (show 0<2^Encodable.encode a by positivity) q -- implicit matches abbrev?
 exact congrArg _ (show b=d by omega) -- Prod.mk a

local notation "χ"=> P.pillars 3
variable {A C b:ℝ}
variable {l:List Axis} {k':ℕ}
variable (x:P.Spectrum0 3)
private lemma price_beat (V:ForecastCard P f r j l (P.macroStep k')) (A:ℝ)(n:ℕ)(h:(V.stage)=k'+k') : P.cardPrice j x V A n = 2*(4*zoomC P.par.R.L^(k'+k'+1-r))*(‖P.sillView j f (k'+k') l x‖+navy n * P.lensForm A (k'+k')/zoomM P.par.R.L):=by
 let u(s:ℕ) := 2*(4*zoomC P.par.R.L^(s+1-r))*(‖P.sillView j f s l x‖+navy n * P.lensForm A s/zoomM P.par.R.L^(s+1-s))
 change u V.stage=_
 refine (congrArg u h).trans (by unfold u; rw [show k'+k'+1-(k'+k')=1 from by omega, pow_one])

abbrev AtGlassRate (P:Spine)(x:P.Spectrum0 3)(j:Axis) (f r:ℕ) (l:List Axis) (v:ℕ→ℕ) (a:ℕ→(ℕ×ℕ)→ℝ): Prop:=
      ∃ M≥(0:ℝ), ∃ K≥ (1:ℝ), ∀ᶠ k:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ‖((a i (f,r):ℝ):ℂ) • P.beamWatch j x f (v i) l (P.macroStep k)‖ ≤ M*K^k

structure SettledBallot (P:Spine)(f r:ℕ) (d:ℕ→Pedal P f) where
 table:∀ (p: Trial × ℕ), ForecastCard P f r p.1.1 p.1.2 (P.macroStep p.2)
 index:∀ (p: Trial × ℕ), d (indexDial p)= P.pedal_ξ p.1.1 (table p)
 late:∀ (B:Trial), ∀ᶠ k:ℕ in atTop,(table (B,k)).stage=k+k

lemma later_table (f r:ℕ) : ∃ Rv:ℕ→Pedal P f, Nonempty (SettledBallot P f r Rv):=by
 choose D h using fun t : Trial => P.table_at t.1 f r t.2
 let u(p: Trial × ℕ):=P.pedal_ξ p.1.1 (D p.1 p.2)
 let Z' : ℕ→Pedal P f:= extend indexDial u (fun _ :ℕ=> u ((3,([]:List Axis)),0))
 refine ⟨Z',⟨fun p=>D p.1 p.2,fun p=>dial_injective.extend_apply _ _ _, h⟩⟩

lemma price_at_glass (A:ℝ) (u:P.FullSills x) (B:Trial) {d:ℕ→Pedal P f}(Q₁:SettledBallot P f r d) :
   ∃ M≥(0:ℝ), ∃ K≥ (1:ℝ), ∀ᶠ k:ℕ in atTop, P.cardPrice B.1 x (Q₁.table (B,k)) A (indexDial (B,k))≤ M*K^k:= by
 let Z:= zoomC P.par.R.L; let a:= Encodable.encode B; let c:= (2:ℕ)^a; let H':= lensValue A; let W₁:= zoomM P.par.R.L
 let Y:ℝ:= ((2:ℝ)^(c+1)*H')/W₁
 have hz:1 ≤ Z:=zoomC_p _; have hz':0< Z:=zero_lt_one.trans_le hz
 have hw:0< W₁:=zoomM_p _; have hp:0 < H':=lensBasis A; have hy:0 < Y:=by unfold Y; positivity
 let z:ℝ:= (2:ℝ)^(c*2); have ht:1 ≤ z:=one_le_pow₀ (by norm_num)
 let k₀:=max z ((2:ℝ)*2)
 have hk:1 ≤ k₀:= ht.trans (le_max_left ..)
 let M:= 2*(4*Z)*(1+Y); let k₁:= Z*Z*k₀; have hM:0≤M:=by unfold M; positivity
 have hk₁:1≤ k₁:= one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hz hz) hk
 refine ⟨M,hM,k₁,hk₁,?_⟩;
 filter_upwards [Q₁.late B,tendsto_double_page.eventually (u B.1 f B.2),tendsto_double_page.eventually P.slot_le_unit] with k p q t
 let s:=k+k; let K:= Q₁.table (B,k); let n:=indexDial (B,k); let U₁:= P.sillView B.1 f s B.2 x
 have hv:0< navy n:=by unfold navy; positivity
 have hv':0 < slotFee P.par s:= by
    have he': K.stage=s:=p; rw [←he']; exact K.book
 let q₀:= navy n * P.lensForm A s / W₁
 have e: navy n = z^k * (2:ℝ)^(c+1):=by
    unfold navy z; rw [← pow_mul, ← pow_add]; exact congrArg (fun n:ℕ=> (2:ℝ)^n) (show n+1=c*2*k+(c+1) by unfold n; change c*(2*k+1)+1=c*2*k+(c+1); ring)
 have he: 0 ≤ q₀:= (div_pos (mul_pos hv (mul_pos hp hv')) hw).le
 have hg(s'₀:ℝ)(hs₀:0 ≤ s'₀)(v':s'₀ ≤ k₀): s'₀^k≤ k₀^k:= pow_le_pow_left₀ hs₀ v' _
 have hb: q₀ ≤ k₀^k * Y:=by
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (hg z (zero_le_one.trans ht) (le_max_left ..)) hy.le)
    unfold q₀ Y; rw [← mul_div_assoc,← mul_assoc (z^k),e]; apply div_le_div_of_nonneg_right _ hw.le; exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hp.le (show slotFee P.par _ ≤ 1 from t)) (by rw [← e]; exact hv.le)
 have hU: ‖U₁‖ ≤ k₀^k:=by
    have hh: ‖U₁‖ ≤ ((2:ℝ)*2)^k:= (show ‖U₁‖≤2^s from q).trans_eq (by unfold s; rw [pow_add,mul_pow])
    exact hh.trans (hg ((2:ℝ)*2) (by positivity) (le_max_right ..))
 change P.cardPrice B.1 x K A n≤_
 rw [P.price_beat _ _ _ _ _ (show K.stage=k+k from p)]; change 2*(4*Z^(s+1-r))*(‖U₁‖+q₀)≤ M * k₁^k
 calc 2*(4*Z^(s+1-r))*(‖U₁‖+q₀) ≤ 2*(4*Z^(s+1))*(k₀^k+k₀^k*Y):=by
          refine mul_le_mul ?_ (add_le_add hU hb) (add_nonneg (norm_nonneg _) he) (by positivity); gcongr; omega
      _= M * k₁^k:=by unfold M k₁ s; rw [pow_add,pow_add,mul_pow,mul_pow]; ring
variable {P}
lemma AtMile.earnBeat {a:ℕ→(ℕ×ℕ)→ℝ}{v:ℕ→ℕ}{d:ℕ→Pedal P f}{x:P.Spectrum0 3}(Y:AtMile P A C f r x b v a d) (F:SettledBallot P f r d)(B:Trial)(p:f < r)(q: Odd P.par.R.L.val)(k:ℕ) : ∀ᶠ i:ℕ in atTop, ‖((a i (f,r):ℝ):ℂ) • P.beamWatch B.1 x f (v i) B.2 (P.macroStep k)‖≤ P.cardPrice B.1 x (F.table (B,k)) A (indexDial (B,k)):=by
 filter_upwards [Y.extra (indexDial (B,k)), Y.fast.tendsto_atTop.eventually (P.account_due B.1 x (F.table (B,k)) p q (indexDial (B,k)) A C)] with i t u₁
 rw [F.index] at t; obtain ⟨c,w,l⟩:= Y.cruise i; exact u₁ _ l t
lemma AtMile.scoutAlso {a:ℕ→(ℕ×ℕ)→ℝ}{v:ℕ→ℕ}{d:ℕ→Pedal P f}{x:P.Spectrum0 3}(Y:AtMile P A C f r x b v a d)(F:SettledBallot P f r d)(p:f < r)(q:Odd P.par.R.L.val) : ScoutAnthem P x A C f r b v a:=by -- idem `SatinThinCentury.*`
 refine ⟨⟨d,Y⟩,?_⟩; intro j l e h; obtain ⟨k,u₁⟩:= (P.macroStep_zero.eventually (gt_mem_nhds h)).exists
 let H':=P.macroStep k; have hu:H'<e:=u₁
 let B:Trial:=(j,l);
 have ht:Tendsto (fun s=> (P.roomy:ℝ)*P.macroStep s) atTop (𝓝 0):=by simpa only [mul_zero] using (P.macroStep_zero.const_mul (P.roomy:ℝ))
 refine ⟨P.cardPrice B.1 x (F.table (B,k)) A (indexDial (B,k)),?_⟩
 filter_upwards [Y.fast.tendsto_atTop.eventually (ht.eventually (gt_mem_nhds (P.macroStep_pos k))), Y.earnBeat F B p q k] with i t u
 have hp:(P.roomy:ℝ)*P.macroStep (v i)<H':=t
 have hh: ‖((a i (f,r):ℝ):ℂ) • P.beamWatch j x f (v i) l H'‖≤_:=u -- precision
 refine ⟨hp.trans hu, le_trans ?_ hh⟩; rw [norm_smul,norm_smul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact P.beam_right_le j x _ (by rw [Apron.pivot_w,P.play_width]; exact hp.le) hu.le

variable (P)
variable (G₀:P.NightCop)(Book:P.repeatBill (twiceT (P.baseRoot f) 3) f)(F₀:f<r)(P0:∀ v:ℕ,r ≤ v→∃ c a w, Workforce A C f v P c a w)(Q0:(∫ x,P.lantern x f r ∂(P.pillars 3))≤ (min7 /4)/4)(u:P.reached f r)
  (S:0< slotFee P.par f)(D:0<P.rewardK f r)
  (Z0:2*lensValue A * (P.rewardK f r * slotFee P.par f /zoomM P.par.R.L^(r-f)) ≤ b/16)
variable (Ξ:∀ᶠ s:ℕ in atTop, ∀ᶠ i:ℕ in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k→ Yoke.ShelterCost C P.run s i k)
include G₀ Book F₀ P0 Q0 u S D Z0 Ξ
-- the *same character*, in both bills. keep the later coupons e.g. AtMile
lemma third_winter (D₀: P.Spectrum0 3→Prop)(p0:∀ᵐ x∂χ,D₀ x)(p:Odd P.par.R.L.val) :
    ∃ x: P.Spectrum0 3,D₀ x ∧ P.FullSills x ∧ ∃ (v:ℕ→ℕ)(a:ℕ→ (ℕ×ℕ)→ℝ), ScoutAnthem P x A C f r b v a ∧ ∀ j l, AtGlassRate P x j f r l v a :=by
 obtain ⟨Rv,⟨hr⟩⟩:= P.later_table f r
 obtain ⟨x,⟨q,h⟩,v,a,Y'⟩:= P.appearance G₀ Book F₀ P0 Q0 u S D Z0 Rv (fun u=> D₀ u∧P.FullSills u) (p0.and (P.ae_full_sills Ξ))
 refine ⟨x,q,h,v,a,Y'.scoutAlso hr F₀ p,fun j l=>?_⟩
 let t:Trial:= (j,l); obtain ⟨M,hM,K,hK,n⟩:= P.price_at_glass x A h t hr -- order? price_at_glass signature variable x prior A
 exact ⟨M,hM,K,hK,n.mono fun k u=> (Y'.earnBeat hr t F₀ p k).mono fun i w=> w.trans u⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.third_winter
