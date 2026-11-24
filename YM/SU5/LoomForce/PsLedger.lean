import YM.SU5.LoomForce.Oz
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
namespace LoomForce
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP
     Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
     InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Papal Lamour.Bridge Celeste Exterior SpinReceipt Yoke Jewel EmberWind Hiro Onyx
open Regis.Head Regis.Head.Brecht Regis.Circuit
open YM.Stationary (Gaia)

variable (P : Spine) {s i k n : ℕ}
local notation "Λ" => P.par
local notation "Γ" => P.run
namespace Sundial
open LitCurrent LitCurrent.Surplus
open Pressure Worth Worth.Pays BProof
open Next.Rank.Spindle
-- physical-in-microscope timelike here. choose x at 0 (wrapped to every n).
local notation "Ξ"=>takenVolume P
local notation "Υ"=>takenCutoff P
open ProbabilityTheory MeasureTheory
variable {φ : ℕ→ℕ}{β : ℕ→ℝ}(C:Pooling P.run (takenVolume P) (takenCutoff P) φ β)
variable (A:ℝ)(u:0<A)
local notation "X" s:max=> hat (Λ).R.L (Λ).x s
local notation "U" s:max => sPow Λ s A
local notation "Pp" s:max => radiusB (X s)
local notation "Γσ" s:max=> Sheds (Pp s)

open Swell Finger Vow Next.Rank CF.Pannier.Chancel Rous Scree
open Sault Rill
open Yoke WakeInvestment -- scope
open _root_.Zephyr.Chern
local notation "L" s:max n:max=> RootBook P.run (takenVolume P n) (takenCutoff P n) s
local notation "ψ" s:max n:max=> (P.run.voyage (takenVolume P n)).CapeT s
local notation "Nt" s:max n:max=> matterSide P s n
local notation "Pw" s:max n:max=> (L s n).p
local notation "R_" s:max=> -(shadowR P A s) -- negative
local notation "G_" s:max=>shadowR P A s
variable {Y₀ K:ℝ} (V:P.Register){Mc:ℕ}(J:PreparedInvestment P V Y₀ Mc)
private lemma loseLe (J:ℝ):Tendsto (fun s=>sPow Λ s J*WakeInvestment.chip (hat P.par.R.L P.par.x s) (-3)) atTop (𝓝 0):= (Pays.limit (times (whole 0 J 0) (whole (-3/400000) 0 0)) (Or.inl (by norm_num))).comp (turnover Λ)
private lemma loss_cont (ε:ℝ)(p: 0 < ε) (D:ℝ):∃ v> (0:ℝ),D^2*(2*(2*unitReceipt*v+v^2))≤ ε/2:=by
 have he:Tendsto (fun z:ℝ=> D^2*(2*(2*unitReceipt*z+z^2))) (𝓝[>]0) (𝓝 0):=by
    let X_:=fun z:ℝ=> D^2*(2*(2*unitReceipt*z+z^2)); simpa only [ContinuousWithinAt,X_,mul_zero,zero_pow (by decide:(2:ℕ)≠0),add_zero] using ((show Continuous X_ from by unfold X_;fun_prop).continuousAt (x:=0)).continuousWithinAt (s:=Set.Ioi 0)
 exact ((show ∀ᶠ x in 𝓝[>](0:ℝ), 0<x from self_mem_nhdsWithin).and (he.eventually (ge_mem_nhds (half_pos p)))).exists
private lemma struck (d e:ℂ)(f f' g g':ℂ)(A B:ℝ)(hd:‖d-e‖≤ B)(hf:‖f-f'‖≤ B)(hg:‖g-g'‖≤ B)(hp:‖f'‖≤ A)(hq:‖g'‖ ≤ A) :
  ‖(d-f*g)-(e-f'*g')‖≤ B+ (2*A*B + B^2):=by
 rw [sub_sub_sub_comm]; have hu:0≤ A:=(norm_nonneg _).trans hp; have hv:0≤ B:=(norm_nonneg _).trans hd; have hl:‖f‖≤ B+A:=by have hl:=norm_add_le (f-f') f'; rw [sub_add_cancel] at hl; exact hl.trans (add_le_add hf hp)
 apply (norm_sub_le ..).trans; apply add_le_add hd
 rw [show f*g-f'*g'= f*(g-g')+(f-f')*g' by ring]; refine (norm_add_le ..).trans ?_; rw [norm_mul,norm_mul]; exact (add_le_add (mul_le_mul hl hg (norm_nonneg _) (add_nonneg hv hu)) (mul_le_mul hf hq (norm_nonneg _) hv)).trans_eq (by ring)

variable (s:ℕ)
abbrev LeafOne (s n r:ℕ)(a v:ℝ):= P.StampMark r s (takenVolume P n) (takenCutoff P n) a v
local notation "E₀" s:max n:max x:max=> compass P.run (takenVolume P n) (takenCutoff P n) s x
abbrev feeReal (β:ℕ→ℝ)(A:ℝ){s n r:ℕ}{a v:ℝ} (E:LeafOne P s n r a v):ℂ := let Z:= stageFace P s E A β; let f:= compass P.run (takenVolume P n) (takenCutoff P n) s; f (Z true * Z false)-f (Z true)*f (Z false)
local notation "Φ_" s:max n:max=> readingFob (Pp s) (R_ s) (0:Site (matterSide P s n))
local notation "χT" s:max=> WakeInvestment.chip (hat P.par.R.L P.par.x s) (-3)
-- open notations actual supports
#print axioms loseLe

-- may want to lift across n eventually to P.E: cost order fixed by P and all other parameters.s after Owneed. Not crossing heights simultaneously.
local notation "μ_" s:max n:max=> (RootBook P.run (takenVolume P n) (takenCutoff P n) s).p.B/10
open Clock Clock.Hookah Gleam Gleam.Wake
include J u C
lemma purchased (a b c v ε:ℝ)(ha:0<a)(hv:0≤v)(he:0<ε) (r:ℕ) (hc:0 ≤ c) : ∃ I> (0:ℝ), ∀ᶠ s:ℕ in atTop, ∀ᶠ n:ℕ in atTop, let n':=φ n; let N:=matterSide P s n';
    Ferry Γ s (Ξ n') (Υ n') ∧ s<P.run.uv (takenCutoff P n') ∧ SlabMark.Between P.calibration 3 (-(shadowR P A s)) (shadowR P A s) (litRegion P s) ∧ ∃ h:2*(radiusB (hat P.par.R.L P.par.x s)+1)<(More N).val,
    ∀ (E:LeafOne P s n' r a v), MaskPoint P.run r s (takenVolume P n') (takenCutoff P n') a b→ let B:= radiusB (hat P.par.R.L P.par.x s);
      let G:= κFix β s; let M:= stageFace P s E A β; let U':=sPow P.par s A ^4; let k:= (Pw s n').B/10
      let D:=polynomialPad (radiusB (hat P.par.R.L P.par.x s)) h (0:Site N) E k U'; let y:= debit P A s
      let V' := landQ N; let r':=node (0:Site N)
      (∀ i,Broom P.run s (Ξ n') (Υ n') (readingFob B (-(shadowR P A s)) (0:Site N)) I (1/2) G (2*y) 0 4 (V' (M i) r' y) (polynomialPad B h (0:Site N) E k U' i)) ∧ Broom P.run s (Ξ n') (Υ n') (Φ_ s n') I (1/2) G (2*y) 0 4 (V' (M true*M false) r' y) (D true*D false) ∧
      AtSupport false ((litRegion P s).image (wrap (More N))) (M false)∧ AtSupport false ((reflectedBox 3 (-(shadowR P A s)) (litRegion P s)).image (wrap (More N))) (M true)∧ M true=reflMark 3 (-(shadowR P A s)) (M false) ∧ (∀ i,covariant (M i)) ∧
      ‖feeReal P β A E-Finger.Ledger (cashY B h 0 E k) (accepted)‖ ≤ ε ∧
      (Stakes (compassLine E 0 (ψ s n') (Pw s n') k) c → incidence c-ε ≤ (feeReal P β A E).re) :=by
 obtain ⟨g,t,k⟩:=cozy 3 P.par.dpos; obtain ⟨T,ht⟩:=tanks_live P.par.dpos; obtain ⟨x,xT⟩:=J.investment
 obtain ⟨W⟩:=charts group; obtain ⟨D₀,i₀,D⟩:=issued_finger a t g v P.par.d ha P.par.dpos k
 let L₀:= occupancy a v g
 have h0: 0≤ L₀:=by
   unfold L₀ occupancy Jet.composeCost; have hp:= k.peta.le
   have hf:0 ≤ expiry (4*a) v:= mul_nonneg (tsum_nonneg (fun _=> by have ht : 16 ≤ Tenant.quota:= Tenant.quota_bound; have h0:0≤ Tenant.quota:= le_trans (by norm_num) ht; positivity)) hv
   positivity
 obtain ⟨I,tI,hI⟩:= ((eventually_gt_atTop (0:ℝ)).and (rallies Λ L₀ T W (A+1) A D₀ h0 ht.size)).exists
 let a₀:ℝ:=1/2; obtain ⟨u',y₀,z₀⟩:= loss_cont ε he D₀
 refine ⟨I,tI,?_⟩
 let L'(s:ℕ):= χT s; let b₁(s:ℕ):= L' s+ (2*sPow Λ s (upperPay I) * L' s + L' s ^ 2)
 have he₁:Tendsto L' atTop (𝓝 0):= (limit (whole (-3/400000) 0 0) (Or.inl (by norm_num))).comp (turnover Λ); have he₂:Tendsto b₁ atTop (𝓝 0):=by
    have he:= he₁.add (((loseLe P (upperPay I)).const_mul 2).add (he₁.pow 2))
    simpa only [b₁,L',mul_assoc,mul_zero,zero_pow (by decide:(2:ℕ)≠0), add_zero] using he
 filter_upwards [hI, (debit_cal P A u),dye_funds Λ 0 4 I tI, Yoke.sails.{0} Γ P.law P.history xT J.dispatch J.rocky.merit 0 4 tI (show 0 < a₀ by unfold a₀; norm_num) (by unfold a₀; norm_num),fare_becomes P C A u u' y₀, he₂.eventually (ge_mem_nhds (show 0<ε/2 from half_pos he))] with s h q d₀ T₀ g₀ b₂
 let B:= Pp s
 filter_upwards [pairedAhead P s φ C.up B,g₀,C.up.tendsto_atTop.eventually T₀] with n u₁ v₁ w₁
 intro n' N; obtain ⟨f,hf,h₂,H⟩:=u₁; refine ⟨f,hf,q.2,H, fun E hp=>?_⟩
 intro B' G M U' w Φ y V' r'
 let K:= Φ_ s n'; let Uq:=Pw s n'; let Pκ:= ψ s n'; have hl:= D B r' (E.A (0:Site N)) (E.moorA _) H w
 have hh: |G| ≤ 2*bornQ Λ s:=paidFix Γ C P.large s; let A':=occupancy a v g
 have hv:= both_assets Γ s (Ξ n') (Υ n') B y (R_ s) 0 hp.C E U' I G (pow_nonneg (BProof.coin_pos .. |>.le) _) H ht W (hp.V1 ▸ h.neck) k hp.B0 rfl (fundsDebit P A s N) h.level hh (h.cap _ q.1) h.panels _ hl (hp.V1 ▸ h.fuel G hh)
 obtain ⟨ar,bs,eq',C'⟩:= futures P A s hp E β; let V₁: Hookah N:= V' (M true*M false) r' y
 have hy: Broom Γ s (Ξ n') (Υ n') K I a₀ G (2*y) 0 4 V₁ (Φ true*Φ false):=hv.2
 refine ⟨hv.1,hy,ar,bs,eq',C',?_⟩
 let Z:= feeReal P β A E; let A₁:= cashY B H 0 E w; let z:= Finger.Ledger A₁ accepted; let E':= Finger.Ledger A₁ (pulseFee P A β s n')
 let Z'(i:Bool):= seatT Γ s (Ξ n') (Υ n') K (Φ i) G; let z':= seatT Γ s (Ξ n') (Υ n') K (Φ true*Φ false) G
 have hZ:z'-Z' true* Z' false= E':= Surplus.valuation Γ s _ _ B (R_ s) (0:Site N) G (U s) H E
 let uκ(t):= w₁.2.2 (2*y) (V' (M t) r' y) G K _ (hv.1 t)
 have ht'(b:Bool): ‖Z' b‖ ≤ sPow Λ s (upperPay I):= (hv.1 b).parts.choose_spec.1.seatCost Γ s (Ξ n') (Υ n') K d₀ hf.le
 have hl₁:‖Z-E'‖≤ ε/2:= hZ ▸ le_trans (struck _ _ _ _ _ _ _ _ (w₁.2.2 _ V₁ G K (Φ true*Φ false) hy) (uκ true) (uκ false) (ht' true) (ht' false)) b₂ -- `..` only at end
 have hv: ‖E'-z‖≤ ε/2:= le_trans (variance_drift A₁ ((charge_lease B H 0 E w).trans hl) u' unitReceipt unit_pos.le y₀.le (fun i j=>by unfold accepted; split; rw [Complex.norm_real,Real.norm_of_nonneg unit_pos.le]; rw [norm_zero]; exact unit_pos.le) v₁) z₀ -- overshadow
             -- adjust
 have hm: ‖Z-z‖≤ ε:= (norm_sub_le_norm_sub_add_norm_sub Z E' z).trans ((add_le_add hl₁ hv).trans_eq (add_halves ..))
 refine ⟨hm,fun y=> sub_le_iff_le_add.mpr ?_⟩
 have hx:= Complex.re_le_norm (z-Z); rw [Complex.sub_re,norm_sub_rev] at hx; apply le_trans (emit H E (by change 4*B+1 < N.val; have hl:4*B+40<N.val:=h₂; omega) hp.C y hc hp.B0.symm); linarith only [hx, hm]
#print axioms purchased
end Sundial
end LoomForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
