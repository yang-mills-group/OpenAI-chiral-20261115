import YM.SU5.FiniteGaugeData.SalonG.Coal
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
namespace SalonG
open Nacre Heat Charm Chrono Journey
variable (K:Calibration) (a:Axis)(d n:ℕ)
-- choose train length rather than using powers-only.Board. pass through supports ANY.
abbrev stint (d:ℕ)(N:Side):= N.val / (2*yard K d)
lemma stints (m:Side)(t:0<d): PaidSpan K m d (stint K d (K.c m)):= by
 have hz:0<2*yard K d:= Nat.mul_pos two_pos (Nat.mul_pos (tic_pos K) t); have hv:= Nat.div_add_mod (K.c m).val (2*yard K d); have ht:= Nat.mod_lt (K.c m).val hz; unfold stint; constructor<;>unfold proceed<;> rw [← mul_assoc] <;> omega
abbrev stops:= stint (tent Y h) d (side Y i s)
lemma stops_p (p:0<d): PaidSpan (tent Y h) (momentm Y i s) d (stops Y h s i d):=by rw [stops, ← show (tent Y h).c (momentm Y i s)=side Y i s from terrain ..]; exact stints Kₜ d _ p
include h in
lemma c_rises:Tendsto (fun i=>(side Y i s).val) atTop atTop:=by -- include h
 have he(i:ℕ):(tent Y h).c (momentm Y i s)= side Y i s:= terrain Y h (Y.ir i) s
 exact Tendsto.congr (fun i=>congrArg Subtype.val (he i)) ((c_grows Kₜ).comp (momentum Y s))
lemma stops_grow (p:0<d): Tendsto (fun i=>stops Y h s i d) atTop atTop:= tendsto_atTop.2 fun r=> ((c_rises Y h s).eventually_ge_atTop (r*(2*yard Kₜ d))).mono fun i t=> (Nat.le_div_iff_mul_le (Nat.mul_pos two_pos (Nat.mul_pos (tic_pos Kₜ) p))).mpr t

variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (x:W (tent Y h))(t:Locator (tent Y h) x T)(r:Ahead a 0 (reserve Λ l) T) (f:W (tent Y h))
variable (B₁ B₂ ε:ℝ)
abbrev Credential (z:W (tent Y h)):= ‖sharp Y h s i k (CarrierF a d (stops Y h s i d) z).val‖ ≤ B₁
-- binds all setups.When k paid. `s,n,k,i` names. CashWidth choose large n upper Ct from Stamp.
include W'
local notation "D"=> duration T
local notation "d'"=> energyS Λ d n
local notation "μ₁" i:max=> momentm Y i s
local notation "ν₁" i:max=> momentm Y i (s+n)
lemma coal_point (p:0<ε) : ∀ᶠ j in atTop,∀ k,legacy Y (u j) (v k)→ ‖hot Y h s (u j) (v k) x.val-E s x.val‖ ≤ ε := by
 have hb(w:ℕ→ℕ)(q:eligiblePath Y u v w): Tendsto (fun i=>hot Y h s (u i) (v (w i)) x.val) atTop (𝓝 (E s x.val)):=by rw [← mood_eq Y h s W' x.val (well_for Kₜ x).1]; exact (W'.pick.booked Y h s (well_for Kₜ x).1).1.paths w q
 exact (path_budget (z:=E s x.val) (v:=u) (A:=fun i k=>hot Y h s i k x.val) Y W'.pick.grow_k hb ε p).mono fun i q k v=>(q k v).le.trans_eq' (dist_eq_norm _ (_:ℂ)) -- tune
lemma often_paid (p:0≤ B₂) :∀ᶠ k' in atTop,Ferry Y s i (v k') ∧ ∀ f:W (tent Y h), RealWidth (tent Y h) f (momentm Y i s) B₂ → ‖sharp Y h s i (v k') f.val- hot Y h s i (v k') f.val‖ ≤ 1:=by
 let z:=B₂+1; have he:0<z:=by unfold z; linarith
 filter_upwards [W'.pick.grow_k.tendsto_atTop.eventually (gluedM Y h ∅ s (1/z) (by positivity)), W'.pick.pass Y h s i] with k' t v
 refine ⟨v,fun x u=> ((t i v).1 x).trans (le_trans (mul_le_mul_of_nonneg_left (?_ : _ ≤ z) (by positivity)) (le_of_eq (div_mul_cancel₀ _ he.ne')))⟩
 exact u.cashW.trans (by unfold z; linarith)
lemma loadSmall (g:0<d) : ∀ᶠ i in atTop, ∀ᶠ k in atTop, ∀ (f:W (tent Y h)) (t:Locator (tent Y h) f S), (RealWidth Kₜ f (momentm Y (u i) s) (drift Kₜ S d (duetCharge Y s))) → Credential Y h s (u i) (v k) a d 2 f := by
 let V:= drift Kₜ S d (duetCharge Y s); have hb:0≤V:= (Real.exp_pos _).le
 filter_upwards [(W'.pick.grow_i.tendsto_atTop.eventually ((stops_grow Y h s d g).eventually_gt_atTop 0)), ((momentum Y s).comp W'.pick.grow_i.tendsto_atTop|> Tendsto.comp (c_grows Kₜ)).eventually_ge_atTop (booth Kₜ S)] with i t p
 let y:=stops Y h s (u i) d; filter_upwards [often_paid Y h s (u i) W' (V^(4*y)) (pow_nonneg hb _)] with k v f u v' -- u i now shadow
 obtain ⟨p',hv⟩:=v; let r:= CarrierF a d y f
 have he := hv r (diligent Kₜ _ a d y f V v'); have ht:= (Equity.record Y h s _ _ p').chariot a d y f u (stops_p Y h s _ d g) (by omega) p v'; unfold Credential; have hq := (norm_sub_norm_le _ _).trans he; exact (sub_le_iff_le_add.mp hq).trans ((add_le_add le_rfl (show ‖hot Y h s _ _ r.val‖≤1 from ht)).trans_eq (by ring)) -- syntax y≠0

variable (g:0<d)(v':Studio a 0 (yard (tent Y h) d) (reserve Λ l) S)
local notation "β"=> duration (seriesQ Λ l S n)*(bridgesK Y h S s n*B₂)
local notation "D₁'"=> duetCharge Y (s+n)
local notation "π" x:max=> Passenger Y h S s (u x)
local notation "Ω" j:max=> TellerC j Kₜ (duetCharge Y (s+n))
-- Tilted astronomy cores
abbrev upperHours :ℝ:= (B₁+1)*(TellerC (Ran Kₜ (d:=energyS Λ d n) (T:=T)) Kₜ (duetCharge Y (s+n))* (((duration T * ‖reading Kₜ T x t‖)^2)^2))+1 -- note d binder order
abbrev EchoF (d n:ℕ)(x f:W (tent Y h)):= Fold Kₜ a 0 (openQ Kₜ a d n f x) (openQ Kₜ a d n f x)
include W' t v' g r
lemma uniformPhase (i0:ℕ)(C:∀ᶠ k in atTop,projectR Y S s i0 (v k) n)(p: endurance Kₜ (Ran Kₜ (d:=energyS Λ d n) (T:=T)) ≤ ((tent Y h).c (momentm Y i0 (s+n))).val)(b:0 ≤ B₂) :∀ᶠ k' in atTop,
    Ferry Y (s+n) i0 (v k') ∧ ∀ (f:W Kₜ) (e:Locator (tent Y h) f S), ‖reading Kₜ S f e‖≤ B₂ → Credential Y h s i0 (v k') a d B₁ f→
    let v':= v k'; let j:= Passenger Y h S s i0 v' n f e
    (stops Y h s i0 d :ℝ) * ((hot Y h (s+n) i0 v' (EchoF Y h a (energyS Λ d n) 1 x j).val).re - (hot Y h (s+n) i0 v' (EchoF Y h a (energyS Λ d n) 0 x j).val).re) ≤ upperHours Y h T s d n x t B₁ := by
 let z:=stops Y h s i0 d; have hx:= stops_p Y h s i0 d g; have ht:= season Y h s i0 d n z hx
 have hw': 0 ≤ β:= mul_nonneg (duration_pos _).le (mul_nonneg (bridgesK_nn ..) b)
 let hT:= (width_read t); let u:= D*‖reading Kₜ T x t‖
 filter_upwards [C,often_paid Y h (s+n) i0 W' ((β)^(4*z)) (pow_nonneg hw' _)] with k' F hv; refine ⟨hv.1,fun f e z' H=>?_⟩; intro v'' j; have hp:= ledgerL Y h S s i0 v'' d n z a f e hx v' F -- v' proof still
 have h':= hv.2 (CarrierF a d' z j) (diligent Kₜ (ν₁ i0) a d' z j (β) (passenger_width Y h S s i0 v'' n f e z' (momentm Y i0 (s+n)))) -- width ∀ v; ok
 let Q:= Equity.record Y h (s+n) i0 v'' hv.1; let E':= TellerC (Ran Kₜ (d:=d') (T:=T)) Kₜ D₁'
 have he:‖(heatX Y h (s+n) i0 v'' hv.1) (CarrierF a d' z j)‖ ≤ B₁+1:= by
    rw [norm_sub_rev] at h'
    have h:=(norm_sub_norm_le _ _).trans h'; exact ((sub_le_iff_le_add).mp h).trans (by rw [←hp]; exact (add_le_add le_rfl (show _≤ B₁ from H)).trans_eq (add_comm ..)) -- tune
 have hl:= Q.travel a d' z T x j r (ride_loc ..) t (series_geo Y h S d n a v') ht p (hT (momentm Y i0 (s+n))) he
 unfold upperHours; rw [sq,sq] -- both? powers rewrites first outer gives repetition then inner `rw` only first? rw all occ maybe
 exact hl
#print axioms uniformPhase
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
