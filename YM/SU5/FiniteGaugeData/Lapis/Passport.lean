import YM.SU5.FiniteGaugeData.Lapis.CoatZ
import YM.SU5.FiniteGaugeData.CodaT.Aria
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LapisS
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open YM.SU5.FiniteGaugeData.Lapis Lumi Eight
open Next.Rank Spindle Push.Local Rhythm LightK
namespace Stadium
open Quest.Chaperone Hills Rhythm.Hush LyraBill.Aria
variable {ι:Type}[Fintype ι][DecidableEq ι]{γ b θ α ε:ℝ}{Λ: Preparation}{l:ℕ}
variable (Y:Course Λ (VolumeCape.Dream.Nimbus l))(hY:RadioCity.Hypothesis Λ l γ Y)(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E){P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)
variable (A:∀ i:Axis, Repertory Y h K R i)(T:Duct SU.group ι)(p:Cover)
local notation "Kₜ"=> tent Y h
local notation "V₁" i:max s:max=> side Y i s
local notation "Σ"=>Λ.K.top.clip
local notation "W₁"=> Charm.W (tent Y h)
local notation "𝜁" i:max k:max s:max=> (((Y.voyage i).X (Y.uv k)).gram s).beta
variable {s i k:ℕ}
abbrev amiss (s i k:ℕ)(κ:ℝ) := κ*Real.sqrt (((Y.voyage i).X (Y.uv k)).gram s).beta
abbrev sales (s i k:ℕ)(κ:ℝ):ℝ:= lesson T Λ.V (side Y i s) (Y.uv k - s) κ
lemma sales_bound (s i k:ℕ)(κ:ℝ): |sales Y T s i k κ| ≤ T.h:=by
 unfold sales LightK.lesson Lumi.scaleM divanF; rw [←Real.norm_eq_abs]; apply (norm_integral_le_of_norm_le_const (C:=T.h) ?_).trans_eq (by simp); exact Filter.Eventually.of_forall (fun i=> T.enough _) -- tune
private abbrev optic (T:Duct SU.group ι): Axis→ℕ:= fun _=>2*macroK ι T
local notation "D₀"=> scape p (macroK ι T)
local notation "G"=> capR Kₜ (optic T)
private def capW (n:ℕ)(v:Calibration)(t:ℝ):= capR v (fun _=>2*n) * t -- pins
private lemma capW_ok(v:Calibration)(n:ℕ): (0:ℝ)≤capR v (fun (_:Axis)=>2*n):= Nat.cast_nonneg _
abbrev income(b:ℝ):= b^2+Dig.service (Lumi.prizeL T b)
lemma income_nn (b:ℝ):0≤ income T b:=by unfold income Dig.service Motion.bill; positivity
include K R A hY
lemma legend (t:0<b)(e:0<ε) : ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,∀ (κ:ℝ)(Φ:ℕ→Charm.W (tent Y h)→ₗ[ℂ]ℂ)(z:ℂ)(a:Signed), Sphere Y h K R A Φ→ |κ| ≤2 → ‖z‖≤ b→ let c:=sales Y T s (u i) (v k) κ; let Ψ:=pole T Λ.K.top.clip (amiss Y s (u i) (v k) κ) (tent Y h) p a; ‖1+z*Φ s Ψ‖ ≤ Real.exp (z.re*c+ pulse T b+ capW (macroK ι T) Kₜ (income T b))*(1+ε):=by
 let Ψ:=D₀; let Δ:= income T b; let C:= (capR (tent Y h) (optic T):ℝ); let W:=Real.exp (- (C*Δ)); let Q:=1+b*T.h; let P':=Real.exp (b*T.h)* Q; have hc:0≤C:=capW_ok _ _; have hd:0≤Δ:=income_nn ..; have hy:0≤ b*T.h:=mul_nonneg t.le T.charge; have hP:0≤P':=mul_nonneg (Real.exp_pos _).le (add_nonneg zero_le_one hy)
 have hQ: W*Real.exp (Δ* C)≤1:=by unfold W; rw [←Real.exp_add,show -(C*Δ)+Δ*C=0 from by ring,Real.exp_zero]
 have Hs: ∀ i,∃ z',film z' (optic T i) Ψ i:= by intro i; obtain ⟨a,b⟩:= scape_shape p (macroK ι T) i; exact ⟨a,b⟩
 filter_upwards [LightK.flight T Y hY t.le (pow_pos t 2)] with s hy
 filter_upwards [LapisS.cashC Y h K R A Ψ s (ι:=ι) 3 Hs hP (Real.exp_pos _).le e hd hQ] with i y
 filter_upwards [y,K.pick.pass Y h s (u i)] with k hv hK κ Φ ζ a H p' q c Ξ
 let α:= - (ζ.re*c) - pulse T b - C * Δ; let q':= amiss Y s (u i) (v k) κ; let H₀:= mint T Σ Kₜ p a ζ (r:=q') (α:=α); have hCorr:α≤ b*T.h:=by
    have hl:‖ζ.re‖ ≤ b := (Complex.abs_re_le_norm ζ).trans q; have hc': |c|≤ T.h:=sales_bound ..; have ht : |ζ.re*c|≤ b*T.h:= (abs_mul _ _).le.trans (mul_le_mul hl hc' (abs_nonneg _) t.le); have hp:0≤pulse T b:=div_nonneg (sq_nonneg _) (by norm_num); unfold α; linarith only [mul_nonneg hc hd,hp,abs_le.mp ht |>.1] -- tune
 let F:=plaza T Σ q' Kₜ p a ζ α; have heP(x:Fields (side Y (u i) s)): ‖sold Y h s (u i) F.val x‖≤P':= stand T Σ p a ζ Y h s (u i) _ hCorr q x -- arg
 have he: LapisS.Paper Y s (u i) (v k) T Σ q' ζ.re (α+pulse T b) W Δ:=by
    intro U n x hX; obtain ⟨S',f,tN,y,_,H'⟩:=hX.store; have hw:= hy (u i) (v k) hK.depth hK.enters ζ.re κ _ S' f x ((Complex.abs_re_le_norm ..).trans q) p' y H'; apply hw.trans_eq; unfold W; rw [← Real.exp_nat_mul,←Real.exp_add,tN]; -- bill price.Pages.
    congr 1; change ((n:ℝ)*(ζ.re*c)+Δ*_+n*_) = _; unfold α; change _= n*(- (C*Δ))+_ ; ring -- coercion defeq
 have ht:= hv _ _ _ _ _ F H₀ heP (stake T Σ p a ζ Y h s (u i) q) he Φ H; unfold F plaza at ht; rw [map_smul,map_add,map_smul,H.living,norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le] at ht; change Real.exp α * ‖1+ζ*Φ s Ξ‖≤1+ε at ht
 apply le_of_mul_le_mul_left (ht.trans_eq ?_) (Real.exp_pos α); rw [←mul_assoc,←Real.exp_add]; rw [show α+(ζ.re*c+pulse T b+capW (macroK ι T) Kₜ Δ)= 0 from (by unfold α; change _+ (ζ.re*c+pulse T b+C*Δ)=0; ring),Real.exp_zero,one_mul] -- tune subtraction
omit K R A hY in
private lemma waffle_y : ∀ b:ℝ, capW (macroK ι T) Kₜ (income T b)=capW (macroK ι T) Kₜ (income T 1)* b^2 := by
 intro b; unfold capW; rw [show income T b=income T 1*b^2 from ?_]; ring
 unfold income Dig.service Lumi.prizeL Motion.bill; ring
omit K R A hY in
private lemma underWave(b C:ℝ)(p:0≤C)(d:0<ε):∃ r:ℝ, 0<r ∧ 4*(Real.exp (C*r^2)*(1+r^2)-1)/r≤ε := by
 let f(s:ℝ):= Real.exp (C*s^2)*(1+s^2); have hh:HasDerivAt f 0 0:=by let A:=(hasDerivAt_id' (0:ℝ)).pow 2; simpa [f] using! (A.const_mul C |>.exp).mul (A.const_add 1)
 obtain ⟨r,y,Z⟩:= ((hh.tendsto_slope_zero_right.eventually (ge_mem_nhds (by positivity: 0<ε/4))).and self_mem_nhdsWithin).exists
 have h:0<r:=Z; refine ⟨r,h,?_⟩; change r⁻¹ * (f (0+r)-f 0)≤ _ at y; rw [zero_add, show f 0=1 by simp [f]] at y; change 4*(f r-1)/r≤_; field_simp at y ⊢; linarith
/-- BP21 estimated gauge strength at EVERY high epoch q, uniform in sampling rate θ from [−2,2] × √β and all $Φ$. observation positions in EACH statement `p` are any ONE Cover root, threshold allowed to depend; witness may choose any legal scopes as in WP accounts. -/
theorem survey (e:0<ε) : ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,∀ (κ:ℝ)(Φ:ℕ→Charm.W (tent Y h)→ₗ[ℂ]ℂ)(a:Signed), Sphere Y h K R A Φ →|κ| ≤ 2→‖Φ s (pole T Λ.K.top.clip (amiss Y s (u i) (v k) κ) (tent Y h) p a) - Complex.ofReal (sales Y T s (u i) (v k) κ)‖ ≤ ε:=by
 let C:= pulse T 1+capW (macroK ι T) Kₜ (income T 1); have hc:0≤C:= add_nonneg (by unfold pulse; positivity) (mul_nonneg (capW_ok ..) (income_nn T 1)); obtain ⟨r,y,hr⟩:=underWave 0 C hc e; let Y':= Real.exp (C*r^2)*(1+r^2); let t:=Y'-1
 have hz : 0<r^2:= pow_pos y 2; have hP:0 <t:= sub_pos.mpr (lt_of_lt_of_le (lt_add_of_pos_right _ hz) (le_mul_of_one_le_left (by positivity) (Real.one_le_exp (by positivity:(0:ℝ)≤C*r^2))))
 filter_upwards [legend Y hY h K R A T p y hz] with s p'; filter_upwards [p'] with i p_; filter_upwards [p_] with k hk κ Φ a φ π; let x:= pole T Λ.K.top.clip (amiss Y s (u i) (v k) κ) (tent Y h) p a; let c:= sales Y T s (u i) (v k) κ
 let f:=fun z:ℂ=>1+z * Φ s x; let x':= Φ s x; have h0:f 0=1:=by simp [f]
 have he: HasDerivAt f x' 0:=by simpa only [one_mul] using! (((hasDerivAt_id' (0:ℂ)).mul_const (Φ s x)).const_add 1)
 apply (come h0 (show DifferentiableOn ℂ f (ball 0 r) from (by unfold f; fun_prop)) he hP y ?_).trans hr
 intro z v'; refine (hk κ Φ z a φ π (mem_ball_zero_iff.mp v').le).trans_eq ?_
 change Real.exp (z.re*c+pulse T r+capW (macroK ι T) Kₜ (income T r))*(1+r^2)= _
 rw [waffle_y Y h T]; change _=Real.exp ((z* Complex.ofReal c).re)*_
 have hv: t=Real.exp (C*r^2)*(1+r^2)-1:=rfl
 rw [hv]; change Real.exp (z.re*c+_+_)*(1+r^2)=Real.exp ((z * Complex.ofReal c).re)*_; rw [Complex.mul_re]; simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero, sub_zero]; unfold C; rw [_root_.add_mul (pulse T 1), Real.exp_add, Real.exp_add, Real.exp_add]; unfold pulse; rw [show (1*T.h)^2/2*r^2=(r*T.h)^2/2 from (by ring)]; ring
-- use epoch λ (not phase-dependent). This is an actual lemma on high observability of the hierarchy in Λ.
def boon (Λ:Preparation)(s:ℕ):ℝ:=Real.sqrt (hat Λ.R.L Λ.x s)
abbrev beacon (s:ℕ)(a:Signed):= pole T Λ.K.top.clip (boon Λ s) (tent Y h) p a
def coolant (s i k:ℕ):= (boon Λ s)/Real.sqrt (𝜁 i k s)
abbrev wattle (s i k:ℕ)(a:Signed):= sales Y T s i k (coolant Y s i k) -- no orientation.
-- expose estimates preserved. also $β vs ctx weak credit true
lemma witness (e:0<ε): ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop, (Y.voyage (u i)).kick≤ v k ∧ s≤Y.uv (v k) ∧ |coolant Y s (u i) (v k)| ≤ 2 ∧ (1/2:ℝ) ≤ coolant Y s (u i) (v k) ∧∀ (Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ) (a:Signed), Sphere Y h K R A Φ→ ‖Φ s (beacon Y h T p s a)- (wattle Y T s (u i) (v k) a:ℂ)‖ ≤ ε:=by
 filter_upwards [(Steam.horizons Λ.x (V:=Λ.V)).eventually_gt_atTop 0,Rhythm.flow Y zero_lt_one, survey Y hY h K R A T p e] with s p0 Q h'; filter_upwards [h'] with i v'; filter_upwards [v',K.pick.pass Y h s (u i)] with k v' hk; have ht:= Q (u i) (v k) hk.enters; let t:=coolant Y s (u i) (v k); let b:=𝜁 (u i) (v k) s; let c:= hat Λ.R.L Λ.x s; have hp:= p0; have hc:b >0:= (half_pos p0 |>.trans_le ht.beta.1); let x:=boon Λ s; let y:= Real.sqrt b; have hx:0<x:=Real.sqrt_pos.mpr p0; have hz:0< y:= Real.sqrt_pos.mpr hc; have he:x^2=c:=Real.sq_sqrt p0.le; have hg:y^2=b:=Real.sq_sqrt hc.le
 have hb': matchedX c b:= ht.beta
 have hu : t*y=x:= div_mul_cancel₀ _ hz.ne'
 have hw:t≥1/2:=by apply (le_div_iff₀ hz).2; apply (sq_le_sq₀ (by positivity) hx.le).1; nlinarith only [he,hg,hb'.2,hc]
 have hy:|t|≤2:=by rw [abs_of_pos (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hw)]; apply (div_le_iff₀ hz).2; apply (sq_le_sq₀ hx.le (by positivity)).1; nlinarith only [he,hg,hb'.1,hc]
 exact ⟨hk.depth,hk.enters,hy,hw,fun Φ a h=> (by have hv:=v' t Φ a h hy; rw [show amiss Y s (u i) (v k) t=x from hu] at hv; exact hv)⟩
end Stadium
end YM.CF.Buffered.Afterglow.Hierarchy.LapisS
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.LapisS.Stadium.witness
