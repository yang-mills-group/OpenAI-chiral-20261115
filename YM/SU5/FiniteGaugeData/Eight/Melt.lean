import YM.SU5.FiniteGaugeData.Eight.Senate
import YM.SU5.FiniteGaugeData.Mirage.Parole
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Eight
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
open Quest.Chaperone
open Steam
variable {Λ: Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E){P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)
variable (A:∀ i:Axis, Repertory Y h K R i)
open Hills Tint
variable (S T:Finset Cover)(s i k:ℕ) {g α C D ε θ C₀:ℝ}
local notation "Kₜ"=> tent Y h
local notation "N"=> side Y i s
local notation "Ω"=> (Y.voyage i).CapeT s
local notation "E₁"=> W (tent Y h)→ₗ[ℂ]ℂ
section
variable (Z:Finset (Face ℤ))(Q: LinksC→ℂ)(F:Family (tent Y h))(t:ℝ)
lemma Model_oneV (Φ:ℕ→Charm.W (tent Y h)→ₗ[ℂ]ℂ)(p:Sphere Y h K R A Φ) : Model Y h Φ s 1=1:=by rw [← identityW, Modell,p.living]
lemma roseColor (p: GaugeInvariant Q)(K:Calibration) : Durable K (dutiful K Q):=by
 intro i g x; change Q _ • (1:FC _)= twist (quantU (tradew _ _)) _; unfold dutiful scalar; change Q (onC _ (Lattice.gauge g x.1)) • (1:FC _) = twist (quantU (tradew (K.c i) g)) (Q (onC _ x.1) • 1); rw [twist_scalar, map_one,Chart.gauge_here,p]
lemma bedColour : GaugeInvariant (bedH Z t):=by
 intro g x; change (↑(∏ i∈Z,max 0 (min 1 (2-SU.group.chord (faceValue (Lattice.gauge g x) i)/t))):ℂ)=(↑(∏ i∈Z,max 0 (min 1 (2-SU.group.chord (faceValue x i)/t))):ℂ); simp_rw [face_gauge, SU.group.chord_conj]
-- high s buys Panelcut, Cover.THRESH
variable (lQ:∀ᶠ s:ℕ in atTop, Club Y g s)(k0:0≤g)
local notation "vV"=> Pressure.temp (hat Λ.R.L Λ.x s)
local notation "f₁"=> Steam.frost Λ.K.top.clip (hat Λ.R.L Λ.x s)
lemma sphereCap (Ko:Calibration)(D:ℕ) : capR Ko (fun _=>D)= ((4:ℝ)*(D+addgap Ko:ℕ))^4:=by unfold capR; push_cast; rw [prod_const,card_fin] -- pushcast D+d.
include lQ K R A k0
private lemma chalkF : ∀ᶠ s in atTop, Pressure.temp (hat Λ.R.L Λ.x s)< |ε|+1:=by
 apply ((show Tendsto Pressure.temp atTop (𝓝 0) from (by simpa using Work.E09.radiusB_temp 0)).comp (Steam.horizons (V:=Λ.V) Λ.x)).eventually (gt_mem_nhds (by positivity))
lemma Incur {C:ℝ}(v:0≤C)(u:0<ε)(y:0<θ): ∀ᶠ s:ℕ in atTop, ( Pressure.temp (hat Λ.R.L Λ.x s) ≤ θ) ∧ ∀ (f:W Kₜ), Locator Kₜ f S → Width Kₜ f C → ∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ→ ‖Model Y h Φ s (troubles Kₜ Z (Pressure.temp (hat Λ.R.L Λ.x s))*f.val)‖ ≤ ε:=by
 let T:= carpet Z∪ S; obtain ⟨D,Q'⟩: ∃ D:ℕ,∀ i:Axis,∃ p:ℤ,film p D T i:= by
    let Z':= T.sup fun i=> univ.sup fun a:Axis=>(i a).natAbs; refine ⟨2*Z',fun a=> ⟨-(Z':ℤ),fun i t=>?_⟩⟩; have he:(i a).natAbs ≤ Z':= (le_sup (f:=fun a:Axis=>(i a).natAbs) (mem_univ _)).trans (le_sup (f:=fun i=>univ.sup fun a:Axis=>(i a).natAbs) t); omega
 let W:= hat Λ.R.L Λ.x; have hw:= Steam.horizons (V:=Λ.V) Λ.x; let M:=Real.exp (slopeF Λ.W g * capR Kₜ (fun _=>D)); let f:= Steam.frost Λ.K.top.clip; have hu:Tendsto (fun s=> C*Real.exp (-f (W s))*M) atTop (𝓝 0):=by
    have hv:Tendsto (fun s=> Real.exp (-f (W s))) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ((frostT _).comp hw)); simpa using (hv.const_mul C).mul_const M
 filter_upwards [lQ, ((show Tendsto Pressure.temp atTop (𝓝 0) from (by simpa using Work.E09.radiusB_temp 0)).comp hw).eventually (ge_mem_nhds y),hu.eventually (ge_mem_nhds u)] with s v0 p a; exact ⟨p,fun f t u Φ r=>(coverageV Y h K R A S s Φ v0 Z (vD:=fun _=>D) Q' v k0 r f t u).trans a⟩ -- tune arg order
lemma Senate.coveted (p:0<t):∀ᶠ s:ℕ in atTop, ∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ→ 1/4< ‖Model Y h Φ s (umbrella Z t Kₜ)‖:=by
 let u:= carpet Z; let B:Charm.W Kₜ:=⟨umbrella Z t Kₜ,⟨⟨u,(bower Z t _).widen⟩,by simp⟩,(show Durable _ (umbrella Z t Kₜ) from roseColor _ (bedColour Z t) Kₜ)⟩
 have he:Locator Kₜ (1-B) u:= by rw [show (1-B)=1+((-1:ℂ)•B) from (by module)]; exact locate_sum _ _ (locate_one ..) (locate_scale _ _ _ ((bower Z t _).widen))
 have hp:Width Kₜ (1-B) 2:=fun i x=>by change ‖(1: FC _) - umbrella Z t Kₜ i x‖ ≤ _; exact (norm_sub_le ..).trans (le_trans (add_le_add ((norm_one (α:=FC _)).le) (roof_line ..)) (le_of_eq (by norm_num)))
 filter_upwards [Incur Y h K R A u Z lQ k0 zero_le_two (by norm_num:(0:ℝ)<1/4) p] with s l Φ hB; have hv:= l.2 (1-B) he hp Φ hB
 rw [show troubles Kₜ Z (Pressure.temp (hat Λ.R.L Λ.x s)) * Subtype.val (p:=fun f=>f∈ well Kₜ) (1-B)=1- umbrella Z t Kₜ from harsh_w Z t _ _ p l.1, map_sub, Model_oneV Y h K R A s Φ hB] at hv; have h2:= norm_sub_norm_le (1:ℂ) ( Model Y h Φ s (umbrella Z t Kₜ)); rw [norm_one] at h2; linarith
-- pay transformed purchase analogue. bering.Senator secured by shape.
omit lQ K R A k0 in
private lemma spell (v:ℝ)(G: Finset (Face ℤ))(q:∀ x:LinksC, ¬alarm G v (x,x)→Q x=1): (troubles (tent Y h) G v)*(1-dutiful (tent Y h) Q)=1-dutiful (tent Y h) Q:=by
 funext m x; let N':= (tent Y h).c m; by_cases v':alarm G v (onC N' x.1,onC N' x.2); · rw [Pi.mul_apply,Pi.mul_apply,show troubles _ _ _ m x= (1:FC (Single N')) from ?_,one_mul]; unfold troubles scalar strike; rw [if_pos v',one_smul]
 rw [Pi.mul_apply,Pi.mul_apply,show (1- dutiful Kₜ Q) m x=(0:FC (Single N')) from ?_, mul_zero]; unfold dutiful scalar; dsimp only [Pi.sub_apply, Pi.one_apply,comp_apply]; rw [q _ v', one_smul,sub_self]
private lemma faith (u:Continuous Q)(p:Lattice.LocalOn S Q)(t:GaugeInvariant Q)(q:∀ v, ‖Q v‖≤ 1) : ∃ g:W (tent Y h),g.val= dutiful Kₜ Q ∧ Locator Kₜ g S∧ Locator Kₜ (1-g) S ∧ Width Kₜ (1-g) 2:=by
 let U_:=(InTest.seed (Coeff.fromC _ _ u p)|>.widen : InTest Kₜ true S false (dutiful Kₜ Q)); let y:Charm.W Kₜ:= ⟨dutiful Kₜ Q,⟨⟨S,U_⟩,by simp⟩,roseColor Q t Kₜ⟩; refine ⟨y,rfl,U_, ?_,fun i x=>?_⟩
 · rw [show 1-y=1+((-1:ℂ)•y) from by module]; exact locate_sum _ _ (locate_one ..) (locate_scale _ _ _ U_)
 have hz: ‖dutiful Kₜ Q i x‖ ≤ 1:=by unfold dutiful scalar; simp only [norm_smul,norm_one,mul_one,Function.comp_apply]; exact q _
 change ‖(1:FC (Single _))-dutiful Kₜ Q i x‖ ≤_; exact (norm_sub_le ..).trans (by rw [norm_one]; linarith)
omit lQ K R A k0 in
private lemma sell_rose (F g:W Kₜ)(p:Roomy S (side Y i s))(u:Locator Kₜ F S)(v:Locator Kₜ g S)(L:Mark (side Y i s)→ₗ[ℂ]ℂ){x:Mark (side Y i s)}(e:AtSupport false (region S N) x)(q:sold Y h s i g.val=dewG (side Y i s) x) (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ) (A':Senate Y h S s i Φ L) : L (sold Y h s i F.val*x)=Model Y h Φ s (F*g).val:=by
 have hp:= sold_affair Y h S s i u; apply A'.price _ _ (hp.mulM e) (locate_join _ _ u v); rw [joinW,sold_mult,q,dewMult (p:=e) _ ((sold_color Y h S s i u (roomy_hosp _ p)).2 ((well_for _ F).2))]
lemma thawEye (C':0≤C)(p₀:Continuous Q)(x:Lattice.LocalOn S Q)(q:GaugeInvariant Q) (H:∀ i:LinksC,‖Q i‖ ≤ 1)(h1:∃ Z:Finset (Face ℤ),∃ t:ℝ,0<t∧∀ c:ℝ, c≤ t→ ∀ V:LinksC, ¬alarm Z c (V,V)→ Q V=1) : ∀ᶠ s:ℕ in atTop,∀ (i:ℕ), Roomy S (side Y i s) → ∀ (L:Mark (side Y i s)→ₗ[ℂ]ℂ)(Φ:ℕ→W (tent Y h)→ₗ[ℂ]ℂ),Sphere Y h K R A Φ → Senate Y h S s i Φ L → ∀ X:Mark (side Y i s), AtSupport false (region S (side Y i s)) X → (∀ z,‖X z‖ ≤ C) → ‖L X-L (Mirage.canv (Q ∘ onC _)*X)‖ ≤ 1/4:=by
 obtain ⟨Z,b,e,r⟩:=h1; let c:=2*(duration S*C); have ht:0 ≤ c:= mul_nonneg zero_le_two (mul_nonneg (duration_pos _).le C'); obtain ⟨w,U,pw,V,v⟩:= faith Y h K R A S Q lQ k0 p₀ x q H -- faith K incl
 filter_upwards [Incur Y h K R A S Z lQ k0 ht (show (0:ℝ)<1/4 from by norm_num) e] with s t i m L Φ he L' X x' T
 obtain ⟨y,z,F,g'⟩:= Senator.salvage Y h S s i L' m x'; let W:=(1-w)*y; have hz:Width (tent Y h) y (duration S*C):=by
    obtain ⟨G,hG⟩:= Hierarchy.certify S Kₜ y.val z; have hp:= signage Y h i s S G C' (roomy_hosp _ m) (by rw [hG,F]; exact dewBound T); intro i; refine fun v=>?_ ; change ‖y.val i v‖≤_; rw [←hG]; exact (compose_price ..).trans (mul_le_mul_of_nonneg_left hp (duration_pos _).le)
 have hx':Width Kₜ W c:= fun i=>RealWidth.mule (v i) (hz i)
 rw [← flagValue Y h i s Q,←U,sell_rose Y h S s i w y m pw z L x' F Φ L',g', ← Modell Y h s Φ y] -- ↑ tune
 have hb:= t.2 W (locate_join _ _ V z) hx' Φ he; rwa [show troubles (tent Y h) Z (Pressure.temp (hat Λ.R.L Λ.x s)) * W.val = y.val-(w*y).val from ?_,map_sub] at hb -- second goal
 change troubles _ _ _*((1-w.val)*y.val)= y.val-(w.val*y.val); rw [←mul_assoc,U,spell Y h Q (Pressure.temp (hat Λ.R.L Λ.x s)) Z (r _ t.1), _root_.sub_mul,one_mul];
#print axioms Senate.coveted
end
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
