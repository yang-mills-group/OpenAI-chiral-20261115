import YM.SU5.FiniteGaugeData.SalonG.Itinerary
import YM.SU5.FiniteGaugeData.Marked.Journey.Wake
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace SalonG
open Nacre Heat Charm Chrono Journey
section adapters
open ContinuousLinearMap
variable {X Y Z:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]
 [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedAddCommGroup Z][NormedSpace ℂ Z]
 {ρ σ τ:ℂ→+*ℂ}[RingHomIsometric ρ][RingHomIsometric σ][RingHomIsometric τ][RingHomCompTriple ρ σ τ]
 {I:Type*}{w:Filter I}
lemma tendSL {P:I→ Y →SL[σ] Z}{Q:I→ X →SL[ρ] Y}{a:Y→SL[σ] Z}{b:X→SL[ρ]Y}(p:Tendsto P w (𝓝 a))(q:Tendsto Q w (𝓝 b)): Tendsto (fun i=>(P i).comp (Q i)) w (𝓝 (a.comp b)):=(show Continuous fun z:(Y→SL[σ] Z)×(X→SL[ρ]Y)=> (compSL X Y Z ρ σ).flip z.2 z.1 from (((compSL X Y Z ρ σ).flip).continuous.comp continuous_snd).clm_apply continuous_fst).continuousAt.tendsto.comp (p.prodMk_nhds q)
lemma tendFlip {P:I→X→SL[ρ] Y→SL[σ]Z}{a:X→SL[ρ]Y→SL[σ]Z}(p:Tendsto P w (𝓝 a)): Tendsto (fun i=>(P i).flip) w (𝓝 a.flip):= by
 have he:= ((flipₗᵢ' X Y Z σ ρ).continuous.tendsto a).comp p; exact he
abbrev conjugator (U: Y→L⋆[ℂ] Y→L[ℂ] Z) (p:X→L[ℂ]Y) : X→L⋆[ℂ] X→L[ℂ]Z:= (((U.comp p).flip).comp p).flip
lemma tendTie {U:I→ Y→L⋆[ℂ]Y→L[ℂ]Z}{V:Y→L⋆[ℂ] Y→L[ℂ] Z}{P:I→X→L[ℂ]Y}{p:X→L[ℂ]Y}(u:Tendsto U w (𝓝 V))(v:Tendsto P w (𝓝 p)) : Tendsto (fun i=> conjugator (U i) (P i)) w (𝓝 (conjugator V p)):= tendFlip (tendSL (tendFlip (tendSL u v)) v)
lemma tendBase (U:X→L⋆[ℂ]X→L[ℂ] Y){F:I→ Y→L[ℂ] Z}{p:Y→L[ℂ]Z}(v:Tendsto F w (𝓝 p)): Tendsto (fun i=>(compL ℂ X Y Z (F i)).comp U) w (𝓝 ((compL ℂ X Y Z p).comp U)):= tendSL (((compL ℂ X Y Z).continuous.tendsto _).comp v) tendsto_const_nhds
end adapters
-- unit weight quadratic form uniform along paths after Offer; actual heatForm. RP at Γ for W with Gauge maybe durable or not. Lipschitz from Wake
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
local notation "ν"=> momentm Y i s
local notation "W₀"=> W (tent Y h)
local notation "λ₀"=> deltaL Y h i s
local notation "A₁"=> (Kₜ.c ν)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (p_:Ferry Y s i k)
def coalX : Catalog S→ₗ[ℂ]ℂ where
 toFun f:= hot Y h s i k (composeQ Kₜ S f)
 map_add' f g:= by rw [map_add]; exact hot_add Y h s (compose_test Kₜ S f) (compose_test Kₜ S g) p_
 map_smul' c x:=by rw [map_smul]; exact hot_mul Y h s c p_
local notation "D"=> duration S
local notation "O"=>Real.exp (duetCharge Y s * ((momentm Y i s).val:ℝ)^4)
lemma cash_g {L:Loom ((tent Y h).c ν)}(f:Catalog S): cash L (composeQ Kₜ S f ν)≤duration S*‖f‖:=by
 unfold cash; refine (integral_mono_of_nonneg (Eventually.of_forall (fun _=> norm_nonneg _)) (integrable_const («μ»:=city _) (duration S* ‖f‖)) (Eventually.of_forall (fun x'=> compose_price S Kₜ f ν _))).trans_eq (by simp)
lemma coal_p (f:Catalog S):‖coalX Y h S s i k p_ f‖ ≤ (Real.exp (duetCharge Y s * ((momentm Y i s).val:ℝ)^4)*duration S)* ‖f‖:=by
 change ‖hot ..‖≤ _; unfold hot; rw [dif_pos p_.depth,mul_assoc]; exact ((boxprice Y h i k p_.depth s p_.fire p_.enters).tally _ ((compose_t S Kₜ f).support ν).env).trans (mul_le_mul_of_nonneg_left (cash_g Y h S s i f) (Real.exp_pos _).le)
open scoped Classical
def coalMeter : Catalog S→L[ℂ]ℂ:= (coalX Y h S s i k p_).mkContinuous ((O)* D) (coal_p Y h S s i k p_)
def coal (s:ℕ)(i k:ℕ): Catalog S→L[ℂ]ℂ := if p:Ferry Y s i k then coalMeter Y h S s i k p else 0
-- bind unit profile.Launch
include p_
lemma coal_view (f:Catalog S): coal Y h S s i k f= hot Y h s i k (composeQ Kₜ S f):= by rw [coal,dif_pos p_]; rfl
omit p_
local notation "Γ" s:max i:max k:max => LocalLimit.Donor.divisionBill Y.meter Λ.C Y.τ s (Y.ivory k) (Y.ir i)
lemma gluedM (ε:ℝ)(e:0<ε) : ∀ᶠ k:ℕ in atTop,∀ i:ℕ, Ferry Y s i k → (∀ (y:W₀), ‖sharp Y h s i k y.val - hot Y h s i k y.val‖ ≤ ε* cash (deltaL Y h i s) (y.val (momentm Y i s))) ∧ ‖mkForm Y h S s i k - coal Y h S s i k‖ ≤ ε*duration S:=by
 filter_upwards [Y.UV.tendsto_atTop.eventually (LocalLimit.Donor.shrinks (T:=Y.meter) (C:=Λ.C) («τ»:=Y.τ) s Λ.b e)] with k v i p
 let t:= boxprice Y h i k p.depth s p.fire p.enters; have he:(Γ s i k) ≤ ε:= v (Y.ir i) ((Y.voyage i).domain k p.depth)
 have hx(f: Family Kₜ)(x:TestFamily Kₜ true f):‖sharp Y h s i k f-hot Y h s i k f‖≤ ε*cash (deltaL Y h i s) (f (momentm Y i s)):=by
    obtain ⟨S,v⟩:=x.paid; unfold hot; rw [dif_pos p.depth]; exact (awaken Y h s p (f (momentm Y i s)) (v.support _).env).trans (mul_le_mul_of_nonneg_right he (cash_nonneg ..))
 refine ⟨fun y=>hx y.val (well_for Kₜ y).1, ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg e.le (duration_pos _).le) fun x=>?_⟩
 rw [_root_.sub_apply,mk_read Y h S s i k ⟨p.depth,p.enters⟩,coal_view Y h S s i k p,mul_assoc]; exact (hx _ (compose_test Kₜ S x)).trans (mul_le_mul_of_nonneg_left (cash_g Y h S s i x) e.le)
include W'
lemma coal_t {k:ℕ→ℕ} (p:eligiblePath Y u v k): Tendsto (fun i=>coal Y h S s (u i) (v (k i))) atTop (𝓝 (singer Y h S s W')):=by
 refine (Metric.tendsto_nhds (α:=Catalog S→L[ℂ]ℂ)).mpr fun r e=> ?_
 have hx:0<r/3:= by linarith
 let C:=duration S; have ht:0 < C:= duration_pos _
 filter_upwards [p,boutique_P Y h S s W' (r/3) hx, W'.pick.cone_ferry Y h s p,(W'.pick.walks Y h p).eventually (gluedM Y h S s ((r/3)/C) (by positivity))] with i a b p u'
 let M:= mkForm Y h S s (u i) (v (k i)); let B:= coal Y h S s (u i) (v (k i)); let X:= singer Y h S s W'
 have he:dist M X≤r/3:= (dist_eq_norm M X).symm ▸ ((b.2 (k i) a).2); have hz:dist M B≤r/3:=by rw [dist_eq_norm M B]; exact (u' _ p).2.trans_eq (div_mul_cancel₀ _ ht.ne')
 exact lt_of_le_of_lt (dist_triangle_left B X M) (by linarith)
#print axioms coal_t
#print axioms gluedM
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
