import YM.SU5.FiniteGaugeData.Eight.Invoice
import YM.SU5.FiniteGaugeData.Hills.Domicile
import YM.SU5.FiniteGaugeData.Mirage.Lorne
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
local notation "U"=> W (tent Y h)
local notation "Ω"=> (Y.voyage i).CapeT s
local notation "E₁"=> W (tent Y h)→ₗ[ℂ]ℂ
variable {a:Axis}{d w n m:ℕ}{x f:W (tent Y h)}{vD:Axis→ℕ}(L:Master Y s i)(lP:Club Y g s)
include K R A
#check billboard
private lemma highroad (p:Studio a 0 (yard Kₜ d) (reserve Λ l) S)(e:0<d)(c:0≤C)(q:0<ε): ∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop, ∀ (f:W (tent Y h))(t:Locator (tent Y h) f S), (∀ z, ‖sold Y h s (u i) f.val z‖ ≤ C) → Credential Y h s (u i) (v k) a d 3 f → ∀ (Φ:ℕ→W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ→ ‖Φ s f‖ ≤1+ε:= by
 filter_upwards [enoughR Y h K S s,billboard Y h S s a d K R (A a) e C ε p 3 c q] with i H t
 filter_upwards [t] with k ht f t w v' Φ V'; let x:=reading (tent Y h) S f t; have hz: ‖x‖ ≤ C:= signage Y h (u i) s S x c (roomy_hosp _ H) (by unfold x; rw [reading_p]; exact w)
 exact (V'.stamp s f a).trans ((guestPrice Y h s a d K R (A a) (x:=f) ⟨S,p,t⟩ e).trans (ht _ t hz v'))
private lemma rimH (u':ℕ→ℕ)(p:StrictMono u')(t:0<d):∀ᶠ i in atTop,(∀ j∈ univ.erase a,vD j+addgap Kₜ≤(side Y (u' i) s).val)∧ 0<stops Y h s (u' i) d:= by -- omit duplicate argument. K R binds.
 filter_upwards [side_grows Y s h p (univ.sup vD+addgap Kₜ),((stops_grow Y h s d t).comp p.tendsto_atTop).eventually_gt_atTop 0] with i y p'; exact ⟨fun j _=> le_trans (Nat.add_le_add_right (le_sup (f:=vD) (mem_univ j)) _) y, p' ⟩
omit K R A in
private lemma sell_t (b:ℤ)(p:∀ z, ‖sold Y h s i f.val z‖ ≤ C):∀ z, ‖sold Y h s i (clockW Kₜ a b f).val z‖ ≤ C:=by
 have hP: ∀ (f:W Kₜ), (∀ z, ‖sold Y h s i f.val z‖ ≤ C)→ ∀ v:ℤ,∀ z, ‖sold Y h s i (fire Kₜ a v f).val z‖ ≤ C := by intro f p v z; rw [ice_print, sold_reflect]; exact (theta_fee ..).le.trans (p _)
 exact hP _ (hP f p 0) (gaugeShift Λ.block b)
theorem express (a:Axis)(p:∀ i,∃ b:ℤ,film b (vD i) S i) (c:0≤C)(k0:0≤C₀)(e:0<ε)(c':0≤θ)(p0:C₀*Real.exp (θ*capR Kₜ vD) ≤1): ∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,∀ (V: Literature (side Y (u i) s))(f:W (tent Y h))(p:Locator (tent Y h) f S), (∀ z, ‖sold Y h s (u i) f.val z‖≤ C) → Tax Y h s (u i) (V:=V) m 0 C S f → LedgerT Y s (u i) (v k) V m C C₀ θ→∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ→ ‖Φ s f‖≤1+ε:=by
 obtain ⟨z,P,t,H_p,t'⟩:= duty (K:=Kₜ) (p a).choose_spec; let T':=hour Kₜ S a z; have hz:Studio a 0 (yard Kₜ P) (reserve Λ l) T':=H_p; let v0:=v
 filter_upwards [rimH (vD:=vD) (a:=a) Y h K R A s u K.pick.grow_i t, highroad Y h K R A T' s hz t c e] with i j t_
 filter_upwards [t_,pizzazz Y s (u i) h a (m:=m) K T' t hz (fun i u=> Exists.intro _ ((p i).choose_spec.tick u.symm z)) t' j.1 j.2 k0 c c' p0] with k G HP V f s' w pF cF Φ J
 rw [← J.color s a f z]; let hF:=loc_tic Kₜ S a z s'; have hk:=sell_t Y h s (u i) (a:=a) (f:=f) z w; exact G _ hF hk (HP _ _ hF hk (Tax.tickW Y h a s (u i) z pF) cF) Φ J
-- rescale cost to final comparators. 
private lemma revenue (p:∀ i,∃ b:ℤ,film b (vD i) S i)(c:0≤C)(z:0<D)(q:0≤θ)(x:0≤α)(w:α*Real.exp (θ*capR Kₜ vD) ≤ 1)(e:D<C₀): ∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,∀ (V:Literature (side Y (u i) s))(f:W (tent Y h))(u_:Locator (tent Y h) f S), (∀ j,‖sold Y h s (u i) f.val j‖ ≤ C) → Tax Y h s (u i) (V:=V) m 0 C S f→ LedgerT Y s (u i) (v k) V m (D⁻¹*C) α θ→∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ→ ‖Φ s f‖ ≤ C₀:=by
 let n:=(D⁻¹:ℝ); have ht: 0<n:=inv_pos.mpr z; let ε:=(C₀-D)*n; have hε:0<ε:=mul_pos (sub_pos.mpr e) ht; let b:ℂ:=↑n
 filter_upwards [express Y h K R A S s (m:=m) 3 p (c:=(show 0≤n*C from mul_nonneg ht.le c)) x hε q w] with i E; filter_upwards [E] with k p' V f u' c' t O Φ H
 have he:sold Y h s (u i) (b • f).val=b • sold Y h s (u i) f.val:=map_smul (sold Y h s (u i)) _ _
 have hb:‖b‖=n:=by unfold b; rw [Complex.norm_real,Real.norm_of_nonneg ht.le]
 have hv := Hull.scale t b; rw [hb] at hv
 have hk:= p' V (b • f) (locate_scale _ _ _ u') (fun z=>by rw [he,Pi.smul_apply, norm_smul,hb]; exact mul_le_mul_of_nonneg_left (c' z) ht.le) (by unfold Tax; rw [he]; exact hv) O Φ H; rw [map_smul,norm_smul,hb] at hk; refine le_of_mul_le_mul_left (hk.trans (show 1+ε ≤ n*C₀ from ?_)) ht; unfold ε n; rw [_root_.sub_mul]; have hx:D*D⁻¹=1:=mul_inv_cancel₀ z.ne'; linarith
local notation "Δ"=> storeH Λ.V
local notation "ξ"=> Quest.zen (slopeF Λ.W g) (Δ).C
local notation "Z" v:max=> GridStep Λ l v
include lP
lemma polar (p:∀ i,∃ b:ℤ,film b (vD i) S i)(T:Crags α Λ w ε)(q:0≤g)(c:0≤C)(e:lighting m α C*Real.exp (ξ*capR (tent Y h) vD)<θ): ∀ᶠ i:ℕ in atTop,∀ y:Master Y s (u i),∀ᶠ k:ℕ in atTop,∀ z:s≤Y.uv (v k),∀(f: W (tent Y h))(t:Locator (tent Y h) f S),(∀ z,‖sold Y h s (u i) f.val z‖≤ C)→ Tax Y h s (u i) (V:=novella w (tailCost (Δ).c (Δ).C w) ε (posters Y s (u i) (v k) y z w).bleed.peg T.budget) m 0 C S f→ ∀ (Φ:ℕ→W (tent Y h) →ₗ[ℂ]ℂ),Sphere Y h K R A Φ→ ‖Φ s f‖≤θ := by
 let z:= Quest.zen (slopeF Λ.W g) (Δ).C; have he:0 ≤ z:= zen_pos _ _ (by unfold slopeF; positivity) (Δ).posse.value.le; let Ψ:= Real.exp (z*capR Kₜ vD)
 obtain ⟨b,p',t⟩:=exists_between e; have hx:0<b:=lt_of_le_of_lt (mul_nonneg (bulb m α _ c) (Real.exp_pos _).le) p'; let X:=lighting m α (b⁻¹*C); have hw:0≤b⁻¹*C:=by positivity
 have hs:X*Ψ ≤ 1:=by apply le_trans _ ((mul_le_mul_of_nonneg_left p'.le (show 0 ≤ b⁻¹ from by positivity)).trans ((inv_mul_cancel₀ hx.ne').le)); unfold Ψ X lighting; exact le_of_eq (by change _= b⁻¹*(Real.exp _*C*Ψ); unfold Ψ; ring) -- unfold on RHS z? adjust
 filter_upwards [revenue Y h K R A S s (m:=m) p c hx he (bulb m _ _ hw) hs t] with i hV y; filter_upwards [hV,K.pick.pass Y h s (u i)] with k Q' t' z f u' g H Φ T'; exact Q' _ f u' g H (LedgerT.ice Y _ _ _ y z lP T hw t'.depth) Φ T'
local notation "vV"=> Pressure.temp (hat Λ.R.L Λ.x s)
local notation "f₁"=> Steam.frost Λ.K.top.clip (hat Λ.R.L Λ.x s)
lemma troublePrice (p:∀ i,∃ b:ℤ,film b (vD i) S i)(q:0≤g)(c:0≤C)(e:C*Real.exp (-f₁)*Real.exp (slopeF Λ.W g * capR Kₜ vD)<θ):∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,∀ (f:W (tent Y h))(xV:Locator (tent Y h) f S),(∀ z,‖sold Y h s (u i) f.val z‖≤ C)→Glints 1 (region S (side Y (u i) s)) vV (sold Y h s (u i) f.val) →∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ→ ‖Φ s f‖ ≤ θ:=by
 let x:=slopeF Λ.W g; have hv:0 ≤ x:=by unfold x slopeF; positivity
 obtain ⟨b,t,pT⟩:= exists_between e; have hz:0<b:=lt_of_le_of_lt (mul_nonneg (mul_nonneg c (Real.exp_pos _).le) (Real.exp_pos _).le) t; let F:= b⁻¹*C*Real.exp (-f₁); have hw:0≤ b⁻¹*C:=by positivity
 have h₀:F*Real.exp (x*capR Kₜ vD) ≤ 1:= ((mul_le_mul_of_nonneg_left t.le (inv_pos.mpr hz|>.le)).trans ((inv_mul_cancel₀ hz.ne').le)).trans' (show F*Real.exp (x*capR Kₜ vD)≤ b⁻¹* _ from le_of_eq (by unfold x F; ring))
 filter_upwards [revenue Y h K R A S s (m:=1) p c hz hv (mul_nonneg hw (Real.exp_pos _).le) h₀ pT] with i t; filter_upwards [t,K.pick.pass Y h s (u i)] with k p' t f u' v g Φ H; exact p' _ f u' v (Hull.trig (V:=fairy vV _) g (sold_affair Y h S s (u i) u') v) (LedgerT.eye Y s _ _ t.enters lP hw t.depth) Φ H -- natural glints by defin
#print axioms polar
#print axioms troublePrice
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
