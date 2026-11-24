import YM.SU5.FiniteGaugeData.Lapis.Porch
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
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
set_option quotPrecheck false
variable (s i k:ℕ)
local notation "Ω" => side Y i s
local notation "VW" => (storeH Λ.V)
local notation "Q" => (Y.voyage i).CapeT s
local notation "WT" => hat Λ.R.L Λ.x s
local notation "ζ" => slopeF Λ.W g

variable (D:Master Y s i) (p:s≤ Y.uv k) (B':Club Y g s) {C ε α θ:ℝ}
variable (h:Real.exp 1 ≤ Λ.x)
local notation "Kx" => tent Y h
local notation "S₀"=>(Y.voyage i).CapeT s
local notation "Ψ" k:max=> Journey.compass Y i k s
private lemma metered (p: Ferry Y s i k) : Journey.Metered Kx (momentm Y i s) (deltaL Y h i s) (Journey.solder Y i k p.depth s ∘ ship (terrain Y h (Y.ir i) s)) (duetCharge Y s) := by
    have he:= boxprice Y h i k p.depth s p.fire p.enters
    rw [show (Journey.solder Y i k p.depth s ∘ ship (terrain Y h (Y.ir i) s))=collector Y h i k p.depth s from funext fun x=>(congrArg (Journey.solder Y i k p.depth s) (ship_eq (terrain Y h (Y.ir i) s) x))]; exact he
omit h in
private lemma frost_delta (A:ℝ)(p:0≤A)(ε:ℝ)(e:0<ε) :∀ᶠ k in atTop, ∀ v:(Y.voyage i).kick ≤ k, ∀ x:Mark Ω, Envelope x→ (∀ i,‖x i‖ ≤ A)→ ‖(Ψ k) x-Journey.solder Y i k v s x‖ ≤ ε:=by
 have hz:0<A+1:=by linarith
 filter_upwards [Y.thaw s (ε/(A+1)) (by positivity)] with k t H x f b
 let W : Envelope (x ∘ drawn (S₀)):= mark_pay ((Y.voyage i).ownership s).paid.bill f
 exact le_trans (t i H (x ∘ drawn (S₀)) (A+1) W.meas (fun x=> le_trans (b _) (by linarith))) (div_mul_cancel₀ _ hz.ne').le

variable {t m n w d:ℕ}
open Eight YM.SU5.FiniteGaugeData.Lapis Lumi
variable {ι:Type}[Fintype ι][DecidableEq ι]

abbrev Paper (i k:ℕ)(A:Duct SU.group ι)(F₀:Clip)(v b α D θ: ℝ):Prop:=∀ (U:Support (More (side Y i s)))(n:ℕ)(y:Mark (side Y i s)), Packed A F₀ v b α n U y → ‖Journey.compass Y i k s y‖ ≤ D^n *Real.exp (θ*Rate.sites (side Y i s))
variable (a:Axis) {f x:W (tent Y h)}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ} (K:Universal Y h u v I E) {C₀:ℝ}
local notation "ℓ"=> reserve Λ l
variable (S:Finset Cover) {T:Axis→ℕ}
local notation "V₀"=> momentm Y i s
--local notation "X"=> stops Y h s i d -- bind variable X shadows errors below; remove
private lemma castPurchase {N M:Side}(e:N=M)(x:Mark N){C:ℝ}(v:∀ z,‖x z‖≤ C):∀ z,‖ship e x z‖ ≤ C:=by subst M; exact v
private lemma castPurchase' {N M:Side}(e:N=M)(x:Mark N){C:ℝ}(v:∀ z, ‖ship e x z‖≤ C):∀ z,‖x z‖ ≤ C:= by subst M; exact v
include K
lemma stag (g:0<d) (t:Studio a 0 (yard Kx d) (reserve Λ l) S)(M: ∀ i:Axis,i≠ a→ ∃ b:ℤ,film b (T i) S i)
 (e:yard Kx d≤2*(T a+addgap Kx)) (q: ∀ j∈ univ.erase a,T j+addgap Kx ≤ (Ω).val)(w: 0< stops Y h s i d) (b0:0 ≤ C₀)(a0:0 ≤ C)(a1:0 ≤ θ)(v0:C₀*Real.exp (θ*capR Kx T) ≤ 1): ∀ᶠ k:ℕ in atTop, ∀ (v0 b α:ℝ)(A₀:Duct SU.group ι)(F₀:Clip)(f:W (tent Y h))(p:Locator (tent Y h) f S), (∀ z, ‖sold Y h s i f.val z‖≤ C)→ Rent Y h s i A₀ F₀ v0 b α 1 S f → Paper Y s i (v k) A₀ F₀ v0 b α C₀ θ → Credential Y h s i (v k) a d 3 f :=by
 have hf := terrain Y h (Y.ir i) s; have ht:= stops_p Y h s i d g
 let n:=stops Y h s i d; obtain ⟨Δ,hx,he,pr⟩:= Mansion (T:=S) hf.symm w ht e (hf.symm ▸ q) M; let U:=terrace a d n S (K:=Kx); let t' := (v:ℕ→ℕ); let Y':= Real.exp (θ* capR Kx T); let Z':=4*n
 let x:=4*n*Δ; have htn (k):s≤ Y.uv k→ s≤ Y.uv k:=fun p=>p -- remove
 have he':C₀^x * Real.exp (θ* Rate.sites (Ω)) ≤ 1:=by
    have hz:(C₀*Y')^x ≤ (1:ℝ):= pow_le_one₀ (by unfold Y'; positivity) v0
    apply le_trans _ hz; change _≤ (C₀*Y')^x; rw [mul_pow]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg b0 _); unfold Y'; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; change Rate.sites (Ω)≤ ↑x*capR Kx T at he; nlinarith only [mul_le_mul_of_nonneg_left he a1]
 filter_upwards [K.pick.pass Y h s i, K.pick.grow_k.tendsto_atTop.eventually (frost_delta Y s i (C^x) (pow_nonneg a0 _) 1 one_pos), K.pick.grow_k.tendsto_atTop.eventually (frost_delta Y s i (C^Z') (pow_nonneg a0 _) 1 one_pos)] with k P F' Ft vy b α Yp Yq f p z tK L
 let J:= CarrierF a d n f; let Fx:= sold Y h s i J.val; let W':=region U (Ω); have hv:AtSupport false W' Fx:= sold_affair Y h U s i (vigilant a d n S f p); have hz:= diligent Kx V₀ a d n f C (castPurchase' hf (f.val V₀) z); have hy:∀ z,‖Fx z‖ ≤ C^Z':= castPurchase hf (J.val V₀) hz
 obtain ⟨S',y,U'⟩:= pr Fx
 have hw:2*proceed Kx n d≤(Ω).val:=  by rw [show Ω= (Kx).c (V₀) from hf.symm]; exact ht.lower
 have h': Packed Yp Yq vy b α x S' y:= mirror_earns (Journey.prepared Λ l) U' (Rent.recycled Y h a s i t tK hw)
 have hh:‖(Ψ (v k)) y‖ ≤ 1:= (L _ _ _ h').trans he'
 let X0:= Journey.solder Y i (v k) P.depth s
 have hs := F' P.depth y (U'.covers hv).env (by unfold x; rw [pow_mul]; exact U'.cost hy); have h2: ‖X0 y‖ ≤ 2:=by rw [norm_sub_rev] at hs; linarith only [(show ‖X0 y‖-‖(Ψ (v k)) y‖ ≤ 1 from (norm_sub_norm_le ..).trans hs), hh]; -- orientation
 have hC: ‖X0 Fx‖ ≤ 2:= le_of_pow_le_pow_left₀ hx.ne' (by norm_num) ((Mirror.heat hf.symm U' (metered Y s i _ h P) hv).trans (h2.trans (le_self_pow₀ (by norm_num) hx.ne')))
 unfold Credential; rw [sold_sharp]; change ‖(Ψ (v k)) Fx‖ ≤ 3; have h:= Ft P.depth Fx hv.env hy; linarith only [hC,(show ‖(Ψ (v k)) Fx‖-‖X0 Fx‖≤ 1 from (norm_sub_norm_le ..).trans h)]
end YM.CF.Buffered.Afterglow.Hierarchy.LapisS

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
open Eight YM.SU5.FiniteGaugeData.Lapis Lumi
variable {ι:Type}[Fintype ι][DecidableEq ι]

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
theorem cashC (a:Axis)(p:∀ i,∃ b:ℤ,film b (vD i) S i) (c:0≤C)(k0:0≤C₀)(e:0<ε)(c':0≤θ)(p0:C₀*Real.exp (θ*capR Kₜ vD) ≤1): ∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,∀ (v0 b α:ℝ)(A₀:Duct SU.group ι)(F₀:Clip)(f:W (tent Y h))(p:Locator (tent Y h) f S), (∀ z, ‖sold Y h s (u i) f.val z‖≤ C) → Rent Y h s (u i) A₀ F₀ v0 b α 1 S f → Paper Y s (u i) (v k) A₀ F₀ v0 b α C₀ θ→∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ→ ‖Φ s f‖≤1+ε:=by
 obtain ⟨z,P,t,H_p,t'⟩:= Eight.duty (K:=Kₜ) (p a).choose_spec; let T':=hour Kₜ S a z; have hz:Studio a 0 (yard Kₜ P) (reserve Λ l) T':=H_p; let v0:=v
 filter_upwards [rimH (vD:=vD) (a:=a) Y h K R A s u K.pick.grow_i t, highroad Y h K R A T' s hz t c e] with i j t_
 filter_upwards [t_,stag Y s (u i) h a (ι:=ι) K T' t hz (fun i u=> Exists.intro _ ((p i).choose_spec.tick u.symm z)) t' j.1 j.2 k0 c c' p0] with k G HP vy a0 d0 J T f s' w pF cF Φ Jx
 rw [← Jx.color s a f z]; let hF:=loc_tic Kₜ S a z s'; have hk:=sell_t Y h s (u i) (a:=a) (f:=f) z w; exact G _ hF hk (HP _ _ _ _ _ _ hF hk (Rent.tickW Y h a s (u i) z pF) cF) Φ Jx

#print axioms cashC
end YM.CF.Buffered.Afterglow.Hierarchy.LapisS
