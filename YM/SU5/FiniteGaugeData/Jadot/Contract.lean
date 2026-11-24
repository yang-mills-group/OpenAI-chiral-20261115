import YM.SU5.FiniteGaugeData.CodaT.Chell
/-! # Generalize Tutor WP18. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
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
open YM.SU5.FiniteGaugeData.CodaT Eight
/- coupon assembly in analogy with WP8 Invoice---no scales except the original publisher supplies from the start, at THIS price. -/
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
variable (a i:Axis)
variable {Ck Z:Side} {K:Calibration} {S T:Finset Cover} {j k M d r n w:ℕ}
variable (s i0:ℕ)
local notation "N"=> side Y i0 s
local notation "Kₜ"=> tent Y h
local notation "B"=> (tent Y h).B
local notation "L"=> (Y.voyage i0).CapeT s
local notation "V₀"=> proceed (tent Y h)
namespace Gamer
structure Contract (NP:Side) where
 art : ℕ→ Support (More NP) → Mark NP → Prop
 unit(V: Support (More NP)): art 0 V 1
 enlarge{S T:Support (More NP)}{n:ℕ}{x:Mark NP}(h:art n S x)(p:S⊆T): art n T x
 both{S T: Support (More NP)}{m n:ℕ}{x y: Mark NP}(h:art m S x)(p:art n T y)(t:Disjoint S T): art (m+n) (S∪T) (x*y)
 turn(a:Axis)(z:ℤ){S:Support (More NP)}{f:Mark NP}{n:ℕ}(h:art n S f): art n (refF NP a z S) (Buffered.reflMark a z f)
-- note notation NP used conflicts binder.E. rename above
variable {f g: W (tent Y h)}{J: Contract (side Y i0 s)}
abbrev RentG (J:Contract (side Y i0 s))(n:ℕ)(S:Finset Cover)(x:W (tent Y h)):= J.art n (region S (side Y i0 s)) (sold Y h s i0 x.val)
local notation "Π'"=> RentG Y h s i0 J
lemma RentG.fireW (z:ℤ)(p:Π' k S f): Π' k (refract a z S) (fire Kₜ a z f):=by unfold RentG; rw [ice_print,sold_reflect,refl_region]; exact J.turn a z p
lemma RentG.tickW (z:ℤ)(p:Π' k S f): Π' k (hour Kₜ S a z) (clockW Kₜ a z f):=by rw [shiftHour]; exact RentG.fireW Y h a s i0 _ (RentG.fireW Y h a s i0 0 p)
lemma RentG.join (t:Π' k S f) (u:Π' M T g)(e:SeatRange r (side Y i0 s) S T): Π' (k+M) (S∪T) (f*g):=by
 unfold RentG; rw [joinW,sold_mult, SalonG.region_union]; apply J.both t u; refine Finset.disjoint_left.mpr (fun i y q=>?_); specialize e i y i q; simp at e
variable (x: Studio a 0 (yard (tent Y h) d) (reserve Λ l) S)
local notation "η"=> reserve Λ l
local notation "T₁"=> proceed_set Kₜ a d S n
include x
lemma RentG.Colony (p:Π' 1 S f)(q:proceed (tent Y h) n d ≤ (side Y i0 s).val): Π' n (proceed_set Kₜ a d S n) (SalonG.Train Kₜ a d f n):= by
 induction n with
 | zero=> rw [proceed_set,SalonG.Train, RentG,identityW, sold_one]; exact J.unit _
 | succ n ih=>
   rw [proceed_succ] at q; have xn:= ih (by omega); let z:= (yard Kₜ d:ℤ); let r_:=refract a (gaugeShift B d) S; let v0:= S∪ r_; let U':= clockW Kₜ a d (SalonG.Train Kₜ a d f n); let S':= hour Kₜ (proceed_set Kₜ a d S n) a d
   have hu:SeatRange (spaceBill Λ l) (side Y i0 s) (S∪r_) S':= seat_separate a (N) (S:=S∪r_) (y:=z) ((x.union (arbour x)).earlier (by omega)) ((shift_port Kₜ a (n:=n) x).later (by rw [proceed_succ]; omega))
   rw [SalonG.Train,proceed_set,reamW,show n+1=1+n from by omega]; split_ifs with e
   · exact RentG.join Y h s i0 (f:=f) (g:=U') (J.enlarge p (image_subset_image subset_union_left)) (RentG.tickW Y h a s i0 d xn) hu
   exact RentG.join Y h s i0 (f:=mateW Kₜ a d f) (g:=U') (J.enlarge (RentG.fireW Y h a s i0 (gaugeShift B d) p) (image_subset_image subset_union_right)) (RentG.tickW Y h a s i0 d xn) hu
lemma RentG.jacket (p:Π' 1 S f)(q:proceed (tent Y h) n d ≤ (side Y i0 s).val): Π' (2*n) (blanket a d n (K:=Kₜ) S) (Jacket a d n f):= by
 have xn:= RentG.Colony Y h a s i0 x p q; have hs:= RentG.fireW Y h a s i0 0 xn; have hv:later 0 (N) (T₁) a η:= (proceed_geo Kₜ a d n x).later (by omega); rw [two_mul]; exact RentG.join Y h s i0 hs xn (seat_separate a (N) (y:=0) (S:=refract a 0 (T₁)) (by rw [cold_twice]; exact hv) hv)
lemma RentG.recycled (p:Π' 1 S f)(q:2*proceed (tent Y h) n d≤(side Y i0 s).val):Π' (4*n) (terrace (K:=Kₜ) a d n S) (CarrierF a d n f):=by
 have he:=RentG.jacket Y h a s i0 x p (by omega:proceed Kₜ n d≤ (N).val); let z:= (proceed Kₜ n d:ℤ); let T:=blanket a d n (K:=Kₜ) S; have ht:=RentG.fireW Y h a s i0 z he; have hx:= blanket_on a d n S x q; rw [show 4*n=2*n+2*n from by omega]; exact RentG.join Y h s i0 he ht (seat_separate a (N) (y:=z) hx hx)
omit x
section
variable {n0 M₀ S₁:Side}(Q0:Contract n0) {U V:Support (More n0)}{A B₀:Mark n0}{u t:ℕ}
local notation "Ω"=>Q0.art
include Q0
lemma seamV (y':Margin S₁ r k w u)(h:Mirror M₀ u n0 U A V B₀ n)(g:Q0.art j U A) : Q0.art (j*n) V B₀ := by
 induction h generalizing j with
 | self => simpa using g
 | @grow S F a z b0=>
   let T:= Heat.gaugeShift M₀ z; have he:Disjoint (S.image ((Buffered.plane a T).anon n0)) S:= by
      refine Finset.disjoint_left.mpr ?_; intro y e f; have he:= margin_separate a T y' y y (Finset.image_subset_image (f:=(Buffered.plane a T).anon n0) b0 e) (b0 f); simp at he
   rw [mul_two]; exact Q0.both (Q0.turn a T g) g he
 | @trans _ _ _ _ _ _ m s e h a b => rw [←mul_assoc]; exact b (a g)
end
end Gamer
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Gamer
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
private lemma metX (p: Ferry Y s i k) : Journey.Metered Kx (momentm Y i s) (deltaL Y h i s) (Journey.solder Y i k p.depth s ∘ ship (terrain Y h (Y.ir i) s)) (duetCharge Y s) := by
    have he:= boxprice Y h i k p.depth s p.fire p.enters
    rw [show (Journey.solder Y i k p.depth s ∘ ship (terrain Y h (Y.ir i) s))=collector Y h i k p.depth s from funext fun x=>(congrArg (Journey.solder Y i k p.depth s) (ship_eq (terrain Y h (Y.ir i) s) x))]; exact he
omit h in
private lemma frostXx (A:ℝ)(p:0≤A)(ε:ℝ)(e:0<ε) :∀ᶠ k in atTop, ∀ v:(Y.voyage i).kick ≤ k, ∀ x:Mark Ω, Envelope x→ (∀ i,‖x i‖ ≤ A)→ ‖(Ψ k) x-Journey.solder Y i k v s x‖ ≤ ε:=by
 have hz:0<A+1:=by linarith
 filter_upwards [Y.thaw s (ε/(A+1)) (by positivity)] with k t H x f b
 let W : Envelope (x ∘ drawn (S₀)):= mark_pay ((Y.voyage i).ownership s).paid.bill f
 exact le_trans (t i H (x ∘ drawn (S₀)) (A+1) W.meas (fun x=> le_trans (b _) (by linarith))) (div_mul_cancel₀ _ hz.ne').le

variable {t m n w d:ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT
abbrev PaperK (i k:ℕ)(W:Contract (side Y i s))( D θ: ℝ):Prop:=∀ (U:Support (More (side Y i s)))(n:ℕ)(y:Mark (side Y i s)), W.art n U y → ‖Journey.compass Y i k s y‖ ≤ D^n *Real.exp (θ*Rate.sites (side Y i s))
variable (a:Axis) {f x:W (tent Y h)}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ} (K:Universal Y h u v I E) {C₀:ℝ}
local notation "ℓ"=> reserve Λ l
variable (S:Finset Cover) {T:Axis→ℕ}
local notation "V₀"=> momentm Y i s
--local notation "X"=> stops Y h s i d -- bind variable X shadows errors below; remove
private lemma castPurchase {N M:Side}(e:N=M)(x:Mark N){C:ℝ}(v:∀ z,‖x z‖≤ C):∀ z,‖ship e x z‖ ≤ C:=by subst M; exact v
private lemma castPurchase' {N M:Side}(e:N=M)(x:Mark N){C:ℝ}(v:∀ z, ‖ship e x z‖≤ C):∀ z,‖x z‖ ≤ C:= by subst M; exact v
include K
lemma stagM (g:0<d) (t:Studio a 0 (yard Kx d) (reserve Λ l) S)(M: ∀ i:Axis,i≠ a→ ∃ b:ℤ,film b (T i) S i)
 (e:yard Kx d≤2*(T a+addgap Kx)) (q: ∀ j∈ univ.erase a,T j+addgap Kx ≤ (Ω).val)(w: 0< stops Y h s i d) (b0:0 ≤ C₀)(a0:0 ≤ C)(a1:0 ≤ θ)(v0:C₀*Real.exp (θ*capR Kx T) ≤ 1): ∀ᶠ k:ℕ in atTop, ∀ (F:Contract Ω)(f:W (tent Y h))(p:Locator (tent Y h) f S), (∀ z, ‖sold Y h s i f.val z‖≤ C)→ RentG Y h s i F 1 S f → PaperK Y s i (v k) F C₀ θ → Credential Y h s i (v k) a d 3 f :=by
 have hf := terrain Y h (Y.ir i) s; have ht:= stops_p Y h s i d g
 let n:=stops Y h s i d; obtain ⟨Δ,hx,he,pr⟩:= Mansion (T:=S) hf.symm w ht e (hf.symm ▸ q) M; let U:=terrace a d n S (K:=Kx); let t' := (v:ℕ→ℕ); let Y':= Real.exp (θ* capR Kx T); let Z':=4*n
 let x:=4*n*Δ; have htn (k):s≤ Y.uv k→ s≤ Y.uv k:=fun p=>p -- remove
 have he':C₀^x * Real.exp (θ* Rate.sites (Ω)) ≤ 1:=by
    have hz:(C₀*Y')^x ≤ (1:ℝ):= pow_le_one₀ (by unfold Y'; positivity) v0
    apply le_trans _ hz; change _≤ (C₀*Y')^x; rw [mul_pow]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg b0 _); unfold Y'; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; change Rate.sites (Ω)≤ ↑x*capR Kx T at he; nlinarith only [mul_le_mul_of_nonneg_left he a1]
 filter_upwards [K.pick.pass Y h s i, K.pick.grow_k.tendsto_atTop.eventually (frostXx Y s i (C^x) (pow_nonneg a0 _) 1 one_pos), K.pick.grow_k.tendsto_atTop.eventually (frostXx Y s i (C^Z') (pow_nonneg a0 _) 1 one_pos)] with k P F' Ft F f p z tK L
 let J:= CarrierF a d n f; let Fx:= sold Y h s i J.val; let W':=region U (Ω); have hv:AtSupport false W' Fx:= sold_affair Y h U s i (vigilant a d n S f p); have hz:= diligent Kx V₀ a d n f C (castPurchase' hf (f.val V₀) z); have hy:∀ z,‖Fx z‖ ≤ C^Z':= castPurchase hf (J.val V₀) hz
 obtain ⟨S',y,U'⟩:= pr Fx
 have hw:2*proceed Kx n d≤(Ω).val:=  by rw [show Ω= (Kx).c (V₀) from hf.symm]; exact ht.lower
 have h': F.art x S' y:= seamV F (Journey.prepared Λ l) U' (RentG.recycled Y h a s i t tK hw)
 have hh:‖(Ψ (v k)) y‖ ≤ 1:= (L _ _ _ h').trans he'
 let X0:= Journey.solder Y i (v k) P.depth s
 have hs := F' P.depth y (U'.covers hv).env (by unfold x; rw [pow_mul]; exact U'.cost hy); have h2: ‖X0 y‖ ≤ 2:=by rw [norm_sub_rev] at hs; linarith only [(show ‖X0 y‖-‖(Ψ (v k)) y‖ ≤ 1 from (norm_sub_norm_le ..).trans hs), hh]; -- orientation
 have hC: ‖X0 Fx‖ ≤ 2:= le_of_pow_le_pow_left₀ hx.ne' (by norm_num) ((Mirror.heat hf.symm U' (metX Y s i _ h P) hv).trans (h2.trans (le_self_pow₀ (by norm_num) hx.ne')))
 unfold Credential; rw [sold_sharp]; change ‖(Ψ (v k)) Fx‖ ≤ 3; have h:= Ft P.depth Fx hv.env hy; linarith only [hC,(show ‖(Ψ (v k)) Fx‖-‖X0 Fx‖≤ 1 from (norm_sub_norm_le ..).trans h)]
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Gamer

namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Gamer
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
open Eight YM.SU5.FiniteGaugeData.CodaT
include K R A
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
theorem cashCpp (a:Axis)(p:∀ i,∃ b:ℤ,film b (vD i) S i) (c:0≤C)(k0:0≤C₀)(e:0<ε)(c':0≤θ)(p0:C₀*Real.exp (θ*capR Kₜ vD) ≤1): ∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,∀ (F:Contract (side Y (u i) s))(f:W (tent Y h))(p:Locator (tent Y h) f S), (∀ z, ‖sold Y h s (u i) f.val z‖≤ C) → RentG Y h s (u i) F 1 S f → PaperK Y s (u i) (v k) F C₀ θ→∀ (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ), Sphere Y h K R A Φ→ ‖Φ s f‖≤1+ε:=by
 obtain ⟨z,P,t,H_p,t'⟩:= Eight.duty (K:=Kₜ) (p a).choose_spec; let T':=hour Kₜ S a z; have hz:Studio a 0 (yard Kₜ P) (reserve Λ l) T':=H_p; let v0:=v
 filter_upwards [rimH (vD:=vD) (a:=a) Y h K R A s u K.pick.grow_i t, highroad Y h K R A T' s hz t c e] with i j t_
 filter_upwards [t_,stagM Y s (u i) h a K T' t hz (fun i u=> Exists.intro _ ((p i).choose_spec.tick u.symm z)) t' j.1 j.2 k0 c c' p0] with k G HP F f s' w pF cF Φ Jx
 rw [← Jx.color s a f z]; let hF:=loc_tic Kₜ S a z s'; have hk:=sell_t Y h s (u i) (a:=a) (f:=f) z w; exact G _ hF hk (HP F _ hF hk (RentG.tickW Y h a s (u i) z pF) cF) Φ Jx
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Gamer
