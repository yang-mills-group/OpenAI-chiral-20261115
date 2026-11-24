import YM.SU5.FiniteGaugeData.SalonG.Coupon
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
variable (a:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (x:W (tent Y h))(t:Locator (tent Y h) x T)(r:Ahead a 0 (reserve Λ l) T) (f:W (tent Y h))
variable (B₁ B₂ ε:ℝ)
variable (g:0<d)(v':Studio a 0 (yard (tent Y h) d) (reserve Λ l) S)
include W' t r v' g R
local notation "N"=> ((tent Y h).c (momentm Y i s))
local notation "d'"=> energyS Λ d n
local notation "Ω"=>EchoF Y h a (energyS Λ d n)
local notation "ν"=> momentm Y i (s+n)
local notation "F" f:max=> ascended Y h s W' R n f
local notation "X"=> upperHours Y h T s d n x t
omit W' R t r v' g in
private lemma cost_eval {x y:ℂ}{p:ℝ}(H:‖x-y‖≤p): x.re ≤ y.re+p:= by
 have he:= (Complex.re_le_norm (x-y)).trans H; rw [Complex.sub_re] at he; linarith -- omit variables
omit W' R t r v' g
lemma Echo_const (y:W (tent Y h)): EchoF Y h a d 0 x f=EchoF Y h a d 0 x y:=by simp only [EchoF,open_small]
include W' R t r v' g
theorem issuance (p:0<ε)(q:0 ≤ B₂) : ∀ᶠ i in atTop, ∀ᶠ k in atTop,∀ (f:W Kₜ) (e:Locator (tent Y h) f S), ‖reading Kₜ S f e‖≤ B₂ → Credential Y h s (u i) (v k) a d B₁ f→
    (E (s+n) (EchoF Y h a (energyS Λ d n) 1 x (ascended Y h s W' R n f)).val).re ≤ (E (s+n) (EchoF Y h a (energyS Λ d n) 0 x (ascended Y h s W' R n f)).val).re + ε := by
 let b:=B₂+1; have hb:0<b:=by unfold b; positivity
 have he:0< ε/3:=by positivity
 let C:= (X) B₁; let V(i:ℕ):ℝ:= ↑(stops Y h s (u i) d)
 have hv:Tendsto V atTop atTop:= tendsto_natCast_atTop_atTop.comp ((stops_grow Y h s d g).comp W'.pick.grow_i.tendsto_atTop)
 filter_upwards [((c_grows Kₜ).comp ((momentum Y (s+n)).comp W'.pick.grow_i.tendsto_atTop)).eventually_ge_atTop (endurance Kₜ (Ran Kₜ (d:=energyS Λ d n) (T:=T))),streams Y h S s n W' R ε p,hv.eventually_gt_atTop (max 0 (C/(ε/3))),zoom_phase a Y h S T s W' R d n x t ((ε/3)/b/b) (by positivity), coal_point Y h (s+n) W' ((Ω) 0 x 1) (ε/3) he] with i ht u' V' e p0
 let T':∀ᶠ k:ℕ in atTop,legacy Y (u i) (v k):= cadence Y v W'.pick.grow_k (u i)
 filter_upwards [uniformPhase Y h S T s a d n W' x t r B₁ B₂ g v' (u i) (T'.mono (fun k e=> (u' k e).1)) ht q,T'] with k t' t₁ f w q' Z
 let h' (i':ℕ):= hot Y h (s+n) (u i) (v k) ((Ω) i' x (Passenger Y h S s (u i) (v k) n f w)).val
 let y (i:ℕ):= E (s+n) ((Ω) i x (F f)).val
 have hh: ‖h' 0-y 0‖≤ ε/3:= by unfold h' y; rw [Echo_const Y h a d' x _ 1, Echo_const Y h a d' x (F f) 1]; exact p0 k t₁
 have hg: ‖h' 1-y 1‖≤ ε/3:= by
    let f':= reading Kₜ S f w; have hx:= e k t₁ f'; rw [satisfied a Y h _ _ s _ _ d n x t f w t'.1,satisfyE a Y h _ _ s W' R d n x t f w] at hx;
    refine hx.trans (le_trans ?_ (show (ε/3/b/b)*b*b ≤ ε/3 from le_of_eq (by rw [div_mul_cancel₀ _ hb.ne', div_mul_cancel₀ _ hb.ne']))); apply mul_le_mul _ (by unfold b; linarith : ‖f'‖≤ b) (norm_nonneg _) (by positivity); apply mul_le_mul_of_nonneg_left _ (by positivity); exact q'.trans (by unfold b; linarith)
 have h₀: V i *((h' 1).re-(h' 0).re) ≤ C:= t'.2 f w q' Z
 obtain ⟨hp0,t₂⟩:= max_lt_iff.mp V'; have hx:= (div_lt_iff₀ he).1 t₂
 have h_ : (h' 1).re-(h' 0).re ≤ ε/3:=by nlinarith -- let h q
 have hz':= cost_eval hh -- arg mess; omit
 rw [norm_sub_rev] at hg; have hz:= cost_eval hg;
 change (y 1).re≤ (y 0).re+ε; linarith
#print axioms issuance

-- frequent credential in a cone.L.For exact f
abbrev Gallery (u v:ℕ→ℕ)(f:W (tent Y h)) :Prop:= ∃ B:ℝ, ∃ᶠ i in atTop, ∃ᶠ k in atTop, Credential Y h s (u i) (v k) a d B f
omit R t r v' in
lemma admit_low (e:Locator (tent Y h) f S)(p:SalonG.Width (tent Y h) f (drift Kₜ S d (duetCharge Y s))): Gallery Y h s a d u v f:=⟨2,((loadSmall Y h S s a d W' g).mono fun i v=> (v.mono (fun k t=>t f e (p _))).frequently).frequently⟩ -- tune role
lemma abroad (p:Gallery Y h s a d u v f)(e:Locator Kₜ f S) :
    (E (s+n) (EchoF Y h a (energyS Λ d n) 1 x (ascended Y h s W' R n f)).val).re ≤ (E (s+n) (EchoF Y h a (energyS Λ d n) 0 x (ascended Y h s W' R n f)).val).re:= by
 apply le_of_forall_pos_le_add
 intro ε h'
 obtain ⟨B,v⟩:=p; obtain ⟨i,p,f'⟩:= (v.and_eventually (issuance Y h S T s a d n W' R x t r B ‖reading Kₜ S f e‖ ε g v' h' (norm_nonneg _))).exists; obtain ⟨k,e',u⟩:= (p.and_eventually f').exists; exact u f e le_rfl e'
#print axioms abroad
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
