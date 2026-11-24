import YM.SU5.Reconstruction.AllGrades.Caption
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice.Session
open Function Set Filter MeasureTheory Spectral Analysis InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket Roy
variable {H W:Hilbert} {a: Axis} {Γ: AddSubgroup ℝ} (K: OS.Semigroup H a)(T:Germ.Alliance (CF.Buffered.Afterglow.Tower.Trans a) Γ H)(S:OS.Semigroup W a)
local notation "U" j:max v:max=> (T.crew j).play v

local notation "S₀"=> Coupon a Γ
abbrev sun (a:Axis){Γ : AddSubgroup ℝ}(i: CF.Buffered.Afterglow.Tower.Trans a)(v t:Γ)(p:0 ≤ (t:ℝ)): Coupon a Γ:= ⟨Function.update (Function.update (0:Axis→Γ) a t) i.val v, by simpa [i.property.symm]⟩
variable (i:CF.Buffered.Afterglow.Tower.Trans a) (v t : Γ) (p:0 ≤ (t:ℝ))
noncomputable def catalog : Sunbelt a Γ H:= ⟨T,look a,look_all a,look_one a,K.E,K.continuousE,fun x=> by simp_rw[K.sym]; exact K.continuousE _⟩
local notation "R"=>sun a i v t p
local notation "cr"=> cross a i.val i.property
local notation "toℝ" p:max=> (p:ℝ).toNNReal
lemma sun_time : (R).dt=(toℝ t):=by simp [Coupon.dt,sun, i.property.symm]
lemma sun_space : (R).displacement = (v:ℝ) • cr:=by -- spotlight2 uses T or new T; no need
 apply Subtype.ext; ext j; by_cases h:j=a
 · subst j; rw [show (R).displacement.val a=0 from (Coupon.displacement _).property,show ((v:ℝ) • cr :OS.Cross a).val a=0 from ((v:ℝ) • cr : Cross a).property]
 rw [Coupon.displacement, diameter_at (face _) _ h]; by_cases q:j=i.val <;> simp_all [face,sun,cross]
lemma sun_crew: Live K T (R)= K.E (toℝ t)* (U i v):=by rw [Live,sun_time]; exact congrArg _ (show _= _ from (spotlight2 (catalog K T) t i v).2.2)
lemma sun_cash: Coupon.cash S (R)= S.E (toℝ t) * S.U ((v:ℝ) • cr):=by rw [Coupon.cash,sun_time,sun_space]
include p in
private lemma halfr: Real.toNNReal ((t+t:Γ):ℝ)= (toℝ t)+(toℝ t):=by rw [AddSubgroup.coe_add, Real.toNNReal_add p p]
local notation "KlA"=>sun a i 0 t p
local notation "KlB"=>sun a i 0 (t+t) (show 0≤_ from add_nonneg p p)
local notation "KlC"=>sun a i v (t+t) (show 0≤_ from add_nonneg p p)
local notation "KlD"=>sun a i (0:Γ) 0 le_rfl
local notation "KlE"=> sun a i v 0 le_rfl -- unused
-- show formula E*U and distortion in Population using Picket.tension.
noncomputable def meterBill(f: S₀→ℂ):ℝ:=2*((f KlB).re-(f KlC).re)-((f KlD).re-2*(f KlA).re+(f KlB).re)
-- custom zero notation x; whitespace tune.SM.Re.
lemma genuine (x:W) : let a:=S.E (toℝ t) x; meterBill i v t p (Coupon.tagT S x)= ‖S.U ((v:ℝ) • cr) a-a‖^2 - ‖x-a‖^2:=by
 intro a'; unfold meterBill Coupon.tagT; simp only [sun_cash,halfr t p,AddSubgroup.coe_zero,zero_smul, S.uZero,Real.toNNReal_zero, S.eZero]; change 2*((inner ℂ x (S.E _ (x))).re - (inner ℂ x (S.E ((toℝ t)+(toℝ t)) (S.U _ x))).re)-((inner ℂ x x).re-2*(inner ℂ x a').re+(inner ℂ x (S.E ((toℝ t)+(toℝ t)) x)).re)= _
 let r:= S.U ((v:ℝ) • cr); let f:=S.E (toℝ t)
 have ht: inner ℂ (f x) (r (f x))=inner ℂ x (S.E ((toℝ t)+(toℝ t)) (S.U ((v:ℝ) • cr) x)):=by rw [S.time]; change inner ℂ (S.E _ x) (S.U _ (S.E _ x))= _; rw [show S.U ((v:ℝ) • cr) (f x)=f (r x) from DFunLike.congr_fun (S.independent (toℝ t) _) x|>.symm, S.swing]; rfl -- swing order and f let
 have h: inner ℂ (f x) (f x)= inner ℂ x (S.E ((toℝ t)+(toℝ t)) x):=by rw [S.time]; exact S.swing ..
 rw [←h,←ht,norm_sub_rev (S.U _ _),norm_sub_sq (𝕜:=ℂ),norm_sub_sq (𝕜:=ℂ),S.unitary]; have v2(y:W) : (inner ℂ y y).re=‖y‖^2:= inner_self_eq_norm_sq (𝕜:=ℂ) y; rw [v2,v2]; change 2*(‖a'‖^2-(inner ℂ a' (r a')).re) - (‖x‖^2 - 2*(inner ℂ x a').re +‖a'‖^2)= ‖a'‖^2 - 2*(inner ℂ a' (r a')).re + ‖a'‖^2- (‖x‖^2 - 2*(inner ℂ x a').re+‖a'‖^2); ring
lemma bill_safe (h:|(v:ℝ)| ≤ (t:ℝ))(e:Forward S)(f:S₀→ℂ)(hz:f ∈ Coupon.Population S Γ):meterBill i v t p f ≤ 0:=by
 have H₁: Continuous (meterBill i v t p):=by unfold meterBill; fun_prop
 apply closure_minimal (t:={f|meterBill i v t p f≤0}) ?_ (isClosed_le H₁ continuous_const) hz
 rintro f ⟨x,rfl⟩; change meterBill _ _ _ _ _≤_; rw [genuine]; apply sub_nonpos.mpr; refine pow_le_pow_left₀ (norm_nonneg _) (tension_bill S x ?_ e) 2
 rw [norm_smul, show ‖cross a i.val i.property‖=1 from (by change ‖basis i.val‖=1; simp),mul_one, Real.coe_toNNReal _ p]
 simpa [Real.norm_eq_abs] using h
-- later actual implication

end YM.ConePrice.Session
#print axioms YM.ConePrice.Session.bill_safe
