import YM.SU5.FiniteGaugeData.Tower.Recharge
import YM.SU5.FiniteGaugeData.Tower.Unaxis
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
/-!
# Pay every final assembly (pure central charge)

At angles D issue this at any fixed further rung. Clipping chosen BEFORE
operator subsequence as in Recharge. Numeric exponent not optimized, still
exactly independent of that rung. No continuity vs spatial movement. And
no charge of C^n at the further rung made independent of rung; that
exponential is paid by thaw tuning at a fixed rung as period grows.
-/
section soft
variable {K:Calibration}

lemma main_bill (j:Axis)(w v:ℤ)(n:ℕ){F:Family K}(t:TestFamily K true F){C:ℝ}(h:pay F C):TestFamily K true (banner j w v n F) ∧ pay (banner j w v n F) (C^(4*n)):=by
 let z:=lace K j w F 1 n; let k:=chambers j w v F 1 n
 have x:=lace_paid K j w t (aux_test (S:=∅) InTest.one) n
 have a:TestFamily K true k:=move_ok K j v ((reflect_ok K j 0 x).mul x)
 have hx:pay z (C^n):= by simpa using lace_cost K j w C 1 h (show pay 1 1 from fun i v=> (norm_one : ‖(1:FC (Single (K.c i)))‖=1).le) n
 have hi:pay k (C^n*C^n):=chime_pay K j _ _ (pay_mul (pay_flips K hx j 0) hx)
 have hat:= And.intro ((reflect_ok K j (gaugeT K (cliff w v n)) a).mul a) (pay_mul (pay_flips K hi j (gaugeT K (cliff w v n))) hi); exact (show (C^n*C^n) * (C^n*C^n)=C^(4*n) by ring) ▸ hat

-- flat numeric (allow width P fixed, denominator charge fixed). billing at end n.
-- actually P consumed cubic width (2*(d+)^3); use here
private lemma suppressed {F:ℕ→ℕ}(v:Tendsto F atTop atTop)(q:ℝ)(x:0≤q): ∀ᶠ i in atTop,∀n:ℕ,n ≤ F i→ Real.exp (-((F i:ℕ):ℝ)^2)*(q^(4*n)) ≤ 1:=by
 obtain ⟨N,p⟩:= exists_nat_gt (4*q)
 filter_upwards [v.eventually_ge_atTop N] with i u n t
 have h₁ : q ≤ Real.exp q:= le_trans (by linarith : q ≤ q+1) (Real.add_one_le_exp q)
 calc _ ≤ Real.exp (-((F i:ℕ):ℝ)^2)* (Real.exp q)^(4*n) := by gcongr
      _ = Real.exp (-((F i:ℕ):ℝ)^2+(4*n:ℕ)*q):= by rw [Real.exp_add, Real.exp_nat_mul]
      _ ≤ 1:=by
         apply Real.exp_le_one_iff.mpr; have h₂:(4*n:ℕ) ≤4*F i:=by omega
         have h₃:(N:ℝ) ≤ (F i:ℕ):=by exact_mod_cast u
         push_cast
         have h₄:(n:ℝ) ≤ (F i:ℕ):=by exact_mod_cast t
         nlinarith
end soft

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis)(w:ℕ)(f:Family (tent Y H))(S:Finset Cover)(t:InTest (tent Y H) true S false f)(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
local notation "Z" u:max r:max=> train Y H s u (π r) (ζ r) S f
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
local notation "b₀"=>ruler Λ.block
variable (Qt : Clipped Y H (i∘a) (k∘b))(hw:0 < w)
include V Q
lemma site_law(s:ℕ): Tendsto (fun r=>(T₀ (π r) s).val) atTop atTop := (goes Y H s).comp (V.pick.grow_i.comp Q.growsA|>.tendsto_atTop)
include Qt
lemma plate (s:ℕ)(C:ℝ)(h:0≤C): ∀ᶠ e:ℕ in atTop,∀ n≤(T₀ (π e) s).val,∀ f:Family K,TestFamily K true f→ pay f (C^(4*n))→
 ‖sharp Y H s (π e) (ζ e) f-hot Y H s (π e) (ζ e) f‖ ≤ 1:=by
 filter_upwards [suppressed (site_law Y H V Q s) C h,Qt s] with i a b n t f p h; exact (b p _ h).trans (a n t)
include t hB hw
lemma cost_homestead (x:ℝ)(C:Axis→ℤ)(d:ℕ)(h:Transom j S C d)(he:pay f x):
 ∀ᶠ e:ℕ in atTop,∀ n:ℕ,∀ u:ℤ,
 ‖hot Y H s (π e) (ζ e) (banner j w u n f)‖ ≤ Real.exp ((duetCharge Y s)*(((2*(d+addgap K):ℕ):ℝ)^3)*((m (π e) s).val:ℝ))* (x^(4*n)):=by
 have hM:=site_law Y H V Q s
 filter_upwards [Q.finance s,hM.eventually_ge_atTop (d+addgap K)] with i p v n u
 obtain ⟨D,x₀,t₀,h₀⟩:= centerpiece j w u n C d (show (0:ℤ) ≤ w from by positivity) t hB h
 obtain ⟨i₀,Cs⟩:= main_bill j w u n (aux_test t) he
 set c:=gaugeT K (cliff (w:ℤ) u n)
 let z:=reflectedBox j c D
 have h₂: Transom j (z∪D) C d:= trans_union j (h₀.mirro j c) h₀
 unfold hot; rw [dif_pos p.depth]; rw [←side_register Y H] at v
 exact narrow (boxprice Y H _ _ p.depth s p.fire p.enters) j v (((axial K j c x₀).mono subset_union_left).mul (x₀.mono subset_union_right)) h₂ (x^(4*n)) Cs

lemma pure_cap:∃ c:ℝ,0<c ∧ ∀ r:ℕ,
 ∀ᶠ e:ℕ in atTop,∀ n:ℕ,∀ v:ℤ,
 0<n→2*(b₀*w*n) ≤ (((T₀ (π e) s).val:ℕ):ℤ)→(((T₀ (π e) s).val:ℕ):ℤ) ≤ (4*(b₀*w*n))→
 ‖hot Y H (s+r) (π e) (ζ e) (banner j (uM r) ((L₀:ℤ)^r*v) n (Z r e))‖ ≤ c^(2*n):=by
 obtain ⟨x,h⟩:=Journey.valuation Y H t; have Hv:pay f x:=h; have hx:=pay_nonneg Hv
 obtain ⟨C,d,hc,hT⟩:=trans_exists j S
 let p:= (2*(d+addgap K):ℕ)^3
 let c:= 2*(1+Real.exp ((duetCharge Y s)*(4*(16*Λ.block.val*w)*p:ℕ))*x^4)
 have ht:(0:ℝ) < c:=by unfold c; positivity
 refine ⟨c,ht,fun r=>?_⟩
 have hs:0≤duetCharge Y s:=duetCharge_nn Y s
 let M(i':ℕ):=(T₀ (π i') (s+r)).val
 obtain ⟨A,p₀,Tp⟩:=fares Y H s Q S r
 have he:= mul_nonneg p₀.le hx
 filter_upwards [cost_homestead Y H V s Q j w f S t hB Qt hw x C d hT Hv,Tp 1 zero_lt_one, plate Y H V Q Qt s x hx, plate Y H V Q Qt (s+r) (A*x) he,banner_drop Y H V s Q j t hB r] with i z a b₁ b₂ g n v Hn P y
 let c' := (T₀ (π i) s).val
 let F:=banner j (uM r) ((L₀:ℤ)^r*v) n (Z r i); let f':= banner j w v n f
 have hr: 1≤ b₀*w:= by have hv:0<(w:ℤ):=by exact_mod_cast hw
                       have hf:=ruler_gene Λ.block; nlinarith
 have hu₁:n ≤ c':=by
    change _ ≤ (c':ℤ) at P; zify; nlinarith [mul_le_mul_of_nonneg_right hr (show 0≤(n:ℤ) by positivity)]
 have hu₂:n ≤ M i:=hu₁.trans (by unfold M c'; rw [refine_side Y]; exact Nat.le_mul_of_pos_left _ (pow_pos Λ.R.L.property r))
 obtain ⟨c₀,k₁⟩:= main_bill j w v n (aux_test t) Hv
 obtain ⟨g₀,k₂⟩:=main_bill j (uM r) ((L₀:ℤ)^r*v) n (aux_test (prepared_train Y H s S r _ _ t)) ((a f t _ Hv).2.1)
 let G:= hot Y H s (π i) (ζ i) f'
 let g':=hot Y H (s+r) (π i) (ζ i) F
 have hb:=b₁ _ hu₁ _ c₀ k₁; have hB':=b₂ _ hu₂ _ g₀ k₂
 have hi: ‖g'‖ ≤ ‖G‖+1+1:=by
    have hz:=g n v P
    have h₁:= norm_sub_norm_le (hot Y H (s+r) (π i) (ζ i) F) (sharp Y H (s+r) (π i) (ζ i) F)
    have h₂:= norm_sub_norm_le (sharp Y H s (π i) (ζ i) f') G
    rw [norm_sub_rev] at h₁
    -- hz rewrite only norm price on lhs result after composing thaw
    have hg:=h₁.trans hB'; rw [show sharp _ _ (s+r) _ _ F=_ from hz] at hg
    have hh:=h₂.trans (show _ from hb); change _-‖hot Y H s _ _ _‖ ≤1 at hh; unfold g' G; unfold F f' at *; linarith
 refine hi.trans ((add_le_add_left (add_le_add_left (z n v) 1) 1).trans ?_)
 -- exp cubed p nat, pay m ≤ c' ≤4b n. reduce
 have ha : (m (π i) s).val ≤ 4*(16*Λ.block.val*w)*n:=by
    refine (moment_le Y H (π i) s).trans ?_
    unfold ruler at y
    zify
    push_cast
    -- cast unfolds Ctor side; pin annotation
    exact_mod_cast (show (((T₀ (π i) s).val:ℕ):ℤ) ≤ ((4*(16*Λ.block.val*w)*n:ℕ):ℤ) from (by push_cast; push_cast at y; nlinarith only [y]))
 let T:=4*(16*Λ.block.val*w)
 let D':=duetCharge Y s
 let b:=Real.exp (D'*(T*p:ℕ))*x^4
 have hp : Real.exp (D'*(((2*(d+addgap (tent Y H)):ℕ):ℝ)^3)*((m (π i) s).val:ℝ))*(x^(4*n)) ≤ b^n:=by
    rw [show (x:ℝ)^(4*n)=(x^4)^n from pow_mul .., show b^n = _ * _ from mul_pow ..]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (pow_nonneg hx _) _)
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    have hr:(((m (π i) s).val:ℕ):ℝ) ≤ (T:ℕ) * (n:ℝ):=by exact_mod_cast ha
    have h': (p:ℝ) = (((2*(d+addgap K):ℕ):ℝ)^3):= by unfold p; rw [Nat.cast_pow]
    rw [←h']; change D'* (p:ℝ)* _ ≤ _; rw [Nat.cast_mul]; have hn:0≤D'*(p:ℝ):=by unfold D'; positivity
    nlinarith [mul_le_mul_of_nonneg_left hr hn]
 have hb:0≤b:=by unfold b; positivity
 let z:=(1+b)
 have hb0:1 ≤ z:=by unfold z; linarith
 have hB:b^n≤ z^(2*n):=le_trans (pow_le_pow_left₀ hb (le_add_of_nonneg_left zero_le_one) n) (pow_le_pow_right₀ hb0 (by omega))
 have hz : 1≤ z^(2*n):= one_le_pow₀ hb0
 have hk0:(4:ℝ) ≤2^(2*n):=calc (4:ℝ)=2^2:=by norm_num
                                _ ≤2^(2*n):=pow_le_pow_right₀ (by norm_num) (by omega)
 change _ ≤ (2*z)^(2*n); rw [mul_pow]; change Real.exp (D'*(((2*(d+addgap (tent Y H)):ℕ):ℝ)^3)*((m (π i) s).val:ℝ))*(x^(4*n))+1+1 ≤ _
 nlinarith [mul_le_mul_of_nonneg_right hk0 (zero_le_one.trans hz)]
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.pure_cap
