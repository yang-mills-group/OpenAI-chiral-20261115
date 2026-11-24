import SatinFixedContrastNovember4
import YM.SU5.Thin.HeightBounds

/-!
# uniform power interpolation from native height

This is a VERY close variation on the supplied `PureCap`, `EndTrain`, `Baggage`.
Insert our HeightBounds witness for the homestead test, then propagate that explicit
bound (need it in our uniform-in-height operator calculations later).
Preserve the original transfer and wages (only that one upper bound changed).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
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

def thinStand(P:Preparation)(X:Calibration)(w d:ℕ)(M γ:ℝ) :ℝ:= let p:= (2*(d+addgap X):ℕ)^3; 2*(1+Real.exp (γ*(4*(16*P.block.val*w)*p:ℕ))*M^4)
lemma standPos (P:Preparation)(X:Calibration)(w d:ℕ)(M γ:ℝ) : 0<thinStand P X w d M γ:=by unfold thinStand; positivity
variable (q:ℝ) (g0:0≤ q)(bg:PaidHeight (i:=i) (k:=k) (a:=a) (b:=b) Y H s q)(M0:ℝ)(hd0:pay f M0)(d0:ℕ)(X0:Axis→ℤ)(ht0:Transom j S X0 d0)
local notation "Bω"=> thinStand Λ K w d0 M0 q
include V Q t hB Qt hw g0 bg
lemma costHeight (x:ℝ)(C:Axis→ℤ)(d:ℕ)(h:Transom j S C d)(he:pay f x):
 ∀ᶠ e:ℕ in atTop,∀ n:ℕ,∀ u:ℤ,
 ‖hot Y H s (π e) (ζ e) (banner j w u n f)‖ ≤ Real.exp (q*(((2*(d+addgap K):ℕ):ℝ)^3)*((m (π e) s).val:ℝ))* (x^(4*n)):=by
 have hM:=site_law Y H V Q s
 filter_upwards [Q.finance s,hM.eventually_ge_atTop (d+addgap K),bg] with i p v heightTest n u
 obtain ⟨D,x₀,t₀,h₀⟩:= centerpiece j w u n C d (show (0:ℤ) ≤ w from by positivity) t hB h
 obtain ⟨i₀,Cs⟩:= main_bill j w u n (aux_test t) he
 set c:=gaugeT K (cliff (w:ℤ) u n)
 let z:=reflectedBox j c D
 have h₂: Transom j (z∪D) C d:= trans_union j (h₀.mirro j c) h₀
 unfold hot; rw [dif_pos p.depth]; rw [←side_register Y H] at v
 exact narrowHeight (boxprice Y H _ _ p.depth s p.fire p.enters) j v (((axial K j c x₀).mono subset_union_left).mul (x₀.mono subset_union_right)) h₂ (x^(4*n)) Cs (heightTest p) g0

include hd0 ht0
lemma capHeight: ∀ r:ℕ,
 ∀ᶠ e:ℕ in atTop,∀ n:ℕ,∀ v:ℤ,
 0<n→2*(b₀*w*n) ≤ (((T₀ (π e) s).val:ℕ):ℤ)→(((T₀ (π e) s).val:ℕ):ℤ) ≤ (4*(b₀*w*n))→
 ‖hot Y H (s+r) (π e) (ζ e) (banner j (uM r) ((L₀:ℤ)^r*v) n (Z r e))‖ ≤ Bω ^(2*n):=by
 let x:=M0; let C:= X0; let d:=d0; have hT: Transom j S C d:=ht0; have Hv:pay f x:=hd0; have hx:=pay_nonneg Hv
 let p:= (2*(d+addgap K):ℕ)^3
 let c:= 2*(1+Real.exp (q*(4*(16*Λ.block.val*w)*p:ℕ))*x^4)
 have ht:(0:ℝ) < c:=by unfold c; positivity
 intro r
 have hs:0≤q:=g0
 let M(i':ℕ):=(T₀ (π i') (s+r)).val
 obtain ⟨A,p₀,Tp⟩:=fares Y H s Q S r
 have he:= mul_nonneg p₀.le hx
 filter_upwards [costHeight Y H V s Q j w f S t hB Qt hw q g0 bg x C d hT Hv,Tp 1 zero_lt_one, plate Y H V Q Qt s x hx, plate Y H V Q Qt (s+r) (A*x) he,banner_drop Y H V s Q j t hB r] with i z a b₁ b₂ g n v Hn P y
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
 let D':=q
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

omit V Q t hB Qt hw g0 bg hd0 ht0 in
private lemma thinCounter (n B:ℕ)(hB:0<B)(p:2*B≤n):
 let k:=finalN n B; 0 < k ∧ 2*B*k≤ n∧ n ≤ 2*B*k+2*B∧ n ≤ 4*B*k:=by
 intro k
 have h:0< k:= Nat.div_pos p (by positivity)
 have ht:=Nat.mod_add_div n (2*B); have he:=Nat.mod_lt n (by positivity:0<2*B); unfold k finalN at *
 obtain ⟨a,d⟩:= And.intro (by omega :2*B*(n/(2*B))≤n) (by omega : n<2*B*(n/(2*B))+2*B)
 exact ⟨h,a,d.le,(by nlinarith)⟩

lemma interpolateThin:∀ (r N:ℕ)(d:ℕ) (A:ℤ)(c:ℝ)(p':0≤A),∀ᶠ e:ℕ in atTop,
 ∀ n:ℕ,n≤ N→∀ (x:Family K) (X:Finset Cover), InTest K true X false x→Between (tent Y H) j (2*(b₀*(uM r))) A X→ CompactArc X d→pay x c→
 ‖hot Y H (s+r) (π e) (ζ e) (chambers j (uM r) 0 (Z r e) x n)‖ ≤ wages K (duetCharge Y (s+r)) d A c * Bω ^n:=by
 let C:= Bω; have y:0<C:=standPos ..; have qH:=capHeight Y H V s Q j w f S t hB Qt hw q g0 bg M0 hd0 d0 X0 ht0
 intro i' nT d R0 c hc
 let r:=i'; let z:= s+i'
 let N0(e:ℕ):= (T₀ (π e) s).val
 let Nr(e:ℕ):=(T₀ (π e) (s+r)).val
 obtain ⟨a0,hA⟩:=Journey.valuation Y H t
 obtain ⟨k',hF,v⟩:= fares Y H s Q S i'
 let u:ℕ:=16*Λ.block.val*w
 let p:ℕ:=uM i'
 have he':b₀*w=(u:ℕ):=by unfold u ruler; push_cast; rfl
 have hr:u>0:=by unfold u; have h:= Λ.block.property; positivity
 have hs: b₀*p=(↑(u*L₀^r):ℤ):=by unfold p; push_cast; rw [mul_left_comm,he']; ring
 let mant(e:ℕ):= (K).c (m (π e) z)
 have hg:Tendsto (fun e=>(mant e).val) atTop atTop:=by unfold mant;simp_rw [side_register]; exact site_law Y H V Q z
 filter_upwards [qH i', site_law Y H V Q s|>.eventually_ge_atTop (2*u*(1+nT)), hg.eventually_ge_atTop (widthPair K (rim_width R0 d)+addgap K), hg.eventually_ge_atTop (widthPair K d+addgap K),
     hg.eventually_ge_atTop (2*R0.toNat),v 1 zero_lt_one,Q.finance z] with j0 qp hj hR hD hv hh zf n hb x X t' hZ Dn hp
 let F:=Z i' j0
 have hB1:InTest K true (W i') false F:=prepared_train Y H s S i' (π j0) (ζ j0) t
 let N:= finalN (N0 j0) u
 let H0:= mant j0
 have hP: H0.val=L₀^r*N0 j0:=by unfold H0 mant; rw [side_register,refine_side]
 obtain ⟨hN,hM,hE,HM⟩:=thinCounter (N0 j0) u hr (by
    change _ ≤ N0 j0; exact le_trans (Nat.le_mul_of_pos_right _ (by omega:0<1+nT)) hj)
 change 0 < N at hN; change 2*u*N≤ N0 j0 at hM; change N0 j0≤2*u*N+2*u at hE; change N0 j0≤ 4*u*N at HM
 have hL:2*(b₀*(p:ℕ)*(N:ℕ)) ≤ ((H0.val:ℕ):ℤ):=by
    rw [hs,hP,Nat.cast_mul]
    calc _= (↑(L₀^r:ℕ):ℤ)*((2*u*N:ℕ):ℤ):=by push_cast; ring
         _≤ (↑(L₀^r:ℕ):ℤ) * ↑(N0 j0):=by exact mul_le_mul_of_nonneg_left (by exact_mod_cast hM) (by positivity)
         _ = _:= by norm_cast
 have hL': (((H0.val):ℕ):ℤ) ≤ 2*(b₀*(p:ℕ)*(N:ℕ))+2*(b₀*(p:ℕ)):=by
    rw [hP,hs,Nat.cast_mul]
    calc _≤ (↑(L₀^r:ℕ):ℤ)*((2*u*N+2*u:ℕ):ℤ):=by gcongr
         _=_:=by push_cast; ring
 have hv':R0+(b₀*(p:ℕ)*(N:ℕ))≤ ((H0.val:ℕ):ℤ):=by
    have h:2*R0.toNat≤ (H0.val:ℕ):=hv; have ht:(2*R0.toNat:ℕ)≤ ((H0.val:ℕ):ℤ):=by exact_mod_cast h
    have hh:2*R0 ≤ ((H0.val:ℕ):ℤ):=by omega
    linarith
 have hT:Between (tent Y H) j (0:ℤ) (b₀*(p:ℕ)) (W i'):=by unfold p; rw [Nat.cast_mul,Nat.cast_pow,mul_left_comm]; exact expands_shape Y H hB i'
 have hpp:0 < (p:ℤ):=by unfold p; have hb:0< Λ.R.L.val:=Λ.R.L.property; positivity
 -- casts: uM occurs polymorphic in qp: because w : Nat and casts forced by banner, exponent powers INT!
 have ht(j':ℤ): ‖hot Y H z (π j0) (ζ j0) (banner j (p:ℕ) ((p:ℤ)*j') N F)‖ ≤ C^(2*N) := by
    unfold p F
    push_cast; rw [mul_assoc (↑L₀^i':ℤ)]
    apply qp N ((w:ℤ)*j') hN
    · rw [mul_assoc, ←mul_assoc b₀, he'] -- bad
      rw [←mul_assoc]; exact_mod_cast hM
    rw [he']; convert (show _ from (by exact_mod_cast HM : (((T₀ (π j0) s).val:ℕ):ℤ)≤4*(u:ℤ)*(N:ℕ))) using 1; ring
 have pat:=booking (p:=boxprice Y H (π j0) (ζ j0) zf.depth z zf.fire zf.enters) j _ hpp hB1 hT t' R0 (x:= X) hZ hc N C d y hp ((hh f t a0 hA).2.1) Dn hR hD hL hL' (add_comm _ R0 ▸ hv') (fun i=> by have ht':=ht i; unfold hot at ht'; rw [dif_pos zf.depth] at ht'; exact ht')
 have hn:n≤N:=hb.trans (by unfold N finalN; apply Nat.le_div_iff_mul_le (by positivity) |>.mpr ; change _ ≤ N0 j0; exact le_trans (by nlinarith) hj)
 have h:= pat _ hn; unfold hot; rw [dif_pos zf.depth]; -- adjust casts in goal p polymorphism
 convert h using 3 -- tune
 unfold worth p z; rw [Nat.cast_mul,Nat.cast_pow]


lemma uptake:∀ (r d:ℕ)(T:Finset Cover)(A:ℤ)(h:0 ≤ A)(x:Family (tent Y H)),InTest K true T false x→Between (tent Y H) j (2*(ruler Λ.block*(uM r))) A T→ CompactArc T d→∀ C:ℝ,0<C→pay x C→
 ∀ n:ℕ, ‖E (s+r) (chambers j (uM r) 0 (stream Y H D s r f) x n)‖≤ wages K (duetCharge Y (s+r)) d A C * Bω ^ n:=by
 have p:= interpolateThin Y H V s Q j w f S t hB Qt hw q g0 bg M0 hd0 d0 X0 ht0
 intro r d T A h x u e v C Hc hp n
 obtain ⟨S1,d'⟩:= BQueue.chambersS j (uM r) n 0 (queue_easy Y H V s Q f S t r) (BQueue.stay u Hc hp)
 have hr:= (hot_deck Y H V (s+r) Q _ S1 d').norm
 apply le_of_tendsto hr; exact (p r n d A C h).mono fun i w=> w n le_rfl x T u e v hp
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.uptake
