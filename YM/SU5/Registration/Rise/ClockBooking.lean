import YM.SU5.Reconstruction.Cashier.Engineer
import YM.SU5.Reconstruction.Cashier.Target
/-!
# Keep *all* leaves at the chosen price

Give an operator norm criterion for a `BQueue` of resolution-s slab readings, along
any subsequence of the chosen grant. Uses a `banner` purchased only on the s mesh;
the powers estimate must pay MANY copies already at finite volume (not constant n),
but does not need re-priced input at any other volumes.

Architecture & proofs extend `FiniteGaugeData/Tower/{PureCap,EndTrain,Baggage}` &
`Reconstruction/Cashier/{Every,Save,Target}` (in particular the body of
`interpolates` is a modified `Bankroll.gets`). Uses `Bankroll.engineered` (operator-norm
interpolation) unmodified. Additional geometric renewal including the numeric thresholds,
to apply this criterion, is separate.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.ClockBooking
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SatinVerification

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(G:Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt : Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(w:ℕ){f:ℕ→Family (tent Y H)}(S:Finset Cover){F:Family (tent Y H)}(t:BQueue S f F)(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
variable (φ:ℕ→ℕ)(τ:Tendsto φ atTop atTop)
local notation "π" r:max=>i (a (φ r))
local notation "ζ" r:max=> k (b (φ r))
local notation "Z" u:max r:max=> train Y H s u (π r) (ζ r) S (f r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> ((L₀:ℤ)^t*w)
local notation "b₀"=>ruler Λ.block
include G t τ in
lemma moving_queue (r:ℕ) : BQueue (W r) (fun i=> Z r i) (stream Y H D s r F) :=by
 let M (z:Family K):= stream Y H D s r z
 obtain ⟨A₀,hA,f'⟩:= fares Y H s G S r
 have hf(e:ℝ)(h:0<e):=(τ.eventually (f' e h))
 obtain ⟨C,hC,hT,u⟩:=t.bdd
 refine ⟨fun i=>prepared_train Y H s _ _ _ _ (t.whereTo i), (proceeds Y H G.circuit s r t.landing).1, ⟨A₀*C,mul_pos hA hC,?_,?_⟩,fun ε a=>?_⟩
 · obtain ⟨q,e⟩:=(f' 1 zero_lt_one).exists
   exact (e F t.landing C hT).1
 · filter_upwards [hf 1 zero_lt_one,u] with i e w
   exact (e _ (t.whereTo i) _ w).2.1
 let d:=ε/2/A₀; let e:=ε/2/C; have he:0<e:=by unfold e; positivity
 filter_upwards [hf e he,t.saved d (by unfold d; positivity),u] with i p q hi
 have hs:pay (M (f i)-M F) (A₀*d):=by
    rw [← show M (f i-F)=M (f i)-M F from ?_ ]; exact (p _ (InTest.subOp (t.whereTo i) t.landing) _ q).1
    unfold M; rw [sub_eq_add_neg (f i), ← neg_one_smul ℂ F, woven_add Y H G.circuit s _ (aux_test (t.whereTo i)) ((aux_test t.landing).scale _), woven_smul Y H G.circuit s _ (aux_test t.landing), neg_one_smul]; rfl
 have hh:=pay_add (show pay ((Z r i)-M (f i)) (e*C) from (p _ (t.whereTo i) _ hi).2.2.1) hs
 rw [sub_add_sub_cancel, show e*C+A₀*d=ε from ?_] at hh; exact hh
 unfold e d; field_simp; ring

-- sharp-priced: relative-error accrues on price `d`. Like PureCap.suppressed but
-- small d allowed (still fixed before volume).
private lemma clipped_rel {T:ℕ→ℕ}(v:Tendsto T atTop atTop){q d:ℝ}(x:0≤q)(y:0<d) :
    ∀ᶠ i in atTop,∀ n:ℕ,n≤ T i→ Real.exp (-((T i:ℕ):ℝ)^2)*q^(4*n) ≤ d^(4*n) :=by
 let A:=q/d; have hp:0≤A:=div_nonneg x y.le
 filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp v).eventually_ge_atTop (4*A)] with i h n t
 have hN : (n:ℝ) ≤ T i:= by exact_mod_cast t
 have h : 4*A ≤ (T i:ℝ):=h
 apply (div_le_one (pow_pos y _)).1
 rw [mul_div_assoc, ←div_pow]
 calc _ ≤ Real.exp (-((T i:ℕ):ℝ)^2)* (Real.exp A)^(4*n) :=by gcongr; exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
      _ = Real.exp (-((T i:ℕ):ℝ)^2+(4*n:ℕ)*A):=by rw [Real.exp_add,Real.exp_nat_mul]
      _ ≤ 1:=by apply Real.exp_le_one_iff.mpr; push_cast; nlinarith only [mul_le_mul_of_nonneg_right hN hp, mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α:=ℝ) (T i))]
include V G Qt τ
private lemma cashplate (r:ℕ){q d:ℝ}(x:0≤q)(y:0<d) : ∀ᶠ u:ℕ in atTop,
    ∀ n≤(T₀ (π u) r).val,∀ {f:Family (tent Y H)},TestFamily K true f→ pay f (q^(4*n))→
    ‖sharp Y H r (π u) (ζ u) f-hot Y H r (π u) (ζ u) f‖ ≤ d^(4*n) :=by
 filter_upwards [τ.eventually (Qt r),clipped_rel ((site_law Y H V G r).comp τ) x y] with i t v n h f p q; exact (t p _ q).trans (v _ h)
omit V G Qt τ

/-- Only the 0-origin slab needs to fit, and then long repeats with origins
multiples of THIS w. Estimates on the *already turned long banner*, not an inequality
on all neighbors of that slab. Index φ so BQueue can be along a subsequence. -/
def Issues (_G:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(f:ℕ→Family (tent Y H))(q:ℝ) : Prop :=
   ∀ᶠ u:ℕ in atTop,∀ n:ℕ,∀ v:ℤ, 0<n→2*(b₀*w*n) ≤ (((T₀ (π u) s).val:ℕ):ℤ)→ (((T₀ (π u) s).val:ℕ):ℤ) ≤ (4*(b₀*w*n))→
    ‖sharp Y H s (π u) (ζ u) (banner j w ((w:ℤ)*v) n (f u))‖ ≤ q^(4*n)
-- #check to examine binder order
#check Issues
include V G Qt τ hB t
variable (hw: 0<w)
include hw
lemma all_checked {q:ℝ}(hq:0<q)(h: Issues Y H (j:=j) (w:=w) (φ:=φ) s G f q) (r:ℕ) :
   ∀ᶠ u:ℕ in atTop,∀ n:ℕ,∀ v:ℤ, 0<n→2*(b₀*w*n) ≤ (((T₀ (π u) s).val:ℕ):ℤ)→ (((T₀ (π u) s).val:ℕ):ℤ) ≤ (4*(b₀*w*n))→
    ‖hot Y H (s+r) (π u) (ζ u) (banner j (uM r) ((L₀:ℤ)^r*((w:ℤ)*v)) n (Z r u))‖≤ ((2*q)^2)^(2*n) := by
 obtain ⟨A₀,hA,hX,hV⟩ := (moving_queue Y H s G S t φ τ r).bdd
 filter_upwards [h,τ.eventually (Bankroll.uniform_drop Y H V s G j hB r), cashplate Y H V G Qt φ τ (s+r) hA.le hq,hV] with i h p q' t' n v x y z
 have hr:1≤ b₀*(w:ℤ):=by
    have ht:0<(w:ℤ):=by exact_mod_cast hw
    have he:=ruler_gene Λ.block; nlinarith
 let Ns:=(T₀ (π i) s).val
 have hu:n≤Ns:=by change _ ≤ (Ns:ℤ) at y; zify; nlinarith [mul_le_mul_of_nonneg_right hr (show 0≤(n:ℤ) by positivity)]
 have hu':n ≤(T₀ (π i) (s+r)).val:=hu.trans (by unfold Ns; rw [refine_side]; exact Nat.le_mul_of_pos_left _ (pow_pos Λ.R.L.property r))
 let X:=banner j (uM r) ((L₀:ℤ)^r*((w:ℤ)*v)) n (Z r i)
 have he:‖sharp Y H (s+r) (π i) (ζ i) X‖ ≤ q^(4*n):=by unfold X; rw [p (t.whereTo i) n _ y]; exact h _ v x y z
 obtain ⟨f0,qP⟩:= main_bill j (uM r) ((L₀:ℤ)^r*((w:ℤ)*v)) n (aux_test (prepared_train Y H s S _ _ _ (t.whereTo i))) t'
 apply (norm_le_norm_sub_add _ (sharp Y H (s+r) (π i) (ζ i) X)).trans ((add_le_add ((norm_sub_rev ..).trans_le (q' _ hu' f0 qP)) he).trans ?_)
 rw [← two_mul, ←pow_mul, show 2*(2*n)=4*n from by omega, mul_pow]
 exact mul_le_mul_of_nonneg_right (by simpa only [pow_one] using (pow_le_pow_right₀ (a:=(2:ℝ)) (by norm_num) (show 1≤4*n by omega))) (pow_nonneg hq.le _)
omit V G Qt τ hB t hw

private lemma finalCount (n B:ℕ)(hB:0<B)(p:2*B≤n):
 let k:=finalN n B; 0 < k ∧ 2*B*k≤ n∧ n ≤ 2*B*k+2*B∧ n ≤ 4*B*k:=by
 intro k
 have h:0< k:= Nat.div_pos p (by positivity)
 have ht:=Nat.mod_add_div n (2*B); have he:=Nat.mod_lt n (by positivity:0<2*B); unfold k finalN at *
 obtain ⟨a,d⟩:= And.intro (by omega :2*B*(n/(2*B))≤n) (by omega : n<2*B*(n/(2*B))+2*B)
 exact ⟨h,a,d.le,(by nlinarith)⟩

set_option maxHeartbeats 400000
include V G Qt t τ hw hB
lemma interpolates {dPrim:ℝ}(hq:0<dPrim)(h:Issues Y H (j:=j) (w:=w) (φ:=φ) s G f dPrim) : ∀ (r N:ℕ)(d₀:ℕ) (A:ℤ)(c:ℝ)(p':0≤A),∀ᶠ e:ℕ in atTop,
 ∀ n:ℕ,n≤ N→∀ (x:Family K) (X:Finset Cover), InTest K true X false x→Between (tent Y H) j (2*(b₀*(uM r))) A X→ CompactArc X d₀→pay x c→
 ‖hot Y H (s+r) (π e) (ζ e) (chambers j (uM r) 0 (Z r e) x n)‖ ≤ wages K (duetCharge Y (s+r)) d₀ A c * ((2*dPrim)^2)^n:=by
 intro i' nT d R0 c hc
 let C:=(2*dPrim)^2; have y:0<C:=by unfold C; positivity
 let q:= all_checked Y H V s G Qt j w S t hB φ τ hw hq h i'
 let r:=i'; let z:= s+i'
 let N0(e:ℕ):= (T₀ (π e) s).val
 let Nr(e:ℕ):=(T₀ (π e) (s+r)).val

 obtain ⟨k',hF,v⟩:= fares Y H s G S i'
 let u:ℕ:=16*Λ.block.val*w
 let p:ℕ:=L₀^i'*w
 have he':b₀*w=(u:ℕ):=by unfold u ruler; push_cast; rfl
 have hr:u>0:=by unfold u; have h:= Λ.block.property; positivity
 have hs: b₀*p=(↑(u*L₀^r):ℤ):=by unfold p; push_cast; rw [mul_left_comm,he']; ring
 let mant(e:ℕ):= (K).c (m (π e) z)
 have hg:Tendsto (fun e=>(mant e).val) atTop atTop:=by unfold mant;simp_rw [side_register]; exact (site_law Y H V G z).comp τ
 filter_upwards [q, (site_law Y H V G s|>.comp τ).eventually_ge_atTop (2*u*(1+nT)), hg.eventually_ge_atTop (widthPair K (rim_width R0 d)+addgap K), hg.eventually_ge_atTop (widthPair K d+addgap K),
     hg.eventually_ge_atTop (2*R0.toNat),τ.eventually (v 1 zero_lt_one),τ.eventually (G.finance z)] with j0 qp hj hR hD hv hh zf n hb x X t' hZ Dn hp
 let F:=Z i' j0
 have hB1:InTest K true (W i') false F:=prepared_train Y H s S i' (π j0) (ζ j0) (t.whereTo j0)
 let N:= finalN (N0 j0) u
 let H0:= mant j0
 have hP: H0.val=L₀^r*N0 j0:=by unfold H0 mant; rw [side_register,refine_side]
 obtain ⟨hN,hM,hE,HM⟩:=finalCount (N0 j0) u hr (by
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
 -- alignment at multiples of w on the root mesh, transported to tall mesh
 have ht(j':ℤ): ‖hot Y H z (π j0) (ζ j0) (banner j (p:ℕ) ((p:ℤ)*j') N F)‖ ≤ C^(2*N) := by
    unfold p F
    push_cast; rw [mul_assoc (↑L₀^i':ℤ)]
    apply qp N j' hN
    · rw [mul_assoc, ←mul_assoc b₀, he']
      rw [←mul_assoc]; exact_mod_cast hM
    rw [he']; convert (show _ from (by exact_mod_cast HM : (((T₀ (π j0) s).val:ℕ):ℤ)≤4*(u:ℤ)*(N:ℕ))) using 1; ring
 obtain ⟨a0,pJ⟩ := Journey.valuation Y H (t.whereTo j0)
 have pat:=booking (p:=boxprice Y H (π j0) (ζ j0) zf.depth z zf.fire zf.enters) j _ hpp hB1 hT t' R0 (x:= X) hZ hc N C d y hp ((hh (f j0) (t.whereTo j0) a0 pJ).2.1) Dn hR hD hL hL' (add_comm _ R0 ▸ hv') (fun i=> by have ht':=ht i; unfold hot at ht'; rw [dif_pos zf.depth] at ht'; exact ht')
 have hn:n≤N:=hb.trans (by unfold N finalN; apply Nat.le_div_iff_mul_le (by positivity) |>.mpr ; change _ ≤ N0 j0; exact le_trans (by nlinarith) hj)
 have h:= pat _ hn; unfold hot; rw [dif_pos zf.depth]; -- adjust casts in goal (width)
 convert h using 3
 unfold worth p z; rw [Nat.cast_mul,Nat.cast_pow]


variable {d:ℝ}(hq:0<d)(h:Issues Y H (j:=j) (w:=w) (φ:=φ) s G f d)
   {strict:Bool}{f₀:Entry Y H s j strict w}(hF:f₀.val.val=F)
include V G Qt t τ hw hB h hF hq
lemma paid_on_actor : Bankroll.Evaluator Y H (D:=D) (E:=E) s j strict w f₀ ((2*d)^2) :=by
 intro r e T x hx y hy ey g u hu uy n
 rw [hF]
 obtain ⟨T',hT⟩:= BQueue.chambersS j (uM r) n 0 (moving_queue Y H s G S t φ τ r) (BQueue.stay hy hu uy)
 apply le_of_tendsto (Bankroll.hot_skim Y H V (s+r) G _ T' φ τ hT).norm
 exact (interpolates Y H V s G Qt j w S t hB φ τ hw hq h r n e x u hx).mono fun i h=>h n le_rfl y T hy ey g uy

lemma earned (C:Arena Y H G.circuit j 0 strict): ‖boxOp Y H V s G Qt j strict C w f₀ hw‖ ≤ 2*d :=
 (Bankroll.engineered Y H V s G j strict C w f₀ Qt hw _ (pow_pos (mul_pos (by norm_num) hq) _) (paid_on_actor Y H V s G Qt j w S t hB φ τ hw hq h hF)).trans_eq (Real.sqrt_sq (by positivity))

end YM.CF.Buffered.Afterglow.Tower.SlabMark.ClockBooking
open YM.CF.Buffered.Afterglow.Tower.SlabMark.ClockBooking
#print axioms moving_queue
#print axioms Issues
#print axioms all_checked
#print axioms interpolates
#print axioms paid_on_actor
#print axioms earned
