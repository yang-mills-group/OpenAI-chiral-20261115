import YM.SU5.Reconstruction.Cashier.Engineer
/-! Banner estimates to all stages. Variant of Polity and PureCap. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5900
set_option maxHeartbeats 390000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis){w:ℕ}{f:Family (tent Y H)}{S:Finset Cover}(t:InTest (tent Y H) true S false f)(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
local notation "Z" u:max n:max k:max=> train Y H s u n k S f
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
include V Q hB
section packed
omit Q hB V
variable (C:ℝ)
private lemma clipped_smallG {F:ℕ→ℕ}(v:Tendsto F atTop atTop)(q:ℝ)(x:0≤q): ∀ᶠ i in atTop,∀n:ℕ,n ≤ F i→ Real.exp (-((F i:ℕ):ℝ)^2)*(q^(4*n)) ≤ Real.exp (-2000*(n:ℝ)):=by
 filter_upwards [ (tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp v).eventually_ge_atTop (4*q+2000)] with i hi n u
 have he: q≤ Real.exp q:=by linarith [Real.add_one_le_exp q]
 have hi:(4*q+2000) ≤ (↑(F i):ℝ):=hi
 have hx:(n:ℝ) ≤ F i:= by exact_mod_cast u
 have hg:= Nat.cast_nonneg (α:=ℝ) n
 calc _ ≤ Real.exp (-((F i:ℕ):ℝ)^2)* (Real.exp q)^(4*n) := by gcongr
      _ = Real.exp (-((F i:ℕ):ℝ)^2+(4*n:ℕ)*q):= by rw [Real.exp_add, Real.exp_nat_mul]
      _ ≤ _:= by apply Real.exp_le_exp_of_le; push_cast; nlinarith

open SatinVerification
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "J₀" r:max=> i (G.rows r)
local notation "J₁" r:max=> k (G.columns r)
include V
private lemma exponent_plateG (h:0≤C):∀ᶠ r in atTop,∀ n≤(T₀ (J₀ r) s).val,∀ f:Family K,TestFamily K true f→pay f (C^(4*n))→‖sharp Y H s (J₀ r) (J₁ r) f-hot Y H s (J₀ r) (J₁ r) f‖≤ Real.exp (-2000*(n:ℝ)):=by
 filter_upwards [clipped_smallG (site_law Y H V G.history s) C h,G.clipped s] with i a b n t f p v; exact (b p _ v).trans (a n t)
def GridRolls (F:ℕ→Family (tent Y H))(w:ℕ) : Prop := ∀ j:Axis,∀ᶠ e:ℕ in atTop,∀ n:ℕ,∀ v:ℤ,
 0<n→2*(ruler Λ.block*w*n) ≤ (((Journey.side Y (J₀ e) s).val:ℕ):ℤ)→ (((Journey.side Y (J₀ e) s).val:ℕ):ℤ) ≤ (4*(ruler Λ.block*w*n))→
 ‖sharp Y H s (J₀ e) (J₁ e) (banner j w ((w:ℤ)*v) n (F e))‖ ≤ Real.exp (-3000*(n:ℝ)) -- need Type annotation implicit $ss
variable (F:ℕ→Family (tent Y H))(p:∀i,InTest (tent Y H) true S false (F i))(hp:∀i,pay (F i) C) (wage:GridRolls Y H s G F w)(e:0 < w)
local notation "B₀" i:max r:max=>train Y H s r (J₀ i) (J₁ i) S (F i)
local notation "b₀"=>ruler Λ.block
include p hp wage e hB
lemma allInGrid (r:ℕ) : ∀ᶠ i in atTop,∀ n:ℕ,∀ v:ℤ,
 0<n→2*(b₀*w*n) ≤ (((T₀ (J₀ i) s).val:ℕ):ℤ)→ (((T₀ (J₀ i) s).val:ℕ):ℤ) ≤ (4*(b₀*w*n))→
 ‖hot Y H (s+r) (J₀ i) (J₁ i) (banner j (uM r) ((L₀:ℤ)^r*((w:ℤ)*v)) n (B₀ i r))‖ ≤ rate^(2*n):=by
 let N(i):= (T₀ (J₀ i) (s+r)).val
 obtain ⟨A,p₀,Tp⟩:=fares Y H s G.history S r; have ht:0≤ C:=pay_nonneg (hp 0)
 filter_upwards [wage j,uniform_drop Y H V s G.history j hB r,Tp 1 zero_lt_one, exponent_plateG Y H V (s+r) (A*C) G (by positivity)] with i W₀ t p' t' n v hh Q y
 have h(n:ℕ): 1 ≤ b₀*(w:ℤ):= by
                                       have ht:0<(w:ℤ):=by exact_mod_cast e
                                       have hr:= ruler_gene Λ.block; nlinarith
 let f:=F i; let g:= B₀ i r
 let b:=sharp Y H (s+r) (J₀ i) (J₁ i); let a:= hot Y H (s+r) (J₀ i) (J₁ i)
 let X:=banner j (uM r) ((L₀:ℤ)^r*((w:ℤ)*v)) n g; let g₀:=(T₀ (J₀ i) s).val
 obtain ⟨c₀,k₁⟩:= main_bill j (uM r) ((L₀:ℤ)^r*((w:ℤ)*v)) n (aux_test (prepared_train Y H s S r _ _ (p i))) ((p' _ (p i) C (hp i)).2.1)
 have hu:n≤g₀:=by
    change _ ≤ (g₀:ℤ) at Q; zify; nlinarith [mul_le_mul_of_nonneg_right (h 0) (show 0≤(n:ℤ) by positivity)]
 have hu':n ≤ N i:= hu.trans (by unfold N g₀; rw [refine_side]; exact Nat.le_mul_of_pos_left _ (pow_pos Λ.R.L.property r))
 have hgx : ‖b X‖≤ Real.exp (-3000*(n:ℝ)):= by unfold b X g; rw [t (p i) n _ Q]; exact W₀ n v hh Q y
 have hhΩ:(1:ℝ)≤(n:ℝ):=by exact_mod_cast hh
 have hv:Real.exp (-3000*(n:ℝ)) ≤ Real.exp (-2000*(n:ℝ)):=by apply Real.exp_le_exp_of_le; linarith
 change ‖a X‖ ≤ _
 calc _ ≤ _ := (norm_le_norm_sub_add _ (b X)).trans (add_le_add ((norm_sub_rev ..).trans_le (t' _ hu' X c₀ k₁)) (hgx.trans hv))
      _ ≤ Real.exp (976*(n:ℝ))*Real.exp (-2000*(n:ℝ)):= by
         have h:2 ≤ Real.exp (976*(n:ℝ)):= by linarith only [Real.add_one_le_exp (976*(n:ℝ)),hhΩ];
         nlinarith [Real.exp_pos (-2000*(n:ℝ))]
      _ = _:= by unfold rate; rw [←Real.exp_add,←Real.exp_nat_mul]; push_cast; ring_nf
end packed
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.allInGrid
/-! Variant of EndTrain for our UNIFORM price & moving probe. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option maxHeartbeats 400000
set_option quotPrecheck false

namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
/-
# Choose terminal interpolation length (must on s mesh)

Arithmetic and fiscal proof. Moving input mark y at fine station allowed, terminal coverage supplied, while the important *exponent* declaration stays observing scale only. No extrapolation to unchosen paths. Goal uniform over n, all legal strips at far end; user endpoint applies to fixed n first.
-/
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
open SatinVerification
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Q₀"=>G.history
--variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis)(w:ℕ)(f:ℕ→Family (tent Y H))(S:Finset Cover)(t:∀i,InTest (tent Y H) true S false (f i))(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
local notation "π" r:max=>i (G.rows r)
local notation "ζ" r:max=> k (G.columns r)
local notation "Z" u:max r:max=> train Y H s u (π r) (ζ r) S (f r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
local notation "b₀"=>ruler Λ.block
variable (a0:ℝ)(hA:∀ i,pay (f i) a0)(wage:GridRolls Y H s G f w)(hw:0 < w)

private lemma finalCountG (n B:ℕ)(hB:0<B)(p:2*B≤n):
 let k:=finalN n B; 0 < k ∧ 2*B*k≤ n∧ n ≤ 2*B*k+2*B∧ n ≤ 4*B*k:=by
 intro k
 have h:0< k:= Nat.div_pos p (by positivity)
 have ht:=Nat.mod_add_div n (2*B); have he:=Nat.mod_lt n (by positivity:0<2*B); unfold k finalN at *
 obtain ⟨a,d⟩:= And.intro (by omega :2*B*(n/(2*B))≤n) (by omega : n<2*B*(n/(2*B))+2*B)
 exact ⟨h,a,d.le,(by nlinarith)⟩

include V t hB wage hw hA
lemma getsInGrid : ∀ (r N:ℕ)(d:ℕ) (A:ℤ)(c:ℝ)(p':0≤A),∀ᶠ e:ℕ in atTop,
 ∀ n:ℕ,n≤ N→∀ (x:Family K) (X:Finset Cover), InTest K true X false x→Between (tent Y H) j (2*(b₀*(uM r))) A X→ CompactArc X d→pay x c→
 ‖hot Y H (s+r) (π e) (ζ e) (chambers j (uM r) 0 (Z r e) x n)‖ ≤ wages K (duetCharge Y (s+r)) d A c * rate^n:=by
 intro i' nT d R0 c hc
 let C:=rate; have y:0<C:=pennies
 let q:= allInGrid Y H V s j hB a0 G f t hA wage hw i'
 let r:=i'; let z:= s+i'
 let N0(e:ℕ):= (T₀ (π e) s).val
 let Nr(e:ℕ):=(T₀ (π e) (s+r)).val

 obtain ⟨k',hF,v⟩:= fares Y H s G.history S i'
 let u:ℕ:=16*Λ.block.val*w
 let p:ℕ:=uM i'
 have he':b₀*w=(u:ℕ):=by unfold u ruler; push_cast; rfl
 have hr:u>0:=by unfold u; have h:= Λ.block.property; positivity
 have hs: b₀*p=(↑(u*L₀^r):ℤ):=by unfold p; push_cast; rw [mul_left_comm,he']; ring
 let mant(e:ℕ):= (K).c (m (π e) z)
 have hg:Tendsto (fun e=>(mant e).val) atTop atTop:=by unfold mant;simp_rw [side_register]; exact site_law Y H V G.history z
 filter_upwards [q, site_law Y H V G.history s|>.eventually_ge_atTop (2*u*(1+nT)), hg.eventually_ge_atTop (widthPair K (rim_width R0 d)+addgap K), hg.eventually_ge_atTop (widthPair K d+addgap K),
     hg.eventually_ge_atTop (2*R0.toNat),v 1 zero_lt_one,G.history.finance z] with j0 qp hj hR hD hv hh zf n hb x X t' hZ Dn hp
 let F:=Z i' j0
 have hB1:InTest K true (W i') false F:=prepared_train Y H s S i' (π j0) (ζ j0) (t j0)
 let N:= finalN (N0 j0) u
 let H0:= mant j0
 have hP: H0.val=L₀^r*N0 j0:=by unfold H0 mant; rw [side_register,refine_side]
 obtain ⟨hN,hM,hE,HM⟩:=finalCountG (N0 j0) u hr (by
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
    apply qp N j' hN
    · rw [mul_assoc, ←mul_assoc b₀, he'] -- bad
      rw [←mul_assoc]; exact_mod_cast hM
    rw [he']; convert (show _ from (by exact_mod_cast HM : (((T₀ (π j0) s).val:ℕ):ℤ)≤4*(u:ℤ)*(N:ℕ))) using 1; ring
 have pat:=booking (p:=boxprice Y H (π j0) (ζ j0) zf.depth z zf.fire zf.enters) j _ hpp hB1 hT t' R0 (x:= X) hZ hc N C d y hp ((hh (f j0) (t j0) a0 (hA j0)).2.1) Dn hR hD hL hL' (add_comm _ R0 ▸ hv') (fun i=> by have ht':=ht i; unfold hot at ht'; rw [dif_pos zf.depth] at ht'; exact ht')
 have hn:n≤N:=hb.trans (by unfold N finalN; apply Nat.le_div_iff_mul_le (by positivity) |>.mpr ; change _ ≤ N0 j0; exact le_trans (by nlinarith) hj)
 have h:= pat _ hn; unfold hot; rw [dif_pos zf.depth]; -- adjust casts in goal p polymorphism
 convert h using 3 -- tune
 unfold worth p z; rw [Nat.cast_mul,Nat.cast_pow]



open SatinVerification
omit t hB wage hA
lemma gets_box (f:Entry Y H s j false w)
 (wage: GridRolls Y H s G (fun _=>f.val.val) w)
 (C:Arena Y H G.history.circuit j 0 false):
    ‖SlabMark.boxOp Y H V s G.history G.clipped j false C w f hw‖ ≤ 1:=by
 have ht:Real.sqrt rate ≤ 1:=by
    apply Real.sqrt_le_iff.mpr; unfold rate
    exact ⟨(by norm_num),by rw [one_pow]; exact Real.exp_le_one_iff.mpr (by norm_num)⟩
 refine le_trans (engineered Y H V s G.history j false C w f G.clipped hw rate pennies ?_) ht
 
 obtain ⟨S,t,b⟩:=f.property
 obtain ⟨B,pay⟩:=valuation Y H t
 intro r d T A h x u e v c Hc hp n
 obtain ⟨S1,d'⟩:= BQueue.chambersS j (uM r) n 0 (queue_easy Y H V s G.history f.val.val S t r) (BQueue.stay u Hc hp)
 have hr:= (hot_deck Y H V (s+r) G.history _ S1 d').norm
 apply le_of_tendsto hr
 exact (getsInGrid Y H V s G j w (fun _=>f.val.val) S (fun _=>t) b B (fun _=>pay) wage hw r n d A c h).mono fun i w=> w n le_rfl x T u e v hp
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.gets_box
