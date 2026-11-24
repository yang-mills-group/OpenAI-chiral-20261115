import YM.SU5.Reconstruction.Cashier.Target
import YM.SU5.Reconstruction.Cashier.Engineer
/-!
# Reach arbitrary resolution spectators from a peak-price array
Variant of the local Cashier.{Every,Save,Target} for one path within
the pinned preparation, ANY positive price and relaxed *hot* array input
(torus pure banner at many placements but only the booked length).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option maxHeartbeats 1200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
open SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
open SatinVerification
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Q₀"=>G.history

variable (j:Axis)(w:ℕ)(f:ℕ→Family (tent Y H))(S:Finset Cover)(t:∀i,InTest (tent Y H) true S false (f i))(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
variable (ψ:ℕ→ℕ)(ouT:Tendsto ψ atTop atTop)
local notation "π" r:max=>i (G.rows (ψ r))
local notation "ζ" r:max=> k (G.columns (ψ r))

local notation "Z" u:max r:max=> train Y H s u (π r) (ζ r) S (f r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
local notation "b₀"=>ruler Λ.block

local notation "l₀"=>16*Λ.block.val*w
local notation "ν₀" e:max=>finalN (T₀ (π e) s).val (l₀)

/-- Path-array upper bound, with authorizing reindexing.
    (Only at the coarse height; no uniformity through all higher rungs at fixed cutoff.) -/
def Peak (θ:ℝ) : Prop := ∀ᶠ e in atTop,∀ z:ℤ,
 ‖hot Y H s (π e) (ζ e) (banner j w (↑w*z) (ν₀ e) (f e))‖ ≤ θ^(4*(ν₀ e))

lemma finalCount (n B:ℕ)(hB:0<B)(p:2*B≤n):
 let k:=finalN n B; 0 < k ∧ 2*B*k≤ n∧ n ≤ 2*B*k+2*B∧ n ≤ 4*B*k:=by
 intro k
 have h:0< k:= Nat.div_pos p (by positivity)
 have ht:=Nat.mod_add_div n (2*B); have he:=Nat.mod_lt n (by positivity:0<2*B); unfold k finalN at *
 obtain ⟨a,d⟩:= And.intro (by omega :2*B*(n/(2*B))≤n) (by omega : n<2*B*(n/(2*B))+2*B)
 exact ⟨h,a,d.le,(by nlinarith)⟩


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
include V ouT


lemma rides (s:ℕ) : Tendsto (fun e=>(T₀ (π e) s).val) atTop atTop :=
 (site_law Y H V G.history s).comp ouT
private lemma redeem (s:ℕ)(C θ:ℝ)(hC:0≤C)(ho:0<θ) :
 ∀ᶠ e in atTop,∀ n≤ (T₀ (π e) s).val,∀ F:Family K,
  TestFamily K true F → pay F (C^(4*n)) →
   ‖sharp Y H s (π e) (ζ e) F-hot Y H s (π e) (ζ e) F‖ ≤ θ^(4*n):=by
 filter_upwards [suppressed (rides Y H V G ψ ouT s) (C/θ) (by positivity),ouT.eventually (G.clipped s)]
    with i h y n u f p q
 refine (y p _ q).trans ?_
 specialize h n u
 rw [div_pow,← mul_div_assoc, div_le_one (by positivity)] at h
 exact h

variable (a0:ℝ)(ha0:0<a0)(hA:∀ᶠ i in atTop,pay (f i) a0)
 (θ:ℝ)(hotT:Peak Y H s G j w f ψ θ)
 (ho:0<θ)(hw:0 < w)


include t hB hotT hA ha0 ho hw
lemma summit (r:ℕ) :
 ∀ᶠ e in atTop,∀ z:ℤ, let n:=ν₀ e
   ‖hot Y H (s+r) (π e) (ζ e)
     (banner j (uM r) ((L₀:ℤ)^r*((w:ℤ)*z)) n (Z r e))‖ ≤ ((2*θ)^2)^(2*n):=by
 let N(i):= (T₀ (π i) s).val
 have hs:=rides Y H V G ψ ouT s
 obtain ⟨A,p₀,Tp⟩:=fares Y H s G.history S r
 unfold Peak at hotT
 filter_upwards [hotT,hA,redeem Y H V G ψ ouT s a0 θ ha0.le ho,
   ouT.eventually (Bankroll.uniform_drop Y H V s G.history j hB r),
   redeem Y H V G ψ ouT (s+r) (A*a0) θ (by positivity) ho,
   ouT.eventually (Tp 1 zero_lt_one),hs.eventually_ge_atTop (2*(l₀))]
  with i W₀ xa h₁ dro h₂ p' cnt z
 intro n
 let v:= (w:ℤ)*z
 let g := Z r i; let X := banner j (uM r) ((L₀:ℤ)^r*v) n g
 let x := banner j w v n (f i)
 obtain ⟨u,y⟩:= main_bill j w v n (aux_test (t i)) xa
 obtain ⟨u',y'⟩:= main_bill j (uM r) ((L₀:ℤ)^r*v) n (aux_test (prepared_train Y H s S r _ _ (t i))) ((p' _ (t i) a0 xa).2.1)
 let m0 := l₀
 have hl : 0 < m0:=by unfold m0; have h:=Λ.block.property; positivity
 obtain ⟨hk₁,hk₂,_,_⟩:= finalCount (N i) m0 hl cnt
 change 0<n at hk₁; change 2*m0*n≤ N i at hk₂
 have hu:n≤ N i:= by exact le_trans (Nat.le_mul_of_pos_left n (by positivity)) hk₂
 have h : 2*(b₀*w*n) ≤ (↑(N i):ℤ):=by
    rw [show b₀*(w:ℤ)=(m0:ℤ) from by unfold m0 ruler; push_cast; rfl, ← mul_assoc]
    exact_mod_cast hk₂
 have h' : n ≤ (T₀ (π i) (s+r)).val:= hu.trans
   (by unfold N; rw [refine_side]; exact Nat.le_mul_of_pos_left _ (pow_pos Λ.R.L.property r))
 have hx : ‖sharp Y H s (π i) (ζ i) x‖ ≤ θ^(4*n) + θ^(4*n):= by
    exact (norm_le_norm_sub_add _ (hot Y H s (π i) (ζ i) x)).trans
      (add_le_add (h₁ n hu x u y) (W₀ z))
 have hb : ‖sharp Y H (s+r) (π i) (ζ i) X‖ ≤ θ^(4*n) + θ^(4*n):= by
    unfold X g; rw [dro (t i) n v h]; exact hx

 refine le_trans ((norm_le_norm_sub_add _ (sharp Y H (s+r) (π i) (ζ i) X)).trans
   (add_le_add ((norm_sub_rev ..).trans_le (h₂ n h' X u' y')) hb)) ?_
 rw [← pow_mul, show 2*(2*n)=4*n from by omega, mul_pow]
 have hv:(3:ℝ)≤2^(4*n):=by
    exact (show (3:ℝ) ≤ 2^2 from by norm_num).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
 nlinarith only [mul_le_mul_of_nonneg_right hv (pow_nonneg ho.le (4*n))]
lemma gets : ∀ (r N:ℕ)(d:ℕ) (A:ℤ)(c:ℝ)(_p:0≤A),∀ᶠ e:ℕ in atTop,
 ∀ n:ℕ,n≤ N→∀ (x:Family K) (X:Finset Cover), InTest K true X false x→Between (tent Y H) j (2*(b₀*(uM r))) A X→ CompactArc X d→pay x c→
 ‖hot Y H (s+r) (π e) (ζ e) (chambers j (uM r) 0 (Z r e) x n)‖ ≤ wages K (duetCharge Y (s+r)) d A c * ((2*θ)^2)^n:=by
 intro i' nT d R0 c hc
 let C:=((2*θ)^2); have y:0<C:=by unfold C; positivity
 let q:= summit Y H V s G j w f S t hB ψ ouT a0 ha0 hA θ hotT ho hw i'
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
 have hg:Tendsto (fun e=>(mant e).val) atTop atTop:=by unfold mant;simp_rw [side_register]; exact rides Y H V G ψ ouT z
 filter_upwards [q, rides Y H V G ψ ouT s|>.eventually_ge_atTop (2*u*(1+nT)), hg.eventually_ge_atTop (widthPair K (rim_width R0 d)+addgap K), hg.eventually_ge_atTop (widthPair K d+addgap K),
     hg.eventually_ge_atTop (2*R0.toNat),ouT.eventually (v 1 zero_lt_one), ouT.eventually (G.history.finance z),hA] with j0 qp hj hR hD hv hh zf pa n hb x X t' hZ Dn hp
 let F:=Z i' j0
 have hB1:InTest K true (W i') false F:=prepared_train Y H s S i' (π j0) (ζ j0) (t j0)
 let N:= finalN (N0 j0) u
 let H0:= mant j0
 have hP: H0.val=L₀^r*N0 j0:=by unfold H0 mant; rw [side_register,refine_side]
 obtain ⟨hN,hM,hE,HM⟩:=finalCount (N0 j0) u hr (by
    exact le_trans (Nat.le_mul_of_pos_right _ (by omega:0<1+nT)) hj)
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
    exact qp j'
 have pat:=booking (p:=boxprice Y H (π j0) (ζ j0) zf.depth z zf.fire zf.enters) j _ hpp hB1 hT t' R0 (x:= X) hZ hc N C d y hp ((hh (f j0) (t j0) a0 pa).2.1) Dn hR hD hL hL' (add_comm _ R0 ▸ hv') (fun i=> by have ht':=ht i; unfold hot at ht'; rw [dif_pos zf.depth] at ht'; exact ht')
 have hn:n≤N:=hb.trans (by unfold N finalN; apply Nat.le_div_iff_mul_le (by positivity) |>.mpr ; exact le_trans (by nlinarith) hj)
 have h:= pat _ hn; unfold hot; rw [dif_pos zf.depth]; -- adjust casts in goal p polymorphism
 convert h using 3
 unfold worth p z; rw [Nat.cast_mul,Nat.cast_pow]



omit V t hB hotT hA ha0 ho hw
variable {w S f} {F:Family (tent Y H)}
include ouT
lemma convoy (p:BQueue S f F) (r:ℕ): BQueue (W r) (fun e=>Z r e)
    (stream Y H G.refine s r F):=by
 obtain ⟨a,p₀,p₁,pa⟩:=p.bdd; obtain ⟨A,po,b⟩:=fares Y H s G.history S r
 refine ⟨fun i=>prepared_train Y H s S r _ _ (p.whereTo i),
   (proceeds Y H G.history.circuit s r p.landing).1,⟨A*a,mul_pos po p₀,?_,?_⟩,?_⟩
 · obtain ⟨i,h⟩:=(b 1 zero_lt_one).exists; exact (h _ p.landing a p₁).1
 · filter_upwards [pa,ouT.eventually (b 1 zero_lt_one)] with i f' q; exact (q _ (p.whereTo i) _ f').2.1
 intro ε e
 filter_upwards [pa,ouT.eventually (b (ε/(2*a)) (by positivity)),p.saved (ε/(2*A)) (by positivity)]
    with i f' q g
 let X(f:Family K):=stream Y H G.refine s r f
 have H₁:pay (Z r i-X (f i)) (ε/(2*a)*a):=(q _ (p.whereTo i) _ f').2.2.1
 have H₂:pay (X (f i-F)) (A*(ε/(2*A))):=(q _ (InTest.subOp (p.whereTo i) p.landing) _ g).1

 have hms:X (f i-F)=X (f i)-X F:=by
    unfold X
    rw [sub_eq_add_neg,←neg_one_smul ℂ F,
      woven_add Y H G.history.circuit s r (aux_test (p.whereTo i)) ((aux_test p.landing).scale _),
      woven_smul Y H G.history.circuit s r (aux_test p.landing),neg_one_smul,sub_eq_add_neg]
 rw [hms] at H₂
 have ht:=pay_add H₁ H₂
 rw [show Z r i - X (f i) + (X (f i) - X F) = Z r i - X F from by abel,
       show ε/(2*a)*a + A*(ε/(2*A))=ε from by field_simp; ring] at ht
 exact ht

variable (dome:Entry Y H s j false w)
variable (p:BQueue S f dome.val.val) (room:Arena Y H G.history.circuit j 0 false)
include V hB p ho hotT hw
lemma bankTickets :
  Bankroll.Evaluator Y H s j false w dome ((2*θ)^2) (D:=G.refine) (E:=E) :=by
 intro r d T A h x hx ha ht C c y n
 obtain ⟨w₁,hT⟩:= BQueue.chambersS j (uM r) n 0 (convoy Y H s G ψ ouT p r) (BQueue.stay hx c y)
 have hh:= (Bankroll.hot_skim Y H V (s+r) G.history _ w₁ ψ ouT hT).norm
 obtain ⟨q,a,_,hQ⟩:=p.bdd
 apply le_of_tendsto hh
 exact (gets Y H V s G j w f S p.whereTo hB ψ ouT q a hQ θ hotT ho hw _ n d A C h).mono fun i t=> t n le_rfl x T hx ha ht y

/-- Banner estimate => **operator norm**.
 Applies on the MEAN spine and hence (using C*-contraction) on every
 selected single-phase representation, without genericity restrictions. -/
theorem price :
  ‖boxOp Y H V s G.history G.clipped j false room w dome hw‖ ≤ 2*θ:=by
 have h:=Bankroll.engineered Y H V s G.history j false room w dome G.clipped hw _ 
   (by positivity : 0 < (2*θ)^2) (bankTickets Y H V s G j hB ψ ouT θ hotT ho hw dome p)
 rwa [Real.sqrt_sq (by positivity)] at h
end YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard

#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard.price

