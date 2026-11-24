import Velour.Board.Relate
/-!
# Reach arbitrary resolution spectators from a peak-price array
Version of Velour/Board/Skim & Relate, by using the local Cashier.{Every,Save,Target} for one path within
the pinned preparation, ANY positive price and relaxed *hot* array input with precise fee (tight presidential)
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

namespace Presidential

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
 (ho:0<θ)(hw:0 < w){ε:ℝ}(ht:0<ε)


include t hB hotT hA ha0 ho hw ht
lemma summit (r:ℕ) :
 ∀ᶠ e in atTop,∀ z:ℤ, let n:=ν₀ e
   ‖hot Y H (s+r) (π e) (ζ e)
     (banner j (uM r) ((L₀:ℤ)^r*((w:ℤ)*z)) n (Z r e))‖ ≤ ((θ+2*ε)^2)^(2*n):=by
 let N(i):= (T₀ (π i) s).val
 have hs:=rides Y H V G ψ ouT s
 obtain ⟨A,p₀,Tp⟩:=fares Y H s G.history S r
 unfold Peak at hotT
 filter_upwards [hotT,hA,redeem Y H V G ψ ouT s a0 ε ha0.le ht,
   ouT.eventually (Bankroll.uniform_drop Y H V s G.history j hB r),
   redeem Y H V G ψ ouT (s+r) (A*a0) ε (by positivity) ht,
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
 have hx : ‖sharp Y H s (π i) (ζ i) x‖ ≤ ε^(4*n) + θ^(4*n):= by
    exact (norm_le_norm_sub_add _ (hot Y H s (π i) (ζ i) x)).trans
      (add_le_add (h₁ n hu x u y) (W₀ z))
 have hb : ‖sharp Y H (s+r) (π i) (ζ i) X‖ ≤ ε^(4*n) + θ^(4*n):= by
    unfold X g; rw [dro (t i) n v h]; exact hx

 refine le_trans ((norm_le_norm_sub_add _ (sharp Y H (s+r) (π i) (ζ i) X)).trans
   (add_le_add ((norm_sub_rev ..).trans_le (h₂ n h' X u' y')) hb)) ?_
 rw [← pow_mul, show 2*(2*n)=4*n from by omega]
 calc _ ≤ ε^(4*n)+(ε+θ)^(4*n):=add_le_add_right (pow_add_pow_le ht.le ho.le (by omega)) _
      _ ≤ (ε+(ε+θ))^(4*n):=pow_add_pow_le ht.le (add_nonneg ht.le ho.le) (by omega)
      _ = (θ+2*ε)^(4*n):=by ring_nf
lemma gets : ∀ (r N:ℕ)(d:ℕ) (A:ℤ)(c:ℝ)(_p:0≤A),∀ᶠ e:ℕ in atTop,
 ∀ n:ℕ,n≤ N→∀ (x:Family K) (X:Finset Cover), InTest K true X false x→Between (tent Y H) j (2*(b₀*(uM r))) A X→ CompactArc X d→pay x c→
 ‖hot Y H (s+r) (π e) (ζ e) (chambers j (uM r) 0 (Z r e) x n)‖ ≤ wages K (duetCharge Y (s+r)) d A c * ((θ+2*ε)^2)^n:=by
 intro i' nT d R0 c hc
 let C:=((θ+2*ε)^2); have y:0<C:=by unfold C; positivity
 let q:= summit Y H V s G j w f S t hB ψ ouT a0 ha0 hA θ hotT ho hw ht i'
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



omit t hotT hA ha0 ho hw ht
variable {w S f}
variable (dome:Entry Y H s j false w)
variable (p:BQueue S f dome.val.val) (room:Arena Y H G.history.circuit j 0 false)
include V hB p ho hotT hw ht
lemma bankTickets :
  Bankroll.Evaluator Y H s j false w dome ((θ+2*ε)^2) (D:=G.refine) (E:=E) :=by
 have εp:=ht
 intro r d T A h x hx ha ht C c y n
 obtain ⟨w₁,hT⟩:= BQueue.chambersS j (uM r) n 0 (convoy Y H s G ψ ouT p r) (BQueue.stay hx c y)
 have hh:= (Bankroll.hot_skim Y H V (s+r) G.history _ w₁ ψ ouT hT).norm
 obtain ⟨q,a,_,hQ⟩:=p.bdd
 apply le_of_tendsto hh
 exact (gets Y H V s G j w f S p.whereTo hB ψ ouT q a hQ θ hotT ho hw εp _ n d A C h).mono fun i t=> t n le_rfl x T hx ha ht y

/-- Banner estimate => **operator norm**.
 Applies on the MEAN spine and hence (using C*-contraction) on every
 selected single-phase representation, without genericity restrictions. -/
theorem price :
  ‖boxOp Y H V s G.history G.clipped j false room w dome hw‖ ≤ θ+2*ε:=by
 have hh:=ht
 have h:=Bankroll.engineered Y H V s G.history j false room w dome G.clipped hw _ 
   (by positivity : 0 < (θ+2*ε)^2) (bankTickets Y H V s G j hB ψ ouT θ hotT ho hw hh dome p)
 rwa [Real.sqrt_sq (by positivity)] at h

omit hB p ho hotT hw ht
variable (w f S)
variable (o:Cell)
private lemma cruiseIce (C θ:ℝ)(c:0<C)(r:0<θ):
 ∀ᶠ i' in atTop,let N:=(T₀ (π i') s).val;
    ∀ n ≤ (2*N)^4, iceRate Y s (π i') * C^n ≤ θ^n:=by
 -- fixed positive at this resolution 
 have u:C/θ ≤ Real.exp (C/θ):=by linarith [Real.add_one_le_exp (C/θ)]
 filter_upwards [ (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (rides Y H V G ψ ouT s)|>.eventually_ge_atTop (16*(C/θ))] with i' t
 intro N n h
 let e:=Real.exp (-((N:ℕ):ℝ)^5)
 have hd: e*(C/θ)^n ≤ 1:=by
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) u n)
             (Real.exp_pos _).le) ?_
    rw [←Real.exp_nat_mul]
    unfold e
    rw [←Real.exp_add, Real.exp_le_one_iff]
    have v:(n:ℝ) ≤ (2*(N:ℝ))^4 := by exact_mod_cast h
    change 16*(C/θ) ≤ (N:ℝ) at t
    linarith only [mul_le_mul_of_nonneg_right v (by positivity:0≤C/θ),
       mul_le_mul_of_nonneg_right t (show 0≤(N:ℝ)^4 from by positivity)]
 rwa [div_pow,←mul_div_assoc,div_le_one (by positivity)] at hd

variable (freeze:IcePath Y (i∘G.rows) (k∘G.columns))
 (shape:Parcel (tent Y H) w o 0 S)
 (margin:o j=0)

 (ask:Settle Y H s G w f ψ o θ)
include ask ho hw t shape margin freeze
include ht
lemma peak_Plot (C:ℝ)(p:0<C) (p':∀ᶠi in atTop,pay (f i) C): Peak Y H s G j w f ψ (ε+θ) :=by
 unfold Settle at ask; unfold Peak
 filter_upwards [ask,p',ouT.eventually (freeze s),ouT.eventually (G.history.finance s), 
   cruiseIce Y H V s G ψ ouT C ε p ht,
   (rides Y H V G ψ ouT s).eventually_ge_atTop (2*pitch K w)] with i' q paid ice g d far z
 have r : ∀ d L U, Deck (m (π i') s) w o (f i') d L U →
    ‖hot Y H s (π i') (ζ i') (Representation d)‖ ≤ (ε+θ)^d.length:=by
    intro l A B e
    have hf := q l A B e
    obtain ⟨_,h,_⟩:= pavingReservation (t i') shape e.paved
    have hx :=iceCream Y H s ice g (aux_test h) (pavingCost paid e.paved)

    have hside : (K).c (m (π i') s)= T₀ (π i') s :=terrain Y H (Y.ir (π i')) s
    have hlen:= Deck.length_le hw e; rw [hside] at hlen -- warning rw dependent? l.length no Side
    refine le_trans ((norm_le_norm_sub_add _ (sharp Y H s (π i') (ζ i') (Representation l))).trans
       (add_le_add ((norm_sub_rev ..).trans_le (hx.trans (d l.length hlen))) hf)) ?_
    exact pow_add_pow_le ht.le ho.le (Deck.length_pos e).ne'
 let n := π i'; let k' := ζ i'
 have hN : ((K).c (m n s)).val=(T₀ n s).val := by rw [show (K).c (m n s)= T₀ n s from terrain Y H (Y.ir n) s]
 have hp:=hotStrip (p:=boxprice Y H n k' g.depth s g.fire g.enters)
    (t i') shape j margin hw (far:=le_trans far hN.symm.le) (ε+θ) (by positivity)
    (fun d L U t'=>by have h:=r d L U t'; unfold hot at h; rw [dif_pos g.depth] at h; exact h) z
 dsimp only at hp
 rw [hN] at hp
 unfold hot; rw [dif_pos g.depth]; exact hp

omit t ht
/-- **The sharp array criterion** for purchasing a cap. -/
lemma boardPrice (room:Arena Y H G.history.circuit j 0 false)
  (dome:Entry Y H s j false w) (p:BQueue S f dome.val.val) :
 ‖boxOp Y H V s G.history G.clipped j false room w dome hw‖ ≤ θ:=by
 obtain ⟨c,pos,_,cost⟩:=p.bdd
 have h:=shape j
 unfold Wall at h
 simp only [Pi.zero_apply,margin,mul_zero,zero_add,mul_one] at h
 by_contra! u
 let d:=(‖boxOp Y H V s G.history G.clipped j false room w dome hw‖-θ)/4
 have hd:0<d:=by unfold d; linarith
 have hb:= peak_Plot Y H V s G j w f S p.whereTo ψ ouT θ ho hw hd o freeze shape margin ask c pos cost
 have q:=price Y H V s G j h ψ ouT (d+θ) hb (by positivity) hw hd dome p room
 unfold d at q; linarith
#print axioms boardPrice
end Presidential
end YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard
