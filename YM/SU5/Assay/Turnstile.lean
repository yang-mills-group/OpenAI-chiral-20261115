import YM.SU5.FiniteGaugeData.Tower.StationMaster

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
section turn

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
variable (f0:ℕ→Family (tent Y H))
local notation "Z" u:max r:max=> train Y H s u (π r) (ζ r) S (f0 r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
local notation "b₀"=>ruler Λ.block
variable (Qt : Clipped Y H (i∘a) (k∘b))(hw:0 < w)

include Q
lemma train_queue (h:BQueue S f0 f)(r:ℕ):
    BQueue (W r) (fun i=> Z r i) (stream Y H D s r f):=by
 let Φ:=stream Y H D s r
 obtain ⟨A,u,v⟩:=fares Y H s Q S r
 obtain ⟨c,p,hp,gh⟩:=h.bdd
 have ht(ε:ℝ)(q:0 < ε):∀ᶠ n:ℕ in atTop,pay (Φ f) (A*c)∧pay (Z r n) (A*c)∧pay (Z r n-Φ f) ε:=by
    let d:=ε/(A+c); have hd:0 < d:=div_pos q (by positivity)
    filter_upwards [v d hd,h.saved d hd,gh] with i he hδ hc
    obtain ⟨_,b,a,_⟩:=he _ (h.whereTo i) c hc
    have hv: Φ (f0 i-f)=Φ (f0 i)-Φ f:=by
       unfold Φ; rw [sub_eq_add_neg,←neg_one_smul ℂ f,woven_add Y H Q.circuit _ _ (aux_test (h.whereTo i)) ((aux_test h.landing).scale _),woven_smul Y H Q.circuit _ _ (aux_test h.landing),neg_one_smul,sub_eq_add_neg]
    have hx:= (he _ (InTest.subOp (h.whereTo i) h.landing) _ hδ).1
    change pay (Φ _) _ at hx; rw [hv] at hx
    have hh: d*c+A*d=ε:=by linarith only [show d*(A+c)=ε from div_mul_cancel₀ _ (by positivity)]
    exact ⟨(he _ h.landing _ hp).1,b, by rw [←hh,← sub_add_sub_cancel (Z r i) (Φ (f0 i)) (Φ f)]; exact pay_add a hx⟩
 exact ⟨fun i=>prepared_train Y H s S r _ _ (h.whereTo i),(proceeds Y H Q.circuit s r h.landing).1,⟨A*c,by positivity,by obtain ⟨n,h'⟩:=(ht 1 one_pos).exists; exact h'.1,(ht 1 one_pos).mono fun _ h=>h.2.1 ⟩,fun e p=>(ht e p).mono (fun _ w=>w.2.2)⟩
omit Q

/-- License: terminal banner hot price, at all fixed heights. Width w at s in ticks,
and finalN computed there. C is chamber charge per *two* copies. -/
def Turnstile (C:ℝ):Prop:= ∀ r:ℕ, ∀ᶠ e:ℕ in atTop,
    let N:=finalN (T₀ (π e) s).val (16*Λ.block.val*w)
    ∀ i:ℤ, ‖hot Y H (s+r) (π e) (ζ e) (banner j (uM r) ((uM r)*i) N (Z r e))‖ ≤ C^(2*N)
local notation "license"=>Turnstile (i:=i) (k:=k) (a:=a) (b:=b) Y H s j w S f0

private lemma zCount (n B:ℕ)(hB:0<B)(p:2*B≤n):
 let k:=finalN n B; 0 < k ∧ 2*B*k≤ n∧ n ≤ 2*B*k+2*B∧ n ≤ 4*B*k:=by
 intro k
 have h:0< k:= Nat.div_pos p (by positivity)
 have ht:=Nat.mod_add_div n (2*B); have he:=Nat.mod_lt n (by positivity:0<2*B); unfold k finalN at *
 obtain ⟨a,d⟩:= And.intro (by omega :2*B*(n/(2*B))≤n) (by omega : n<2*B*(n/(2*B))+2*B)
 exact ⟨h,a,d.le,(by nlinarith)⟩

include V Q hB hw
lemma zTurn (tf:∀n,InTest K true S false (f0 n))(C:ℝ)(y:0<C)(q:license C):∀ (r N:ℕ)(d:ℕ) (A:ℤ)(c:ℝ)(_:0≤A),∀ᶠ e:ℕ in atTop,
 ∀ n:ℕ,n≤ N→∀ (x:Family K) (X:Finset Cover), InTest K true X false x→Between (tent Y H) j (2*(b₀*(uM r))) A X→ CompactArc X d→pay x c→
 ‖hot Y H (s+r) (π e) (ζ e) (chambers j (uM r) 0 (Z r e) x n)‖ ≤ wages K (duetCharge Y (s+r)) d A c * C^n:=by
 intro i' nT d R0 c hc
 let r:=i'; let z:= s+i'
 let N0(e:ℕ):= (T₀ (π e) s).val
 let Nr(e:ℕ):=(T₀ (π e) (s+r)).val
 let u:ℕ:=16*Λ.block.val*w
 let p:ℕ:=uM i'
 have he':b₀*w=(u:ℕ):=by unfold u ruler; push_cast; rfl
 have hr:u>0:=by unfold u; have h:= Λ.block.property; positivity
 have hs: b₀*p=(↑(u*L₀^r):ℤ):=by unfold p; push_cast; rw [mul_left_comm,he']; ring
 let mant(e:ℕ):= (K).c (m (π e) z)
 have hg:Tendsto (fun e=>(mant e).val) atTop atTop:=by unfold mant;simp_rw [side_register]; exact site_law Y H V Q z
 filter_upwards [q i', site_law Y H V Q s|>.eventually_ge_atTop (2*u*(1+nT)), hg.eventually_ge_atTop (widthPair K (rim_width R0 d)+addgap K), hg.eventually_ge_atTop (widthPair K d+addgap K),
     hg.eventually_ge_atTop (2*R0.toNat),Q.finance z] with j0 qp hj hR hD hv zf n hb x X t' hZ Dn hp
 let F:=Z i' j0
 have hB1:InTest K true (W i') false F:=prepared_train Y H s S i' (π j0) (ζ j0) (tf _)
 let N:= finalN (N0 j0) u
 let H0:= mant j0
 have hP: H0.val=L₀^r*N0 j0:=by unfold H0 mant; rw [side_register,refine_side]
 obtain ⟨hN,hM,hE,HM⟩:=zCount (N0 j0) u hr (by
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
 have ht(j':ℤ): ‖hot Y H z (π j0) (ζ j0) (banner j (p:ℕ) ((p:ℤ)*j') N F)‖ ≤ C^(2*N) := by
    unfold p F
    push_cast; exact qp j'
 obtain ⟨a,h⟩:=valuation Y H hB1; have ha:pay F a:=h
 have pat:=booking (p:=boxprice Y H (π j0) (ζ j0) zf.depth z zf.fire zf.enters) j _ hpp hB1 hT t' R0 (x:= X) hZ hc N C d y hp ha Dn hR hD hL hL' (add_comm _ R0 ▸ hv') (fun i=> by have ht':=ht i; unfold hot at ht'; rw [dif_pos zf.depth] at ht'; exact ht')
 have hn:n≤N:=hb.trans (by unfold N finalN; apply Nat.le_div_iff_mul_le (by positivity) |>.mpr ; exact le_trans (by nlinarith) hj)
 have h:= pat _ hn; unfold hot; rw [dif_pos zf.depth]; -- adjust casts in goal p polymorphism
 convert h using 3
 unfold worth p z; rw [Nat.cast_mul,Nat.cast_pow]

include V Q hB hw
lemma baggageTurn (tf:BQueue S f0 f)(B:ℝ)(y:0<B)(q:license B):∀ (r d:ℕ)(T:Finset Cover)(A:ℤ)(_:0 ≤ A)(x:Family (tent Y H)),InTest K true T false x→Between (tent Y H) j (2*(ruler Λ.block*(uM r))) A T→ CompactArc T d→∀ C:ℝ,0<C→pay x C→
 ∀ n:ℕ, ‖E (s+r) (chambers j (uM r) 0 (stream Y H D s r f) x n)‖≤ wages K (duetCharge Y (s+r)) d A C * B^n:=by
 have pl:=zTurn Y H V s Q j w S hB f0 hw tf.whereTo B y q
 intro r d T A h x u e v C Hc hp n
 obtain ⟨S1,d'⟩:= BQueue.chambersS j (uM r) n 0 (train_queue Y H s Q f S f0 tf r) (BQueue.stay u Hc hp)
 have hr:= (hot_deck Y H V (s+r) Q _ S1 d').norm
 apply le_of_tendsto hr; exact (pl r n d A C h).mono fun i w=> w n le_rfl x T u e v hp
end turn
end YM.CF.Buffered.Afterglow.Tower.SlabMark
