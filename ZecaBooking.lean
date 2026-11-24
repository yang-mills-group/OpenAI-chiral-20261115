import ZecaDrop
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
set_option linter.unusedSectionVars false
set_option linter.style.whitespace false
set_option maxHeartbeats 800000

/-! Adapt EndTrain.interpolant, Baggage.baggageH to moving input, explicit bill.
Also reindexing. -/
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis)(w:ℕ){Fz:ℕ→Family (tent Y H)}{f:Family (tent Y H)}(S:Finset Cover)(t:BQueue S Fz f)
       {θ:ℝ}(hθ:0<θ)
       (hs:HotPrints Y H (i∘a) (k∘b) s j w Fz θ)
     (hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
local notation "Z" u:max r:max=> train Y H s u (π r) (ζ r) S (Fz r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
local notation "b₀"=>ruler Λ.block
variable (Qt : Clipped Y H (i∘a) (k∘b))(hw:0 < w)


private lemma zCount (n B:ℕ)(hB:0<B)(p:2*B≤n):
 let k:=finalN n B; 0 < k ∧ 2*B*k≤ n∧ n ≤ 2*B*k+2*B∧ n ≤ 4*B*k:=by
 intro k
 have h:0< k:= Nat.div_pos p (by positivity)
 have ht:=Nat.mod_add_div n (2*B); have he:=Nat.mod_lt n (by positivity:0<2*B); unfold k finalN at *
 obtain ⟨a,d⟩:= And.intro (by omega :2*B*(n/(2*B))≤n) (by omega : n<2*B*(n/(2*B))+2*B)
 exact ⟨h,a,d.le,(by nlinarith)⟩

include V Q t hB Qt hw hθ hs
lemma interpolant_moving_price:∀ (r N:ℕ)(d:ℕ) (A:ℤ)(c:ℝ)(p':0≤A),∀ᶠ e:ℕ in atTop,
 ∀ n:ℕ,n≤ N→∀ (x:Family K) (X:Finset Cover), InTest K true X false x→Between (tent Y H) j (2*(b₀*(uM r))) A X→ CompactArc X d→pay x c→
 ‖hot Y H (s+r) (π e) (ζ e) (chambers j (uM r) 0 (Z r e) x n)‖ ≤ wages K (duetCharge Y (s+r)) d A c * ((2*θ)^2)^n:=by
 let C:ℝ:=(2*θ)^2; have y:0<C:=by unfold C; positivity
 have q:= purchase_drop Y H V s Q j hB Qt t hθ hs hw
 intro i' nT d R0 c hc
 let r:=i'; let z:= s+i'
 let N0(e:ℕ):= (T₀ (π e) s).val
 let Nr(e:ℕ):=(T₀ (π e) (s+r)).val

 obtain ⟨k',hF,v⟩:= fares Y H s Q S i'
 let u:ℕ:=16*Λ.block.val*w
 let p:ℕ:=uM i'
 have he':b₀*w=(u:ℕ):=by unfold u ruler; push_cast; rfl
 have hr:u>0:=by unfold u; have h:= Λ.block.property; positivity
 have hs: b₀*p=(↑(u*L₀^r):ℤ):=by unfold p; push_cast; rw [mul_left_comm,he']; ring
 let mant(e:ℕ):= (K).c (m (π e) z)
 have hg:Tendsto (fun e=>(mant e).val) atTop atTop:=by unfold mant;simp_rw [side_register]; exact site_law Y H V Q z
 filter_upwards [q i', site_law Y H V Q s|>.eventually_ge_atTop (2*u*(1+nT)), hg.eventually_ge_atTop (widthPair K (rim_width R0 d)+addgap K), hg.eventually_ge_atTop (widthPair K d+addgap K),
     hg.eventually_ge_atTop (2*R0.toNat),v 1 zero_lt_one,Q.finance z] with j0 qp hj hR hD hv hh zf n hb x X t' hZ Dn hp
 let F:=Z i' j0
 have hB1:InTest K true (W i') false F:=prepared_train Y H s S i' (π j0) (ζ j0) (t.whereTo j0)
 obtain ⟨a0,hA⟩:=Journey.valuation Y H (t.whereTo j0)
 let N:= finalN (N0 j0) u
 let H0:= mant j0
 have hP: H0.val=L₀^r*N0 j0:=by unfold H0 mant; rw [side_register,refine_side]
 obtain ⟨hN,hM,hE,HM⟩:=zCount (N0 j0) u hr (by
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
    push_cast
    apply qp N j' hN
    · rw [mul_assoc, ←mul_assoc b₀, he'] -- bad
      rw [←mul_assoc]; exact_mod_cast hM
    rw [he']; convert (show _ from (by exact_mod_cast HM : (((T₀ (π j0) s).val:ℕ):ℤ)≤4*(u:ℤ)*(N:ℕ))) using 1; ring
 have pat:=booking (p:=boxprice Y H (π j0) (ζ j0) zf.depth z zf.fire zf.enters) j _ hpp hB1 hT t' R0 (x:= X) hZ hc N C d y hp ((hh (Fz j0) (t.whereTo j0) a0 hA).2.1) Dn hR hD hL hL' (add_comm _ R0 ▸ hv') (fun i=> by have ht':=ht i; unfold hot at ht'; rw [dif_pos zf.depth] at ht'; exact ht')
 have hn:n≤N:=hb.trans (by unfold N finalN; apply Nat.le_div_iff_mul_le (by positivity) |>.mpr ; change _ ≤ N0 j0; exact le_trans (by nlinarith) hj)
 have h:= pat _ hn; unfold hot; rw [dif_pos zf.depth]; -- adjust casts in goal p polymorphism
 convert h using 3 -- tune
 unfold worth p z; rw [Nat.cast_mul,Nat.cast_pow]


omit hs hθ hw Qt Q V hB t
def Lading (E:ℕ→Family (tent Y H)→ℂ)(D:ℕ→Family (tent Y H)→Family (tent Y H))(s:ℕ) (j:Axis) (w:ℕ) (f:Family (tent Y H)) (B:ℝ): Prop :=
 0<B∧∀ (r d:ℕ)(T:Finset Cover)(A:ℤ)(h:0 ≤ A)(x:Family (tent Y H)),InTest K true T false x→Between (tent Y H) j (2*(ruler Λ.block*((L₀:ℤ)^r*w))) A T→ CompactArc T d→∀ C:ℝ,0<C→pay x C→
 ∀ n:ℕ, ‖E (s+r) (chambers j ((L₀:ℤ)^r*w) 0 (stream Y H D s r f) x n)‖≤ wages K (duetCharge Y (s+r)) d A C * B^n

include V Q t hB Qt hw hθ hs
lemma make_lading : Lading Y H E D s j w f ((2*θ)^2):=by
 have p:=interpolant_moving_price Y H V s Q j w S t hθ hs hB Qt hw
 refine ⟨by positivity,fun r d T A h x u e v C Hc hp n=>?_⟩
 obtain ⟨S1,d'⟩:= BQueue.chambersS j (uM r) n 0 (queue_next Y H V s Q t r) (BQueue.stay u Hc hp)
 have hr:= (hot_deck Y H V (s+r) Q _ S1 d').norm
 apply le_of_tendsto hr
 exact (p r n d A C h).mono fun i hw=> hw n le_rfl x T u e v hp

omit V t hB hw hθ hs Qt
lemma reroute {σ:ℕ→ℕ}(h:StrictMono σ):
   Coherent (i:=i) (k:=k) (E:=E) Y H D (a∘σ) (b∘σ):=
 ⟨Q.circuit,Q.growsA.comp h,Q.growsB.comp h,fun e=>Q.gate _,
   fun s=>h.tendsto_atTop.eventually (Q.finance s),
   fun s S=>by
     obtain ⟨c,p,t⟩:=Q.implements s S
     exact ⟨c,p,fun e he=>h.tendsto_atTop.eventually (t e he)⟩⟩
end YM.CF.Buffered.Afterglow.Tower.SlabMark
