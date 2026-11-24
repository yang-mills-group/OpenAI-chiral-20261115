import YM.SU5.Reconstruction.Cashier.Every
/-! Variant of EndTrain for our UNIFORM price & moving probe. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
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
variable (a0:ℝ)(hA:∀ i,pay (f i) a0)(wage:Rolls Y H s G f w)(hw:0 < w)

private lemma finalCount (n B:ℕ)(hB:0<B)(p:2*B≤n):
 let k:=finalN n B; 0 < k ∧ 2*B*k≤ n∧ n ≤ 2*B*k+2*B∧ n ≤ 4*B*k:=by
 intro k
 have h:0< k:= Nat.div_pos p (by positivity)
 have ht:=Nat.mod_add_div n (2*B); have he:=Nat.mod_lt n (by positivity:0<2*B); unfold k finalN at *
 obtain ⟨a,d⟩:= And.intro (by omega :2*B*(n/(2*B))≤n) (by omega : n<2*B*(n/(2*B))+2*B)
 exact ⟨h,a,d.le,(by nlinarith)⟩

include V t hB wage hw hA
lemma gets : ∀ (r N:ℕ)(d:ℕ) (A:ℤ)(c:ℝ)(p':0≤A),∀ᶠ e:ℕ in atTop,
 ∀ n:ℕ,n≤ N→∀ (x:Family K) (X:Finset Cover), InTest K true X false x→Between (tent Y H) j (2*(b₀*(uM r))) A X→ CompactArc X d→pay x c→
 ‖hot Y H (s+r) (π e) (ζ e) (chambers j (uM r) 0 (Z r e) x n)‖ ≤ wages K (duetCharge Y (s+r)) d A c * rate^n:=by
 intro i' nT d R0 c hc
 let C:=rate; have y:0<C:=pennies
 let q:= allAlong Y H V s j hB a0 G f t hA wage hw i'
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
 -- casts: uM occurs polymorphic in qp: because w : Nat and casts forced by banner, exponent powers INT!
 have ht(j':ℤ): ‖hot Y H z (π j0) (ζ j0) (banner j (p:ℕ) ((p:ℤ)*j') N F)‖ ≤ C^(2*N) := by
    unfold p F
    push_cast; rw [mul_assoc (↑L₀^i':ℤ)]
    apply qp N ((w:ℤ)*j') hN
    · rw [mul_assoc, ←mul_assoc b₀, he'] -- bad
      rw [←mul_assoc]; exact_mod_cast hM
    rw [he']; convert (show _ from (by exact_mod_cast HM : (((T₀ (π j0) s).val:ℕ):ℤ)≤4*(u:ℤ)*(N:ℕ))) using 1; ring
 have pat:=booking (p:=boxprice Y H (π j0) (ζ j0) zf.depth z zf.fire zf.enters) j _ hpp hB1 hT t' R0 (x:= X) hZ hc N C d y hp ((hh (f j0) (t j0) a0 (hA j0)).2.1) Dn hR hD hL hL' (add_comm _ R0 ▸ hv') (fun i=> by have ht':=ht i; unfold hot at ht'; rw [dif_pos zf.depth] at ht'; exact ht')
 have hn:n≤N:=hb.trans (by unfold N finalN; apply Nat.le_div_iff_mul_le (by positivity) |>.mpr ; change _ ≤ N0 j0; exact le_trans (by nlinarith) hj)
 have h:= pat _ hn; unfold hot; rw [dif_pos zf.depth]; -- adjust casts in goal p polymorphism
 convert h using 3 -- tune
 unfold worth p z; rw [Nat.cast_mul,Nat.cast_pow]


end YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.gets
