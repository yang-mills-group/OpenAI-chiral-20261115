import YM.SU5.FiniteGaugeData.Tower.Baggage
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

/-! See the construction notes. Uniform forms of parts of Polity,
PureCap, plus queue compatibility for moving input. -/
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis){w:ℕ}{S:Finset Cover}(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
local notation "Z" u:max n:max k:max f:max=> train Y H s u n k S f
local notation "π" r:max=>i (a r)
local notation "ζ" r:max=> k (b r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
include V Q hB
lemma banner_every (r:ℕ): ∀ᶠ e:ℕ in atTop, ∀ {f:Family (tent Y H)}, InTest K true S false f → ∀ (n:ℕ)(v:ℤ), 2*(ruler Λ.block*w*n) ≤ (((T₀ (π e) s).val:ℕ):ℤ)→
 sharp Y H (s+r) (π e) (ζ e) (banner j (uM r) ((L₀:ℤ)^r*v) n (Z r (π e) (ζ e) f))=sharp Y H s (π e) (ζ e) (banner j w v n f):=by
 induction r with
 | zero=> exact Eventually.of_forall fun n f _ v p' k=>by simp [train]
 | succ r ih=>
    have hM:Tendsto (fun r=>π r) atTop atTop:= V.pick.grow_i.tendsto_atTop.comp Q.growsA.tendsto_atTop
    let X:=W (r+1); let S0:=W r
    let A:=s+r
    have ht:∀ᶠ e in atTop,Tivoli X ((K).c (m (π e) (A+1))) :=hM.eventually (turning Y H (A+1) X)
    filter_upwards [ih,Q.finance (s+r+1),ht] with e he ae hh f t n q v
    let M':ℕ:=π e; let k':ℕ:= ζ e
    let F:=Z r M' k' f
    have hs:InTest K true S0 false F := prepared_train Y H s S r _ _ t
    have Hs: Between K j 0 (ruler Λ.block * ((L₀:ℤ)^r*w)) S0 :=by rw [mul_left_comm]; exact expands_shape Y H hB r
    have he₁:legalAt Y A M' k':=⟨ae.depth,ae.enters⟩
    let F':=block Y H A M' k' S0 F
    have hx:Delivered Y H A M' k' F F':=⟨aux_test hs,aux_test (booked ..),reserved Y H A S0 M' k' he₁ hs hh⟩
    let U:ℤ:= (L₀:ℤ)^r
    have hy:2*(ruler Λ.block * (U*w) * n) ≤ (((T₀ M' A).val:ℕ):ℤ):=by
       unfold A; rw [refine_side,Nat.cast_mul,Nat.cast_pow]; have ht:0≤U:=by positivity
       rw [show 2*(ruler Λ.block *(U*w)*n)=U*(2*(ruler Λ.block*w*n)) from by ring]; exact mul_le_mul_of_nonneg_left v ht
    have hp:=delivering Y H A M' k' he₁ (bulk_lift Y H A M' k' j he₁ hx n ((L₀:ℤ)^r*q) hs Hs (by positivity) hy)
    rw [← he t n q v,←Nat.add_assoc s r, train_step]
    convert hp using 2 <;> push_cast <;> rw [pow_succ'] <;> congr 1 <;> ring
omit V Q hB

private lemma thinSuppressed {F:ℕ→ℕ}(v:Tendsto F atTop atTop)(q:ℝ)(x:0≤q): ∀ᶠ i in atTop,∀n:ℕ,n ≤ F i→ Real.exp (-((F i:ℕ):ℝ)^2)*(q^(4*n)) ≤ 1:=by
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
variable (Qt : Clipped Y H (i∘a) (k∘b))
include V Q Qt
lemma narrow_diff (s:ℕ)(C c:ℝ)(h:0≤C)(p:0<c) :
 ∀ᶠ e:ℕ in atTop,∀ n≤(T₀ (π e) s).val,∀ f:Family K,TestFamily K true f→ pay f (C^(4*n))→
 ‖sharp Y H s (π e) (ζ e) f-hot Y H s (π e) (ζ e) f‖ ≤ c^(4*n):= by
 filter_upwards [thinSuppressed (site_law Y H V Q s) (C/c) (by positivity),Qt s]
      with i a b n v f t w
 apply (b t _ w).trans
 specialize a n v
 rw [div_pow, ←mul_div_assoc] at a
 exact (div_le_one (show 0<c^(4*n) by positivity)).mp a

omit V Q Qt
/-- End-train hypothesis tested on the *input* cover. -/
def HotPrints (i k:ℕ→ℕ) (s:ℕ) (j:Axis) (w:ℕ)
    (F:ℕ→Family (tent Y H)) (θ:ℝ) : Prop :=
 ∀ᶠ e:ℕ in atTop, ∀ n:ℕ,∀ v:ℤ,
 0 < n → 2*(ruler Λ.block*w*n) ≤ (((T₀ (i e) s).val:ℕ):ℤ) →
    (((T₀ (i e) s).val:ℕ):ℤ) ≤ (4*(ruler Λ.block*w*n)) →
 ‖hot Y H s (i e) (k e) (banner j w (w*v) n (F e))‖ ≤ 2*θ^(4*n)
variable {F:ℕ→Family (tent Y H)}{f:Family (tent Y H)}{θ:ℝ}
       (hQ:BQueue S F f) (hθ:0<θ)
       (hs:HotPrints Y H (i∘a) (k∘b) s j w F θ)
       (hw:0<w)
include V Q Qt hQ hB hθ hs hw
lemma purchase_drop (r:ℕ):
 ∀ᶠ e:ℕ in atTop,∀ n:ℕ,∀ v:ℤ,
 0<n → 2*(ruler Λ.block*w*n) ≤ (((T₀ (π e) s).val:ℕ):ℤ) →
   (((T₀ (π e) s).val:ℕ):ℤ) ≤ (4*(ruler Λ.block*w*n)) →
 ‖hot Y H (s+r) (π e) (ζ e)
    (banner j (uM r) ((uM r)*v) n (Z r (π e) (ζ e) (F e)))‖
     ≤ ((2*θ)^2)^(2*n):=by

 obtain ⟨x,hx,_,cx⟩:=hQ.bdd
 obtain ⟨A,p₀,Tp⟩:=fares Y H s Q S r
 filter_upwards [Tp 1 one_pos,
    narrow_diff Y H V Q Qt s x θ hx.le hθ,
    narrow_diff Y H V Q Qt (s+r) (A*x) θ (by positivity) hθ,
    banner_every Y H V s Q j hB r, cx, hs]
     with e a b c t hxe h n v N hP hh
 let g := F e
 let u : ℤ := w*v
 let B := banner j w u n g
 let p : ℤ := uM r
 let B' := banner j p ((L₀:ℤ)^r*u) n (Z r (π e) (ζ e) g)
 have hp : 1 ≤ ruler Λ.block*w := by
    have h:=ruler_gene Λ.block; have t:1≤(w:ℤ):=by exact_mod_cast hw
    nlinarith
 have he1 : n≤(T₀ (π e) s).val := by apply Int.ofNat_le.mp; nlinarith [mul_le_mul_of_nonneg_right hp (show 0≤ (n:ℤ) by positivity)]
 have he2 : n≤(T₀ (π e) (s+r)).val := by
    rw [refine_side]; exact he1.trans (Nat.le_mul_of_pos_left _ (pow_pos Λ.R.L.property r))
 have tg : InTest K true S false g := hQ.whereTo e
 have t' := prepared_train Y H s S r (π e) (ζ e) tg
 obtain ⟨z,Z'⟩:=main_bill j w u n (aux_test tg) hxe
 obtain ⟨G,k'⟩:=main_bill j p ((L₀:ℤ)^r*u) n (aux_test t') ((a g tg _ hxe).2.1)

 have hu : ‖sharp Y H s (π e) (ζ e) B - hot Y H s (π e) (ζ e) B‖≤θ^(4*n):= b n he1 B z Z'
 have hv : ‖hot Y H (s+r) (π e) (ζ e) B' - sharp Y H s (π e) (ζ e) B‖≤θ^(4*n):=by
    have hg:sharp Y H (s+r) (π e) (ζ e) B'=sharp Y H s (π e) (ζ e) B:= t tg n u hP
    rw [←hg,norm_sub_rev]; exact c n he2 B' G k'
 have hk : ‖hot Y H s (π e) (ζ e) B‖ ≤ 2*θ^(4*n) := h n v N hP hh
 rw [mul_assoc (↑L₀^r:ℤ)]
 change ‖hot Y H (s+r) (π e) (ζ e) B'‖ ≤ _
 refine ((norm_le_norm_sub_add _ _).trans (add_le_add hv
     ((norm_le_norm_sub_add _ _).trans (add_le_add hu hk)))).trans ?_
 rw [←pow_mul,show 2*(2*n)=4*n from by omega, mul_pow]
 have hl : (2:ℝ)^2≤2^(4*n):=pow_le_pow_right₀ (by norm_num) (by omega)
 nlinarith only [mul_le_mul_of_nonneg_right hl (show 0≤θ^(4*n) by positivity)]

omit hB Qt hθ hs hw
lemma queue_next (r:ℕ) :
 BQueue (volumeAround Λ l r S) (fun e=>Z r (π e) (ζ e) (F e)) (stream Y H D s r f) := by
 obtain ⟨t,h,⟨x,hx,p,q⟩,hh⟩:=hQ
 obtain ⟨A,u,g⟩:= fares Y H s Q S r
 refine ⟨fun e=>prepared_train Y H s S r _ _ (t e),
       (proceeds Y H Q.circuit s r h).1, ⟨A*x,by positivity,?_,?_⟩,?_⟩
 · obtain ⟨e,he⟩:=(g 1 one_pos).exists; exact (he f h x p).1
 · filter_upwards [g 1 one_pos,q] with e v y; exact (v (F e) (t e) x y).2.1
 intro ε hp
 let δ:=ε/(A+x)
 have hd:0<δ:= by unfold δ; positivity
 filter_upwards [g δ hd,q,hh δ hd] with e hg h₁ h₂
 let U:=Z r (π e) (ζ e) (F e)
 let T:=stream Y H D s r
 have hu:pay (U-T (F e)) (δ*x):=(hg (F e) (t e) x h₁).2.2.1
 have he:pay (T (F e)-T f) (A*δ):= by
    have hy: T (F e-f)=T (F e)-T f:=by
       unfold T; rw [sub_eq_add_neg (F e), ← neg_one_smul ℂ f,woven_add Y H Q.circuit s r (aux_test (t e)) ((aux_test h).scale _),woven_smul Y H Q.circuit s r (aux_test h),neg_one_smul, sub_eq_add_neg]

    rw [←hy]; exact (hg _ (InTest.subOp (t e) h) δ h₂).1
 intro m' z; specialize hu m' z; specialize he m' z
 have ha:δ*(A+x)=ε:=div_mul_cancel₀ _ (by positivity)
 simp only [Pi.sub_apply] at hu he ⊢
 refine ((norm_sub_le_norm_sub_add_norm_sub (U m' z) (T (F e) m' z) (T f m' z)).trans (add_le_add hu he)).trans ?_
 linarith

end YM.CF.Buffered.Afterglow.Tower.SlabMark
