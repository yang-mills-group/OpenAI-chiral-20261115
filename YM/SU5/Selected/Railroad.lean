import YM.SU5.Selected.FullLattice
/-!
# The semigroup on native pitch. Selfadjoint & even advance exact.
Uses translation invariance just justified on actual elected history. Still
odd sign or taste ambiguity (no inference from even powers). Distances in
level0 matter spacings. Some proofs in this file adopt versions from `Ford.lean`
(collector bound coherent in s); we are using the very same E. No extension
of *spatial* assertion to full continuity. Future tool to seek small-motion
price or foundational translation/dispersion obligations. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
open Set MeshClock
local notation "Δ" v:max=> chime K j v
local notation "L"=> Λ.R.L.val
section connect
variable (s v u t:ℕ)
lemma advance_support {S:Finset Cover} (p:Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S):Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ (address j (v:ℤ) S):=by
 intro i y; obtain ⟨w,h,rfl⟩:= Finset.mem_image.mp y; specialize p w h; rw [moves,if_pos rfl]; omega
noncomputable def bout : (Fₛ s) →ₗ[ℂ] (Fₛ s) where
 toFun f:=⟨(Δ (v:ℤ)) f.val,(purpose_ok ..).2 (by
    obtain ⟨⟨a,p,q⟩,g⟩:=(purpose_ok ..).1 f.property; exact ⟨⟨_,flow_port K j (v:ℤ) p,advance_support Y H j s v q⟩,fun x=>chime_cov _ _ _ p (g x)⟩)⟩ -- notation nested membership dests check
 map_add' _ _:=Subtype.ext (chime_plus ..)
 map_smul' _ _:=Subtype.ext (chime_scale ..)
local notation "δ" s:max=>bout Y H j strict s
variable (x: Tower.Field Y H s j 0 strict)
lemma stride_sum : ((δ s) v) ((δ s) u x)=(δ s) (v+u) x:=Subtype.ext (by
 change _= (Δ ((v+u:ℕ):ℤ)) _; push_cast; exact Tower.bumps K j _ _ (field_test Y H s j 0 strict x).paid.choose_spec)
lemma stride_origin : (δ s) 0 x=x:=Subtype.ext (wake K j (field_test Y H s j 0 strict x).paid.choose_spec)
lemma stride_gauge : (δ s) (4*Λ.block.val*v) x=tick Y H s j 0 strict v x:=Subtype.ext (by change chime K j ((4*Λ.block.val*v:ℕ):ℤ) _=chime K j (Heat.gaugeShift Λ.block _) _; unfold Heat.gaugeShift; push_cast; rfl)

lemma acreage_X {F:Family K}(p:TestFamily K true F)(z:ℤ):stream Y H G.refine s t ((Δ z) F)=(Δ ((L:ℤ)^t*z)) (stream Y H G.refine s t F):=by
  unfold chime; rw [stream_flipped Y H G.history.circuit s t j _ (reflect_ok K j 0 p),stream_flipped Y H G.history.circuit s t j 0 p,mul_zero]
lemma stride_up (p:s≤t) : (δ t) (amount Λ s t v) (Raise Y H G.history.circuit j 0 strict s t p x)=Raise Y H G.history.circuit j 0 strict s t p ((δ s) v x):=by
 apply Subtype.ext; rw [show ((amount Λ s t v))=L^(t-s)*v from rfl]; change (Δ ((L^(t-s)*v:ℕ):ℤ)) _=stream Y H G.refine _ _ _; push_cast; exact (acreage_X Y H G j s (t-s) (field_test Y H s j 0 strict x) v).symm
include V
lemma bout_symmetric (y:Fₛ s): inner ℂ ((κ s) ((δ s) v x)) ((κ s) y)= inner ℂ ((κ s) x) ((κ s) ((δ s) v y)):=by
  rw [stems Y H V,stems Y H V, area0] -- binder args tune
  let Z:= field_test Y H s j 0 strict x; let h:=field_test Y H s j 0 strict y
  let t:= Z.paid.choose_spec; let v':ℤ:=v
  let T:=reflect_ok K j 0 (aux_test (flow_port K j v' t))
  change E s (mirror K j 0 ((Δ v') x.val)* y.val)=E s _
  rw [← shift_eFull Y H V j (T.mul h) v',chime_product,chime_diag K j v' 0 (flow_port K j v' t),Tower.bumps K j (-v') v' t, neg_add_cancel,Tower.wake K j t]; rfl
include C
local notation "Τ"=> bout Y H j strict s
local notation "m"=>meshface (Λ:=Λ) 0 s
lemma bout_uniform (f:Fₛ s):∃ B:ℝ, ∀ t:ℕ, ‖(κ s) (Τ t f)‖ ≤ B:=by
 have ht:= field_test Y H s j 0 strict f
 obtain ⟨S,w⟩:= ht.paid
 obtain ⟨d,a⟩:=Tower.sizes S
 obtain ⟨X,x⟩:=Journey.valuation Y H w; have hx:pay f.val X:=x
 let B:=closefare K (duetCharge Y s) d*(X*X); refine ⟨B+1,fun t=>?_⟩
 let g:= (Τ t f).val
 let S':= reflectedBox j ((t:ℤ)) (reflectedBox j 0 S)
 have hg:InTest K true S' false g:=axial K j _ (axial K j 0 w)
 have H':CompactArc S' d:= (a.reflBox S j 0).reflBox _ j _
 have hp:= pair_budget Y H V s d (axial K j m hg) hg (H'.reflBox S' j m) H' X X (pay_flips K (chime_pay K j _ X hx) j m) (chime_pay K j _ X hx)
 let u₀:= (κ s) (Τ t f); have he: ‖inner ℂ u₀ u₀‖ ≤ B:= (stems Y H V G.history.circuit j 0 strict C s _ _).symm ▸ hp -- z shadow
 have hr:‖inner ℂ u₀ u₀‖=‖u₀‖^2:=by
    rw [inner_self_eq_norm_sq_to_K,norm_pow]; change ‖((‖u₀‖:ℝ):ℂ)‖^2= _; simp
 change ‖u₀‖≤_; rw [hr] at he; nlinarith [norm_nonneg u₀]

lemma concedes (t:ℕ)(f:Fₛ s): ‖(κ s) (Τ t f)‖≤‖(κ s) f‖:= by
 let X(i:ℕ):= (κ s) (Τ i f)
 obtain ⟨d,v⟩:= bout_uniform Y H V G j strict C s f
 let S:Set ℝ:= Set.range fun (i:ℕ)=> ‖X i‖
 have hS(x:ℕ): ‖X x‖∈ S:=Set.mem_range_self x
 have p: BddAbove S:= ⟨d, by rintro _ ⟨i,rfl⟩; exact v i⟩
 let B:= sSup S
 have he(i):‖X i‖≤ B:=le_csSup p (hS i)
 have hB:0≤ B:=(norm_nonneg _).trans (he t)
 let c:=‖(κ s) f‖; have hc:0≤c:=norm_nonneg _
 have h(i:ℕ): ‖X i‖^2≤ c*B:=by
    have ht:‖X i‖^2= ‖inner ℂ (X i) (X i)‖:=by rw [inner_self_eq_norm_sq_to_K,norm_pow]; change _=‖((‖X i‖:ℝ):ℂ)‖^2; simp
    change ‖X i‖^2 ≤ c*B; rw [ht, show inner ℂ (X i) (X i)=inner ℂ ((κ s) f) (X (i+i)) from (bout_symmetric Y H V G j strict C s i f (Τ i f)).trans (congrArg _ (congrArg (κ s) (stride_sum Y H j strict s i i f)))]
    exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (he (i+i)) hc)
 refine (he t).trans ?_
 have ht:B ≤ Real.sqrt (c*B):=csSup_le ⟨_,hS t⟩ (by rintro _ ⟨i,rfl⟩; exact Real.le_sqrt_of_sq_le (h i))
 have h':= Real.sq_sqrt (mul_nonneg hc hB); change B ≤ c; nlinarith [Real.sqrt_nonneg (c*B)]

end connect

local notation "δ" s:max=>bout Y H j strict s
variable (s v n:ℕ)
include V v in
noncomputable def weldT : Lamination Y H s G.history.circuit j 0 strict C where
 go t z:= (δ t) (amount Λ s t v)
 weak t _ x:= concedes Y H V G j strict C t _ x
 same t r h p x:=by rw [← stride_up Y H G j strict t (amount Λ s t v) r x p, amount_grew Λ s t r v h p]
include V v in
noncomputable def weld : A →L[ℂ] A := onship Y H V s G.history.circuit j 0 strict C (weldT Y H V G j strict C s v)
local notation "Ρ" s:max=> weld Y H V G j strict C s
local notation "Q"=>advance Y H V G.history.circuit j 0 strict C
local notation "M"=>timeMesh Λ
lemma weld_at {t:ℕ}(p:s≤t)(x:Fₛ t) : (Ρ s) v ((κ t) x)=(κ t) ((δ t) (amount Λ s t v) x):= todeck Y H V s G.history.circuit j 0 strict C (weldT Y H V G j strict C s v) p x
lemma weld_up {t:ℕ}(p:s≤t): (Ρ s) v=(Ρ t) (amount Λ s t v):=by
 apply test_high Y H V t G.history j strict C; intro r h x; rw [weld_at Y H V G j strict C s v (p.trans h),weld_at Y H V G j strict C t (amount Λ s t v) h, amount_grew Λ s t r v p h]
lemma weld_source: (Ρ s) 0=1:=by
 apply test_high Y H V s G.history j strict C; intro t h x; rw [weld_at Y H V G j strict C s 0 h, amount, mul_zero, stride_origin]; rfl
lemma weldsum (w:ℕ): (Ρ s) v*(Ρ s) w=(Ρ s) (v+w):=by
 apply test_high Y H V s G.history j strict C; intro t h x; change (Ρ s) v ((Ρ s) w _)= _; rw [weld_at Y H V G j strict C s w h,weld_at Y H V G j strict C s v h,weld_at Y H V G j strict C s (v+w) h,amount_add,stride_sum]
lemma weldself : star ((Ρ s) v)=(Ρ s) v:=by
 apply test_high Y H V s G.history j strict C; intro t p x
 apply all_voices Y H G.history.circuit j 0 strict C; intro r y
 let m:=max r s; have h:r≤ m:= le_max_left ..; have hh:s ≤ m:= le_max_right ..; let u:= max r t; have hv:t≤ u:=le_max_right ..; have ht:r≤u:=le_max_left ..
 change inner ℂ _ (ContinuousLinearMap.adjoint _ _) = _
 rw [←join_actor Y H V G.history.circuit j 0 strict C t u hv,←join_actor Y H V G.history.circuit j 0 strict C r u ht,ContinuousLinearMap.adjoint_inner_right]
 simp only [weld_at Y H V G j strict C s v (p.trans hv)]
 exact bout_symmetric Y H V G j strict C ..
lemma weld_tick : (Ρ s) (4*Λ.block.val*v)=ripple Y H V s G.history.circuit j 0 strict C v := by
 apply test_high Y H V s G.history j strict C; intro t h x
 rw [weld_at Y H V G j strict C s _ h x, limited_time Y H V s G.history.circuit j 0 strict C v h x,show amount Λ s t (4*Λ.block.val*v)=4*Λ.block.val*amount Λ s t v by unfold amount; ring,stride_gauge]
noncomputable def pitchMill (Λ:Preparation)(s v:ℕ):ℝ≥0:=v/((Λ.R.L.val:ℝ≥0)^s)
lemma pitch_scaled (Λ:Preparation)(s v:ℕ):whenly (timeMesh Λ) s v=(8*Λ.block.val) • pitchMill Λ s v:=by
 change (v:ℝ≥0)*(8*(Λ.block.val:ℝ≥0)/_) = ((8*Λ.block.val:ℕ)) • pitchMill Λ s v
 rw [nsmul_eq_mul]; unfold pitchMill; push_cast; dsimp only [timeMesh]; ring
lemma weld_clock : (Ρ s) (2*v)= Q (pitchMill Λ s (2*v)):= by
  let n:=Λ.block.val; let T:=(Ρ s) (2*v); let t:=pitchMill Λ s (2*v)
  have ht: (2*n) • t= whenly M s v/2:=by
    rw [pitch_scaled]; simp only [pitchMill,t,nsmul_eq_mul, Nat.cast_mul,Nat.cast_ofNat,n]; ring
  have h: Q ((2*n) • t)=T^(2*n):=by
    rw [ht,undoubles Y H V G j strict C s v,←weld_tick]; unfold T; rw [power_stride, show 4*(Λ.block.val)*v=(2*v)*(2*n) from by unfold n; ring]
  have hs(k:ℕ):Q (k • t)=(Q t)^k:=by -- k : ℕ
    induction k with
    |zero=> rw [zero_smul,advance_source,pow_zero]; rfl
    |succ k ih=> rw [add_smul,one_smul,advance_smag, ih,pow_succ]; rfl
  have he:0 ≤ T:=by
    unfold T; rw [two_mul,←weldsum]; nth_rw 1 [← weldself Y H V G j strict C s v]; exact star_mul_self_nonneg ((Ρ s) v)
  exact symmetryX Λ s (n:=2*n) (by unfold n; positivity) (a:=T) he (b:=Q t) (warm_nonneg Y H V G j strict C t) (h.symm.trans (hs (2*n)))
where power_stride (v k:ℕ): ((Ρ s) v)^k=(Ρ s) (v*k):= by
        induction k with | zero=> rw [pow_zero,mul_zero,weld_source] | succ k ih=> rw [pow_succ,ih,Nat.left_distrib,mul_one,weldsum]
      symmetryX (Λ:Preparation)(s:ℕ){W:Hilbert}{n:ℕ}(p:0<n) {a b:W.Op}(ha:0 ≤ a)(hb:0 ≤ b) (x:a^n=b^n):a=b:=by
        have h:0 < (n:ℝ≥0):=by exact_mod_cast p
        have ht : a^(n:ℝ≥0)=b^(n:ℝ≥0):=by
          rw [CFC.nnrpow_eq_rpow h, CFC.nnrpow_eq_rpow h]; push_cast; rw [CFC.rpow_natCast a n ha, CFC.rpow_natCast b n hb]; exact x
        exact (CFC.nnrpow_nnrpow_inv a h.ne' ha).symm.trans ((congrArg (fun a:W.Op=> a^((n:ℝ≥0)⁻¹)) ht).trans (CFC.nnrpow_nnrpow_inv b h.ne' hb))
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.weld_clock
