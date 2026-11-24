import YM.SU5.FiniteGaugeData.KernelP.Regular
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
open scoped NNReal ENNReal
open OS.Semigroup
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(X:Engine Y h W' R a H)(j:Axis)
local notation "M" s:max=> H.leaf s
local notation "F"=> H.space
local notation "T"=> X.val
local notation "Q" s:max=> X.val.onceL s a
local notation "G"=> regular Y h W' R a H X
include S' X
def time_aux : OS.Semigroup H.space a where
 E:= regular Y h W' R a H X
 U _:= 1 -- aux ONLY
 eZero:= regular_zero Y h W' R A S' a H X
 time:= regular_time Y h W' R A S' a H X
 sym t:= IsSelfAdjoint.of_nonneg (regular_nn Y h W' R a H X t)
 shrinks:= regular_bounds Y h W' R A S' a H X
 uZero:=rfl
 space _ _:=by ext1; rfl
 unitary _ _:= rfl
 independent t s:=by ext1; rfl
 continuousE v:= regular_all Y h W' R A S' a H X v
 continuousU v:= continuous_const
local notation "R₀"=> time_aux Y h W' R A S' a H X
def transitS: Spectral.Orbit H.space ℝ where
 translation:= (time_aux Y h W' R A S' a H X).edge
 origin:= (R₀).birth
 sends:= (R₀).send
 unitary:= (R₀).life
 moves:= (R₀).cont
abbrev prismS: Spectral.PVM H.space ℝ:= axis_spec (R₀)
local notation "τ"=> transitS Y h W' R A S' a H X
local notation "π"=> prismS Y h W' R A S' a H X

lemma transitS_data :(transitS Y h W' R A S' a H X).Spectrum (prismS Y h W' R A S' a H X):=by
 intro x b; rw [MeasureTheory.charFun_apply]; have he:=realHeat R₀ (b:ℂ) (by simp) x; rw [Complex.ofReal_im, Complex.ofReal_re,Real.toNNReal_zero,(R₀).eZero] at he; refine (?_ : _= (∫ p, Complex.exp ((↑p:ℂ)*(↑b)*(Complex.I)) ∂ (axis_spec (R₀)).diagonal x)).trans he.symm; apply integral_congr_ae; filter_upwards with t; simp [mul_comm]
abbrev Revolve (t:ℝ):= Spectral.Orbit.translation (transitS Y h W' R A S' a H X) t
lemma transitS_time (z:ℂ)(t:0≤z.im)(v:H.space) : inner ℂ v ((τ).translation z.re (regular Y h W' R a H X z.im.toNNReal v)) = ∫ p, Complex.exp ((↑p:ℂ)*z*Complex.I) ∂ (axis_spec (time_aux Y h W' R A S' a H X)).diagonal v := realHeat R₀ z t v
lemma transitS_purchase (x:F) : (Measure.support ((π).diagonal x)) ⊆ Set.Ici 0:= energyP ..
lemma regular_edge (t:ℝ)(z:ℤ)(p:Allows a j z): Commute ((τ).translation t) ((T).stepT s j z p):=by
 let v:= (T).stepT s j z p; let Q':=time_aux Y h W' R A S' a H X; let w:= OS.Semigroup.duration 1+ sideways t -- ambiguity
 have he:Commute (Q'.E 1) v:= regular_coin Y h s W' R a H X j 1 z p; have ht:Commute (Q'.F w) v:=(Q'.stare 1).commute_cfcHom (Q'.stare 1).isStarNormal he (Q'.roots w); change Q'.edge t*v=v*Q'.edge t; apply DFunLike.coe_injective; apply (Q'.whole 1).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _); funext y; change Q'.edge t (v (Q'.E 1 y))= _; rw [show v (Q'.E 1 y)=Q'.E 1 (v y) from congrArg (fun u:H.space.Op=>u y) he.eq.symm,Q'.high]; exact (congrArg (fun P:H.space.Op=> P y) ht.eq).trans (congrArg v (Q'.high _ y).symm)

variable (x:H.space)
lemma shoreUnity (p:x∈ X.val.Unity) : x∈ (time_aux Y h W' R A S' a H X).ground:=by
 let n:=time_aux Y h W' R A S' a H X
 have he(k:ℕ): n.E k x=x:=by
    change (G) k x=x; have hx:thetaX Λ 0 k=k:=by simp [thetaX,tassel]
    rw [← hx,atemporal Y h 0 W' R A S' a H X k]; exact (X.val.unityH x).1 p ..
 have h:n.orth x=x:= tendsto_nhds_unique ((n.emerges x).comp (tendsto_natCast_atTop_atTop (R:=ℝ≥0))) (tendsto_const_nhds.congr' (Eventually.of_forall fun k=> (he k).symm))
 exact (h ▸ n.ground.starProjection_apply_mem x)
lemma edge_fixed (h: x∈ X.val.Unity)(u:ℝ): (transitS Y _ W' R A S' a H X).translation u x=x:= real_fixed _ x (shoreUnity Y _ W' R A S' a H X x h) u
lemma party (p:∀ t:ℝ,(transitS Y h W' R A S' a H X).translation t x=x) :
      let μ':= (axis_spec (time_aux Y h W' R A S' a H X)).diagonal x
      μ' = (‖x‖₊^2:ℝ≥0) • Measure.dirac (0:ℝ) :=by
 intro ν; apply Measure.ext_of_charFun; funext u; rw [show charFun _ u=inner ℂ x ((τ).translation u x) from transitS_data Y h W' R A S' a H X x u,p,inner_self_eq_norm_sq_to_K]
 rw [charFun_apply_real, integral_smul_nnreal_measure, integral_dirac]; simp [NNReal.smul_def,Complex.real_smul]
lemma unity_real (p:∀t:ℝ,(transitS Y h W' R A S' a H X).translation t x=x):∀ t:ℝ≥0, regular Y h W' R a H X t x=x := by
 intro t; have he:= transitS_time Y h W' R A S' a H X (((t:ℝ):ℂ)*Complex.I) (by simpa [Complex.mul_im] using t.property) x
 simp only [Complex.mul_re,Complex.I_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Complex.mul_im,Complex.I_im, add_zero, zero_add,mul_one,Complex.ofReal_re] at he; rw [(τ).origin,ContinuousLinearMap.id_apply, Real.toNNReal_coe,party Y h W' R A S' a H X x p,integral_smul_nnreal_measure,integral_dirac] at he
 simp only [Complex.ofReal_zero, zero_mul,Complex.exp_zero,NNReal.smul_def, Complex.real_smul,mul_one,NNReal.coe_pow,coe_nnnorm, Complex.ofReal_pow] at he -- check
 let y:=(G) t x; have hx:inner ℂ y x=inner ℂ x x:=by nth_rw 1 [← inner_conj_symm]; change (starRingEnd ℂ) (inner ℂ x (regular Y h W' R a H X t x))= _; rw [he,inner_self_eq_norm_sq_to_K]; simp
 apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ) ((((G) t).le_of_opNorm_le (regular_bounds Y h W' R A S' a H X t) x).trans_eq (one_mul _)) ?_
 rw [show inner ℂ ((G) t x) x=inner ℂ x x from hx]; exact inner_self_eq_norm_sq ..
lemma core_real : x∈ X.val.Unity ↔ (∀ j:Axis,j≠a → ∀ (s:ℕ)(z:ℤ)(p:Allows a j z), X.val.stepT s j z p x=x) ∧ ∀ t:ℝ,(τ).translation t x=x := by
 constructor; intro p; exact ⟨fun i _ s z t=> (X.val.unityH _).1 p _ _ _ _,edge_fixed Y h W' R A S' a H X x p⟩
 intro v; refine (X.val.unityH _).2 fun s i z p=> ?_; by_cases h':i=a; swap; · exact v.1 i h' _ _ _
 subst i; obtain ⟨i,rfl⟩:=Int.eq_ofNat_of_zero_le (p rfl); exact Eq.trans (congrArg (fun f:H.space.Op=>f x) (atemporal Y h s W' R A S' a H X i).symm) (unity_real Y h W' R A S' a H X x v.2 _)
#print axioms core_real
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
