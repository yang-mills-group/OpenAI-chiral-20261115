import YM.CF.Buffered.Hilbert

/-! algebra of bounded Borel kernels for rectangle-trace comparison -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Stack
open Function Lattice RG Finset MeasureTheory Push.SectorMeasure
open scoped BigOperators ENNReal Topology InnerProductSpace ComplexOrder

variable {X : Type*} [MeasurableSpace X]


-- no one
structure Kern (μ : Measure X) where
  Q : X×X → ℂ
  paid : Envelope Q

namespace Kern
variable {μ : Measure X} [IsFiniteMeasure μ]
omit [IsFiniteMeasure μ] in
@[ext] lemma ext (F G : Kern μ) (h : F.Q=G.Q) : F=G:= by cases F; cases G; congr
instance : CoeFun (Kern μ) fun _=> X × X→ ℂ := ⟨Kern.Q⟩
omit [IsFiniteMeasure μ] in
@[simp] lemma Q_apply (F : Kern μ) (x:X×X) : F.Q x=F x := rfl

instance : Star (Kern μ) := ⟨fun f => ⟨HS.dual f.Q, HS.envDual f.paid⟩⟩
omit [IsFiniteMeasure μ] in
@[simp] lemma star_at (F : Kern μ) (x:X×X) : (star F) x=star (F x.swap) := rfl

end Kern
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
-- generalize to finite marg for integration over counting x prob
lemma marginal {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (f:X×Y→V) (h:Envelope f) (ν:Measure Y) [IsFiniteMeasure ν] : Envelope fun x=>∫ y,f (x,y)∂ν := by
 obtain ⟨C,p⟩:=h.cost; exact ⟨h.meas.stronglyMeasurable.integral_prod_right'.measurable,C*ν.real Set.univ,fun x=> norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun i=>p (x,i))⟩ -- tune

namespace Kern
variable [IsFiniteMeasure μ]
def ravel (F G : Kern μ) : Kern μ := ⟨fun x=>∫ z,F (x.1,z)*G (z,x.2)∂μ,
 marginal (fun i:(X×X)×X=>F (i.1.1,i.2)*G (i.2,i.1.2)) (env_mult (Env.along F.paid ((measurable_fst.comp measurable_fst).prodMk measurable_snd)) (Env.along G.paid (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))) _⟩

instance : Mul (Kern μ) := ⟨ravel⟩
@[simp] lemma mul_at (F G : Kern μ) (x:X×X) : (F*G) x=(∫ z,F (x.1,z)*G (z,x.2)∂μ) := rfl

private lemma multiply (F G H : Kern μ) : F*G*H=F*(G*H) := by
 apply ext; funext x; simp_rw [mul_at,←integral_mul_const,←integral_const_mul,mul_assoc]
 let h : Envelope (fun p:X×X=> F (x.1,p.2)*(G (p.2,p.1)*H (p.1,x.2))) := env_mult (Env.along F.paid (measurable_const.prodMk measurable_snd)) (env_mult (Env.along G.paid measurable_swap) (Env.along H.paid (measurable_fst.prodMk measurable_const)))
 exact integral_integral_swap (Env.integrableX (f:=fun p:X×X=> F (x.1,p.2)*(G (p.2,p.1)*H (p.1,x.2))) h (μ.prod μ))
instance : Semigroup (Kern μ) where
 mul_assoc:=multiply

private lemma dual_shift (F G : Kern μ) : star (F*G)=star G*star F:=by
 apply ext; funext x; simp_rw [star_at]
 rw [mul_at, ←starRingEnd_apply,←integral_conj (𝕜:=ℂ)]; simp [star_mul,mul_comm]

instance : StarMul (Kern μ) where
 star_involutive x := by ext z; simp
 star_mul:=dual_shift

def τ (F : Kern μ) := ∫ x,F (x,x)∂μ -- this ISN'T trace on single kernel; only multiplied ones use
lemma τ_prod (F G : Kern μ) : τ (F*G)= HS.trace μ F.Q G.Q := by
 unfold τ HS.trace; rw [integral_prod]; simp; exact Env.integrableX (env_mult F.paid (Env.along G.paid measurable_swap)) _
lemma τ_cycle (F G : Kern μ) : τ (F*G)=τ (G*F) := by
 rw [τ_prod,τ_prod]; unfold HS.trace; rw [←integral_prod_swap (μ:=μ) (ν:=μ) (f:=fun p:X×X=> G.Q p*F.Q p.swap)]; simp [mul_comm]

lemma τ_pos (F : Kern μ): 0 ≤ τ (F*star F) := by
 rw [τ_prod]; exact integral_nonneg fun x=> mul_star_self_nonneg (F x)

variable (μ) in
private def sqnorm (f : X → ℂ) := ∫ x, ‖f x‖^2 ∂μ
local notation "⟪" x "," y "⟫" => inner ℂ x y
private def vec (f : X→ℂ) (h : Envelope f) (μ : Measure X)[IsFiniteMeasure μ] : HS.Hilb μ:= MemLp.toLp _ (MemLp.of_bound h.meas.aestronglyMeasurable _ (Filter.Eventually.of_forall h.cost.choose_spec))
private lemma pairing (f g : X→ℂ) (h: Envelope f)(p : Envelope g) : ⟪vec f h μ,vec g p μ⟫=(∫ i,g i*star (f i)∂μ):=by
 unfold vec; rw [L2.inner_def]; apply integral_congr_ae
 filter_upwards [show (vec f h μ).val=ᵐ[μ] f from MemLp.coeFn_toLp _, show (vec g p μ).val=ᵐ[μ] g from MemLp.coeFn_toLp _] with i u v
 unfold vec at u v; rw [u,v,RCLike.inner_apply,starRingEnd_apply]
private lemma norm_vec (f : X→ℂ) (h : Envelope f) : ‖vec f h μ‖^2 = sqnorm μ f := by
 have he:= pairing (μ:=μ) f f h h
 rw [inner_self_eq_norm_sq_to_K] at he
 apply Complex.ofReal_injective; change ((‖vec f h μ‖^2:ℝ):ℂ)= _; rw [Complex.ofReal_pow, (show (↑‖vec f h μ‖:ℂ)^2 = _ from he),sqnorm,← integral_complex_ofReal]
 apply integral_congr_ae; refine Filter.Eventually.of_forall fun x=>?_ ; dsimp only; rw [←starRingEnd_apply, ← RCLike.inner_apply, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; rfl

def count (F : Kern μ) := ‖vec F.Q F.paid (μ.prod μ)‖^2
lemma count_nonneg (F : Kern μ) : 0 ≤ count F := sq_nonneg _
lemma count_eq (F : Kern μ) : count F=∫ x,‖F x‖^2∂μ.prod μ := norm_vec ..
lemma τ_inner (F G : Kern μ) : τ (F*star G)=⟪vec G.Q G.paid (μ.prod μ),vec F.Q F.paid (μ.prod μ)⟫ := by
 rw [τ_prod,pairing]; simp [HS.trace]
lemma τ_count (F : Kern μ) : τ (F * star F)=(count F:ℂ):=by rw [τ_inner,inner_self_eq_norm_sq_to_K,count, Complex.ofReal_pow]; rfl
lemma τ_count' (F : Kern μ) : ‖τ (F * star F)‖=count F:=by rw [τ_count, Complex.norm_real, Real.norm_of_nonneg (count_nonneg _)]
lemma τ_schwarz (F G : Kern μ) : ‖τ (F * star G)‖^2 ≤ count G*count F:=by
 rw [τ_inner]; exact (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm ..) 2).trans_eq (mul_pow ..)

private lemma rowCS (f g : X→ℂ) (h: Envelope f)(p : Envelope g) : ‖∫ x,f x*g x∂μ‖^2 ≤ sqnorm μ g * sqnorm μ f := by
 let G(x):=star (g x); let e:Envelope G:= Girt.pole_w _ star continuous_star p
 have hv: sqnorm μ g=sqnorm μ G:=by simp [G,sqnorm]
 have ht: ⟪vec G e μ,vec f h μ⟫ = ∫ x,f x*g x∂μ:= by rw [pairing]; simp [G]
 rw [←ht,hv, ←norm_vec _ e, ←norm_vec _ h]; exact (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm ..) 2).trans_eq (mul_pow ..)
lemma count_mul (F G : Kern μ) : count (F*G) ≤ count F*count G := by
 have he (F:Kern μ): Envelope (fun x => ‖F x‖^2) := Girt.pole_w _ (fun x :ℂ=> ‖x‖^2) (continuous_id.norm.pow 2) F.paid
 let l (x y : X):=‖F (x,y)‖^2
 let r (x y : X):=‖G (x,y)‖^2
 rw [count_eq, count_eq,count_eq,integral_prod _ (Env.integrableX (he F) (μ.prod μ)), integral_prod_symm _ (Env.integrableX (he G) (μ.prod μ)),← integral_prod_mul (fun x=> ∫ y,l x y∂μ) (fun y=> ∫ x,r x y∂μ)]
 apply integral_mono (Env.integrableX (he (F*G)) _) ((Env.integrableX (he F) (μ.prod μ)).integral_prod_left.mul_prod (Env.integrableX (he G) (μ.prod μ)).integral_prod_right)
 intro x; dsimp only; rw [mul_at]; apply (rowCS _ _ (Env.along F.paid (measurable_const.prodMk measurable_id)) (Env.along G.paid (measurable_id.prodMk measurable_const))).trans_eq (mul_comm ..)
end Kern
end YM.CF.Buffered.Stack
