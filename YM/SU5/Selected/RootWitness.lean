import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
/-!
# Rank-one ground check in normed crossed slabs: representation-free limit

This part abstracts some tools, no specific space or label. A test `J`, the average
of countably many model-specific contractions, is used to select their joint 1-eigenspace.
Powers are not essential: Cesàro range graining of this single contractive element tells
which ground characters actually give EXTREMAL vacuum states on the slab sample C⋆-algebra.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric Complex
open scoped Topology ComplexOrder InnerProductSpace BigOperators Classical

variable {A H : Type*} [CStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
section positivity
variable [PartialOrder A] [StarOrderedRing A]
private lemma lift_nonneg {B : Type*}[CStarAlgebra B] (j : B →⋆ₐ[ℂ] A) (h : Injective j) (b : B)
    (p : 0 ≤ j b) : b ∈ AddSubmonoid.closure (Set.range fun s => star s * s) := by
  letI := CStarAlgebra.spectralOrder B; haveI := CStarAlgebra.spectralOrderedRing B
  rw [← StarOrderedRing.nonneg_iff]
  have e : IsSelfAdjoint b := h (by rw [map_star,p.star_eq])
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R:=ℝ) b e, ← e.map_spectrum_real j h]
  exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R:=ℝ) _ p.isSelfAdjoint).mp p
lemma sub_positive (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] : StarOrderedRing S := by
  apply StarOrderedRing.of_nonneg_iff (fun {x y} h z => show (z:S)+x ≤ z+y from ?_) (fun x=>?_)
  · change z.val + x.val ≤ z.val + y.val; exact add_le_add_right (show x.val≤y.val from h) _
  constructor
  · exact fun h=> lift_nonneg S.subtype Subtype.val_injective x h
  intro p
  change (0:A)≤x.val
  induction p using AddSubmonoid.closure_induction with
  | zero=> exact le_rfl
  | mem s hs=> obtain ⟨s,rfl⟩:=hs; exact star_mul_self_nonneg (s:S).val
  | add x y _ _ a b=> exact add_nonneg a b
end positivity
section average
variable (b : ℕ → A) (h : ∀ n, ‖b n‖ ≤ 1)
def grades (n : ℕ) := ((2:ℝ)⁻¹)^(n+1)
lemma grades_pos (n : ℕ) : 0 < grades n:= pow_pos (by norm_num) _
lemma grades_hasSum : HasSum grades 1 := by
  have h := (hasSum_geometric_of_norm_lt_one (ξ:=(2:ℝ)⁻¹) (by norm_num)).mul_right (2:ℝ)⁻¹
  simp_rw [show grades = (fun i : ℕ=> ((2:ℝ)⁻¹)^i*(2:ℝ)⁻¹) from funext fun i=> pow_succ ..]; convert! h using 1; norm_num
noncomputable def cog : A := ∑' n : ℕ, ((grades n):ℂ) • b n
include h
lemma cog_hasSum : HasSum (fun n=> ((grades n):ℂ) • b n) (cog b) := by
  apply Summable.hasSum; apply Summable.of_norm_bounded grades_hasSum.summable
  intro n; simpa [norm_smul, abs_of_pos (grades_pos n)] using
    (mul_le_of_le_one_right (grades_pos n).le (h n))
lemma cog_norm_le : ‖cog b‖ ≤ 1 := by
  apply le_of_tendsto_of_tendsto' (cog_hasSum b h|>.tendsto_sum_nat.norm) grades_hasSum.tendsto_sum_nat
  intro n; refine le_trans (norm_sum_le ..) (Finset.sum_le_sum fun i _=>?_)
  rw [norm_smul,norm_real,Real.norm_eq_abs,abs_of_pos (grades_pos i)]; exact mul_le_of_le_one_right (grades_pos i).le (h i)
variable (ρ : A →⋆ₐ[ℂ] (H→L[ℂ] H)) (x : H)
lemma cog_apply_sum : HasSum (fun n=> ((grades n):ℂ) • ρ (b n) x) (ρ (cog b) x) := by
  let f : A→L[ℂ](H→L[ℂ] H):= ρ.toLinearMap.mkContinuous 1 (fun x=>by rw [one_mul]; exact NonUnitalStarAlgHom.norm_apply_le ρ x)
  have p := (cog_hasSum b h).mapL ((ContinuousLinearMap.apply ℂ H x).comp f)
  convert p using 1
  · ext i; rw [map_smul]; rfl
  rfl
lemma cog_fixes : ρ (cog b) x=x ↔ ∀ n, ρ (b n) x=x := by
  have he:=cog_apply_sum b h ρ x
  constructor
  · intro t n
    let d : ℕ → ℝ := fun n=> (inner ℂ x (ρ (b n) x)).re
    have hle i : ‖ρ (b i) x‖ ≤ ‖x‖ :=by
      simpa using! (ρ (b i)).le_of_opNorm_le ((NonUnitalStarAlgHom.norm_apply_le ρ _).trans (h i)) x
    have hu i : d i ≤ ‖x‖^2 := le_trans (Complex.re_le_norm _)
      ((norm_inner_le_norm x (ρ (b i) x)).trans (by rw [sq]; exact mul_le_mul_of_nonneg_left (hle i) (norm_nonneg _)))
    let F:ℕ→ℝ:=fun n=> grades n*‖x‖^2-grades n*d n
    have hs : HasSum (fun i=> grades i*d i) (‖x‖^2) := by
      rw [t] at he
      have ht:= (he.mapL (innerSL ℂ x)).mapL reCLM
      simpa [d, inner_self_eq_norm_sq, ← ofReal_pow] using ht
    have hy : HasSum F 0 := by
      convert! (grades_hasSum.mul_right (‖x‖^2)).sub hs using 1; ring
    have hp i : 0 ≤ F i:= sub_nonneg.mpr (mul_le_mul_of_nonneg_left (hu i) (grades_pos i).le)
    have hx : F n=0 := (le_trans (hy.summable.le_tsum n (fun i _=> hp i)) hy.tsum_eq.le).antisymm (hp n)
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ) (hle n); rw [inner_re_symm]
    exact mul_left_cancel₀ (grades_pos n|>.ne') (sub_eq_zero.mp hx).symm
  intro u; simp_rw [u] at he
  suffices HasSum (fun i=>((grades i):ℂ) • x) x from he.unique this
  have hy := (grades_hasSum.mapL ofRealCLM).smul_const x; simpa using hy
end average
section means
variable (J : A) (h : ‖J‖≤1) (ρ : A →⋆ₐ[ℂ] (H→L[ℂ] H))
noncomputable def sweep (n : ℕ) : A := (n:ℂ)⁻¹ • ∑ i∈Finset.range n, J^i
include h
lemma sweep_bound (n : ℕ) : ‖sweep J n‖≤1 := by
  nontriviality A
  unfold sweep
  rw [norm_smul,norm_inv,norm_natCast]
  cases n.eq_zero_or_pos with
  | inl t=> rw [t]; simp
  | inr t=>
    rw [inv_mul_le_iff₀ (by exact_mod_cast t),mul_one]; refine (norm_sum_le ..).trans (le_trans (b:=∑ _∈Finset.range n, (1:ℝ)) ?_ ?_)
    · exact Finset.sum_le_sum fun i _=> (norm_pow_le ..).trans (pow_le_one₀ (norm_nonneg _) h)
    simp
lemma sweep_maps (x : H) : Tendsto (fun n=>ρ (sweep J n) x) atTop (𝓝 (((ρ J).eqLocus (1 : H→L[ℂ] H)).orthogonalProjectionOnto x).val) := by
  convert (ρ J).tendsto_birkhoffAverage_orthogonalProjection ((NonUnitalStarAlgHom.norm_apply_le ρ J).trans h) x using 1
  funext i; simp [birkhoffAverage,birkhoffSum,sweep]
end means
open PositiveLinearMap
section rank
variable [PartialOrder A][StarOrderedRing A]
variable (f : A→ₚ[ℂ]ℂ)
local notation "ρ" => f.gnsStarAlgHom
noncomputable def origin : f.GNS := (f.toPreGNS (1:A): f.PreGNS)
local notation "ζ"=> origin f
lemma takes_state (x : A) : ρ x (origin f)=(f.toPreGNS x:f.PreGNS) := by
  change f.gnsNonUnitalStarAlgHom x (↑(f.toPreGNS 1) : f.GNS)=(↑(f.toPreGNS x):f.GNS); rw [gnsNonUnitalStarAlgHom_apply_coe]; simp
lemma gns_state (x : A) : inner ℂ ζ (ρ x ζ)= f x := by rw [takes_state,origin]; simp [preGNS_inner_def]
variable (hf : f 1=1) (J:A) (h : ‖J‖≤1)
lemma gns_dense : DenseRange (fun x=> ρ x (origin f)):=by
  simp_rw [takes_state]
  exact UniformSpace.Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange (UniformSpace.Completion.continuous_coe _)
lemma gns_operator_cont : Continuous (fun x=>ρ x ζ):= (map_continuous ρ).clm_apply continuous_const
include hf
lemma origin_norm : ‖origin f‖=1:=by
  have p :=gns_state f 1; rw [map_one,show ((1:f.GNS →L[ℂ] f.GNS) ζ) =ζ from rfl,hf] at p
  have h:= (@inner_self_eq_norm_sq ℂ f.GNS _ _ _ (origin f)); rw [p,RCLike.one_re] at h; nlinarith [norm_nonneg (origin f)]
lemma gns_state_norm (x : A) : ‖f x‖ ≤ ‖x‖:=by
  rw [← gns_state]; refine (norm_inner_le_norm ..).trans ?_
  have p:=(ρ x).le_opNorm ζ; rw [origin_norm f hf,mul_one] at p; rw [origin_norm f hf,one_mul]; exact p.trans (NonUnitalStarAlgHom.norm_apply_le ρ x)
include h
-- Requiring reality saturation leaves a *face*; equality to 1 follows too
lemma gns_full : IsFixedPt (ρ J) ζ ↔ (f J).re=1:=by
  rw [← gns_state]; change ρ J ζ=ζ ↔ _
  constructor
  · intro e; rw [e]; change RCLike.re (inner ℂ ζ ζ)=1; rw [inner_self_eq_norm_sq,origin_norm f hf,one_pow]
  intro e; apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ)
  · simpa using! (ρ J).le_of_opNorm_le ((NonUnitalStarAlgHom.norm_apply_le ρ J).trans h) ζ
  rw [inner_re_symm,origin_norm f hf,one_pow]; exact e
omit h hf
abbrev rooted : Submodule ℂ f.GNS:= (ρ J).eqLocus (1:f.GNS→L[ℂ]f.GNS)
abbrev limSeat : f.GNS →L[ℂ] rooted f J := (rooted f J).orthogonalProjectionOnto
-- universal variance signature; continuous in state when finite; exact on arbitrary x
noncomputable def grain (n : ℕ) (x : A) : ℝ:= (f (star (sweep J n*x)*(sweep J n*x))).re
lemma realized_grain (n : ℕ) (x : A) : grain f J n x= ‖ρ (sweep J n) (ρ x ζ)‖^2 := by
  rw [grain,← gns_state, map_mul ρ,map_star];
  change RCLike.re (inner ℂ ζ (ContinuousLinearMap.adjoint (ρ (sweep J n*x)) ((ρ (sweep J n*x)) ζ))) = _
  rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq,map_mul (ρ)]; rfl
noncomputable def jointResidual (x : A) := ‖limSeat f J (ρ x ζ)‖^2
include h
lemma grain_limit (x : A) : Tendsto (fun n=>grain f J n x) atTop (𝓝 (jointResidual f J x)):=by
  simp_rw [realized_grain]; exact ((sweep_maps J h ρ (ρ x ζ)).norm).pow _
omit h
lemma residual_cont : Continuous (jointResidual f J):= ((limSeat f J).continuous.comp (gns_operator_cont f)).norm.pow _
include hf h
variable (pf : (f J).re=1)
local notation "ω"=> origin f
lemma root_below (x : A) (n : ℕ) : grain f J n x∈ Set.Icc 0 (‖x‖^2):= by
  rw [realized_grain]; refine ⟨sq_nonneg _,?_⟩
  apply pow_le_pow_left₀ (norm_nonneg _); calc
     ‖ρ (sweep J n) (ρ x ζ)‖ ≤ ‖ρ x ζ‖ := by simpa using! (ρ (sweep J n)).le_of_opNorm_le ((NonUnitalStarAlgHom.norm_apply_le ρ _).trans (sweep_bound J h n)) (ρ x ζ)
     _ ≤ ‖x‖ := by simpa only [origin_norm f hf,mul_one] using (ρ x).le_of_opNorm_le (NonUnitalStarAlgHom.norm_apply_le ρ x) ζ
include pf
lemma at_pin (x : A) : inner ℂ (⟨origin f,(gns_full f hf J h).mpr pf⟩ : rooted f J) (limSeat f J (ρ x ζ))= f x := (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ..).trans (gns_state ..)
lemma residual_above (x : A) : ‖f x‖^2 ≤ jointResidual f J x :=by
  have p:=norm_inner_le_norm (𝕜:=ℂ) (⟨ζ,(gns_full f hf J h).mpr pf⟩ : rooted f J) (limSeat f J (ρ x ζ))
  rw [at_pin f hf J h pf] at p; change ‖f x‖ ≤ ‖ζ‖*_ at p; rw [origin_norm f hf,one_mul] at p; exact pow_le_pow_left₀ (norm_nonneg _) p _
lemma root_rank (p : ∀ x, jointResidual f J x= ‖f x‖^2) :
    rooted f J=Submodule.span ℂ {ζ} := by
  refine le_antisymm ?_ (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (show ζ∈ rooted f J from (gns_full f hf J h).mpr pf)))
  let W:=Submodule.span ℂ {ζ}; let u: rooted f J:= ⟨ζ,(gns_full f hf J h).mpr pf⟩
  let T:= (rooted f J).subtypeL.comp (limSeat f J)
  have hp : IsClosed ((T) ⁻¹' (W : Set f.GNS)) := W.closed_of_finiteDimensional.preimage T.continuous
  intro x hx; rw [← (show T x=x from congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨x,hx⟩ : rooted f J)))]; apply closure_minimal _ hp (gns_dense f x); rintro _ ⟨y,rfl⟩
  let a:= limSeat f J (ρ y ζ); change a.val∈ (W : Set f.GNS)
  have he : a= (f y) • u := by
    have hp':‖a‖^2=‖f y‖^2:=p y
    have pu : ‖u‖=1:=origin_norm f hf
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ)
    · rw [norm_smul,pu,mul_one]; nlinarith [norm_nonneg a, norm_nonneg (f y)]
    rw [norm_smul,pu,mul_one,inner_re_symm, inner_smul_left u a (f y), show inner ℂ u a=f y from at_pin f hf J h pf y]
    simp [Complex.sq_norm, Complex.normSq_apply]
  rw [he]; exact W.smul_mem (f y) (Submodule.subset_span (a:=ζ) (Set.mem_singleton _))
/-- Relative to **all** states on this C⋆-algebra, not only the characters of a given
    commutative system. We show the collapsed residual makes decomposition impossible.
    Applies even if `J` is not selfadjoint or positive. -/
def pure0 (f : A→ₚ[ℂ]ℂ) : Prop := f 1=1 ∧ ∀ g k : A→ₚ[ℂ]ℂ, g 1=1 → k 1=1 →
    ∀ r : ℝ, 0<r → r<1 → (∀ x : A, f x = (r:ℂ) * g x + ((1-r:ℝ):ℂ) * k x) → f=g ∧ f=k
lemma root_pure (p : ∀ x, jointResidual f J x= ‖f x‖^2) : pure0 f:=by
  refine ⟨hf,fun g k hg hk r hr hu H' =>?_⟩
  let t:=1-r; have ht:0<t:=sub_pos.mpr hu
  have hmix(x:A): (f x).re=r*(g x).re+t*(k x).re:=by rw [H']; simp [mul_re,t]
  have heg(z:A→ₚ[ℂ]ℂ)(h' : z 1=1) : (z J).re ≤1:= (re_le_norm ..).trans ((gns_state_norm z h' _).trans h)
  have gp:(g J).re=1:= (heg g hg).eq_of_not_lt (fun i=>by have hJ:=hmix J; have K:=heg k hk; unfold t at hJ ht; nlinarith)
  have kp:(k J).re=1:= (heg k hk).eq_of_not_lt (fun i=>by have hJ:=hmix J; unfold t at hJ ht; nlinarith)
  have tlim (x : A) : ‖f x‖^2=r*jointResidual g J x+t*jointResidual k J x:=by
    rw [← p]
    have he n : grain f J n x=r*grain g J n x+t*grain k J n x:=hmix _
    apply tendsto_nhds_unique (grain_limit f J h x); simp_rw [he]
    exact ((grain_limit g J h x).const_mul r).add ((grain_limit k J h x).const_mul t)
  have he(y:A)(e:f y=0) : g y=0 ∧ k y=0:=by
    have u:=tlim y; rw [e,norm_zero,zero_pow (by decide)] at u
    have q:=residual_above g hg J h gp y; have v:=residual_above k hk J h kp y
    suffices ‖g y‖^2=0 ∧ ‖k y‖^2=0 by simpa using this
    have g' : 0≤ jointResidual g J y:= sq_nonneg _; have k' : 0 ≤ jointResidual k J y:=sq_nonneg _
    have hx:jointResidual g J y=0:= by nlinarith
    have hy:jointResidual k J y=0:=by nlinarith
    exact ⟨by nlinarith,by nlinarith⟩
  have H₁ (x:A): f x=g x∧ f x=k x:=by
    let y:=x- (f x) • (1:A)
    obtain ⟨u,v⟩:=he y (by simp [y,hf])
    simp [y,hg,hk,sub_eq_zero] at u v
    exact ⟨u.symm,v.symm⟩
  exact ⟨DFunLike.ext _ _ (fun x=>(H₁ x).1),DFunLike.ext _ _ (fun x=>(H₁ x).2)⟩
end rank
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.sweep_maps
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.root_rank
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.root_pure
