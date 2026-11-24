import YM.SU5.FiniteGaugeData.Hills.SquareH
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace Hills
open Nacre Heat Charm Chrono SalonG Journey
section
open OS Ground Function Set Filter MeasureTheory Measure Spectral TopologicalSpace WeakDual
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators Classical
-- abstraction apart of axes
variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A][TopologicalSpace A]
structure Prismatic (H : Hilbert) (p : A →⋆ₐ[ℂ] H.Op) (w:H) (R : Panes A) : Prop extends Ground.Panes.Shines H p w R where
 -- `R.Shines` arg order? inspect
 hunts (x:C(R.X,ℂ)):∃ a:A,∀ y:R.X, R.character y a=x y
-- copy stronger pano optics
lemma panoramaS {A : Type} [CommCStarAlgebra A] (H : Hilbert) (p : A →⋆ₐ[ℂ] H.Op) (w : H) (hw : ‖w‖=1)
    (u : ℕ → A) (hu : DenseRange u) (ht : ∀ i : A, p i w=0 → i=0) : ∃ R : Panes A, Prismatic H p w R := by
  classical
  let X := Theta (X := A)
  letI : MetrizableSpace X := tiny u hu
  letI : MetricSpace X := metrizableSpaceMetric X
  letI : MeasurableSpace X := borel _; letI : BorelSpace X := ⟨rfl⟩
  let P : Rep.CC X →⋆ₐ[ℂ] H.Op := p.comp ((gelfandStarTransform A).symm : _ →⋆ₐ[ℂ] _)
  let V : Panes A := { X := X, μ := Rep.sees P w, character := view }
  have hp i : P (gelfandStarTransform A i)=p i := congr_arg p ((gelfandStarTransform A).symm_apply_apply _)
  refine ⟨V,⟨?_,?_,bij,view_cont,mark_cont,?_⟩,?_⟩
  · apply isProbabilityMeasure_iff_real.mpr
    change (Rep.sees P w).real _=1
    rw [Rep.size,hw,one_pow]
  · refine supports H P w ?_
    intro x hx
    obtain ⟨i,rfl⟩ := (gelfandStarTransform A).surjective x
    change P (gelfandStarTransform A i) w=0 at hx; rw [hp] at hx
    change (gelfandStarTransform A i)=0; rw [ht i hx,map_zero]
  · intro i
    have h := Rep.pairings P w (gelfandStarTransform A i)
    rw [hp] at h; exact h

  intro x; obtain ⟨y,hp⟩:= (gelfandStarTransform A).surjective (show Rep.CC X from x); refine ⟨y,fun i=>?_⟩; exact DFunLike.congr_fun hp i
-- normalization for OPEN character point. Assumes orbit-faithfulness only.
variable {H: Hilbert}{p:A→⋆ₐ[ℂ] H.Op}{w:H}{R:Panes A}(F:Prismatic H p w R)
include F
local notation "μ"=> R.μ
local notation "X"=> R.X
local notation "L" i:max uι:max=> (R.character i) uι -- use token conflict
lemma amplit (a b c:A) : ∫ x,R.character x (star a*b*c)  ∂ R.μ=inner ℂ (p a w) (p b (p c w)):=by
 rw [F.ground,mul_assoc,map_mul,map_mul,map_star,mul_apply_eq_comp,mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
lemma paysPrism (U:Set (R.X))(i : R.X)(h:U∈𝓝 i)(v:∀ i:A,p i w=0→ i=0) :
    ∃ u:A,‖p u w‖=1 ∧ ∀ x:R.X,x∉ U→ R.character x u=0:= by
 obtain ⟨r,t,h⟩:= Metric.mem_nhds_iff.mp h; let b:C(X,ℂ):= ⟨fun y=> ((↑(max 0 (r-dist y i)):ℂ)), Complex.continuous_ofReal.comp (by fun_prop)⟩
 obtain ⟨y,f⟩:= F.hunts b; have ht:b i ≠0:=by change (↑(max 0 (r-dist i i)):ℂ) ≠ 0; rw [dist_self, sub_zero, max_eq_right t.le]; exact_mod_cast ne_of_gt t
 have hv : 0<‖p y w‖:= norm_pos_iff.mpr fun z=> ht ((f i).symm.trans ((congrArg (R.character i) (v y z)).trans (map_zero _)))
 let a:= (((↑‖p y w‖:ℂ))⁻¹:ℂ); refine ⟨a • y,by rw [map_smul, _root_.smul_apply,norm_smul]; unfold a; rw [norm_inv, Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv,inv_mul_cancel₀ hv.ne'],?_⟩
 intro x g; rw [map_smul,f]; have hx: r≤ dist x i:= le_of_not_gt (fun v=>g (h v)); change a • ((↑(max 0 (r-dist x i)):ℂ))=0; rw [max_eq_left (by linarith), Complex.ofReal_zero,smul_zero]

lemma coneB (i:R.X)(ε:ℝ)(e:0<ε) (V:Finset A)(p':∀ i:A,p i w=0→ i=0): ∃ u:H, ‖u‖=1 ∧ ∀ a∈ V, ‖inner ℂ u (p a u) - R.character i a‖≤ε:=by
 haveI := F.normalized
 let U:Set R.X:={y|∀ a∈V, dist (L y a) (L i a) < ε}
 have hU:U∈𝓝 i:= (eventually_all_finset V).2 (fun v _=> Metric.tendsto_nhds.1 ((F.weak v).tendsto i) ε e)
 obtain ⟨u,h,b⟩:=paysPrism F U i hU p'; let c (y:X):= ‖L y u‖^2
 have hc:Continuous c:= ((F.weak u).norm.pow 2)
 have he(a:X→ℝ)(p:Continuous a): Integrable a R.μ:= p.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hf (a:A)(x:X): (L x (star u *a*u))= (c x:ℂ) * L x a:= by
    have h(x:ℂ):star x*x= (↑(‖x‖^2):ℂ):=by rw [mul_comm]; change x*(starRingEnd ℂ) x=_; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [map_mul,map_mul,map_star,mul_right_comm,h]
 have hp : ∫ x,c x ∂ R.μ=1:= by
    apply Complex.ofReal_injective; rw [← integral_complex_ofReal];
    calc
    _ = ∫ x, R.character x (star u* 1 *u)  ∂ R.μ:= integral_congr_ae (Eventually.of_forall fun x=> (by dsimp only; rw [hf,map_one,mul_one]))
    _ = _:=by rw [amplit F, map_one]; change inner ℂ (p u w) (p u w)= ((1:ℝ):ℂ); rw [inner_self_eq_norm_sq_to_K,h]; norm_num
 refine ⟨p u w,h,fun a t=>?_⟩
 have hb: L i a= ∫ x,(c x:ℂ)*L i a ∂ R.μ:= by rw [integral_mul_const,integral_complex_ofReal,hp,Complex.ofReal_one,one_mul]
 rw [← amplit F,hb]; simp_rw [hf]; have hI(f:X→ℂ)(p:Continuous f): Integrable f R.μ:= p.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hL:= Complex.continuous_ofReal.comp hc
 rw [← integral_sub (hI (fun x=>(c x:ℂ)* L x a) (hL.mul (F.weak a))) (hI (fun x=>(c x:ℂ)*L i a) (hL.mul continuous_const))]
 have hq(x:X): ‖(c x:ℂ)* L x a-(c x:ℂ)*L i a‖ ≤ c x*ε:=by
    rw [← mul_sub,norm_mul, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by unfold c; positivity)]; by_cases g:x∈U; · exact mul_le_mul_of_nonneg_left (((show ∀a∈V, dist _ _< ε from g) a t).le.trans_eq' (dist_eq_norm _ _)) (sq_nonneg _) -- trans_eq' expects dist=norm; maybe remove
    rw [show c x=0 from by unfold c; rw [b x g, norm_zero]; norm_num,zero_mul,zero_mul]
 exact (norm_integral_le_integral_norm ..).trans (le_trans (integral_mono_of_nonneg (Eventually.of_forall fun _=> norm_nonneg _) ((he c hc).mul_const ε) (Eventually.of_forall hq)) (le_of_eq (by rw [integral_mul_const,hp,one_mul])))
#print axioms coneB
end
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
