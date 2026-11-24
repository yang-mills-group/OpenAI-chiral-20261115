import YM.SU5.Relativistic.SirenA
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra screen_fin
local notation "I"=>Complex.I
local notation "φ"=> 2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
variable {d:ℕ}{s:Finset ℤ}{c:ℤ→Behind→ℂ}{a r:ℝ}
namespace UpStart
variable (P:UpStart d s c r (2*a))
local notation "Ω"=>target s c
local notation "Z"=>turned s c
local notation "U"=>launch d r
section poly
lemma array_s (f:WalkA→₀ℂ): Continuous (array f):=continuous_finsetSum _ fun k _=> continuous_const.mul (spax_cont _)
lemma array_chip (f:WalkA→₀ℂ)(x:WalkA): gaugeRead x (array f)= f x:=by
 -- eval obvious by linearity. exact normal cost
 unfold array gaugeRead; simp_rw [Finsupp.sum, mul_sum]; -- may match inverse expr after
 rw [integral_finsetSum]; swap
 · intro i v; simp_rw [mul_left_comm (spax x _)]; unfold eyeMeasure -- ease measurable integrable
   have h(i:WalkA):MemLp (spax i) 2 eyeMeasure := MemLp.of_bound (spax_cont _).aestronglyMeasurable 1 (Eventually.of_forall fun k=> (spax_norm i _).le)
   exact ((MemLp.integrable_mul (h x) (h (-i))).const_mul _)
 rw [mul_sum]; have he(z:ℂ)(i:WalkA):gaugeRead x (fun v=>z*spax (-i) v)=z*gaugeRead x (spax (-i)):=by unfold gaugeRead; simp_rw [mul_left_comm (spax x _)]; rw [integral_const_mul,mul_left_comm]
 have hp(i): ((↑(φ:ℝ)^3)⁻¹:ℂ)*(∫ k,spax x k*(f i*spax (-i) k)∂eyeMeasure)=f i*(if x=i then 1 else 0) := by rw [← eyeLease]; exact he (f i) i
 simp_rw [hp]; rw [sum_eq_single x]; simp
 · intro i v u; simp [Ne.symm u]
 intro v; simp_all [Finsupp.notMem_support_iff]
end poly
include P
lemma apron (i:SpinIdx)(n:ℕ)(ε:ℝ)(p:0<ε) : ∃ f: ℤ→ WalkA→₀ℂ,(∀ k∈backPane,∀ t:ℝ, ‖(∑ x∈TwistT n,array (f x) k* soundT x t)-beforeT i n s c k t‖≤ε) ∧
     (∀ j:ℤ,j∉s→ i∈plusHalf→ f j=0) ∧ ∀ j k, k∈backPane → ‖array (f j) k - sailV i j s c k‖≤ ε :=by -- strengthen previous repeated
 classical
 let T:=TwistT n; let D:ℝ:=T.card+1; have h:0<D:=by unfold D; positivity
 have hp(j:ℤ) : ∃ f: WalkA→₀ℂ,(∀ k∈backPane, ‖array f k-sailV i j s c k‖≤ ε/D)∧ (j∉s → i∈plusHalf→ f=0):=by
    by_cases t:j∈s ∨ i∉plusHalf
    · obtain ⟨a,g⟩:= summit _ (P.sail_cont i j).continuousOn (fun k h=>P.sail_support i j h) _ (div_pos p h); exact ⟨a,g, fun x w=> Or.elim t (fun u=>(x u).elim) (fun u=>(u w).elim)⟩
    push Not at t; refine ⟨0,fun k _=>?_,fun _ _=>rfl⟩; unfold array sailV; rw [P.landing t.2 k _ t.1]; simp [(div_pos p h).le]
 choose f u v using hp
 refine ⟨f,fun k y t=>?_,v,fun j k p'=> (u j k p').trans (div_le_self p.le (by unfold D; simp))⟩; unfold beforeT; rw [← Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans; simp_rw [←sub_mul,norm_mul,sound_norm,mul_one]; apply (sum_le_sum (fun i e=>u i k y)).trans; rw [sum_const,nsmul_eq_mul]; exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one : (T.card:ℝ)≤D) (div_pos p h).le).trans (Eq.le (mul_div_cancel₀ _ h.ne'))
lemma dominant {f:WalkA→₀ℂ}{ε:ℝ}(g:0<d) (p:∀ k∈ backPane, ‖array f k - sailV 2 0 s c k‖≤ε): ∀ S:Finset WalkA,
    ∑ x∈S, ‖f ((d:ℤ) • x) - (if x=0 then 1 else 0)‖^2 ≤ ε^2:=by
 intro S; let g':= sailV 2 0 s c; let h:= fun k=>array f k - g' k
 have hp: MemLp h 2 jEye:= MemLp.of_bound ((array_s f).sub (P.sail_cont 2 0)|>.aestronglyMeasurable) ε (eyeWithin.mono (fun x hx=> p x hx))
 let w(i:WalkA):=(d:ℤ) • i; have he:Injective w:=by
    intro i j p; funext x; have he: (d:ℤ)*i x=(d:ℤ)*j x:=by simpa [w,smul_eq_mul] using congrFun p x
    exact mul_left_cancel₀ (by exact_mod_cast g.ne') he
 have hK(x):g' x=stationed d r x:=by
    rw [show g' x=wrapT 0 (fun t=> pledge s c x t*fell 2 x t) from ?_]; swap; · unfold g' sailV; congr 1; ext1 t; rw [tariffed]; simp
    exact P.beats x
 have hg(x:WalkA): gaugeRead (w x) h=gaugeRead (w x) (array f)-gaugeRead (w x) g':=by
    simp_rw [gauge_true]; unfold h; simp_rw [mul_sub]; apply integral_sub
    · apply integrable_fin _ ((spax_cont (w x)).mul (array_s f))
    apply integrable_fin _ ((spax_cont (w x)).mul (P.sail_cont 2 0))
 have hv:= lobe_size (S.image w) h hp ε p; rw [Finset.sum_image he.injOn] at hv; simp_rw [hg,funext hK,array_chip, show ∀ x,gaugeRead (w x) (stationed d r)=_ from fun x=> fingerSnap g r P.wage P.tail x] at hv; exact hv
where integrable_fin (f:Behind→ℂ)(p:Continuous f) : Integrable f jEye:=by
        obtain ⟨b,u⟩:= (isCompact_univ_pi (fun _:Fin 3=> isCompact_Icc)).exists_bound_of_continuousOn (s:=backPane) p.continuousOn
        exact Integrable.mono' (integrable_const _) p.aestronglyMeasurable (eyeWithin.mono fun x=>u x)
-- purchase independent of array length m later.
abbrev Waxy:=SpinIdx→ℤ→WalkA→₀ℂ
def timbre(n:ℕ)(F:Waxy)(u:Behind)(t:ℝ):Ket SpinIdx:= WithLp.toLp 2 (fun i=> boardZ n F i u t)
lemma receiptZ(p:0<a)(w:0<d) : ∃ R> (0:ℝ),∀ n:ℕ, ∃ f:Waxy, (∀ k∈backPane,∀ t∈Φ, ‖timbre n f k t-Ω k t‖ ≤ R * spangle a n) ∧
      (∀ i∈plusHalf,∀ j:ℤ,j∉s→f i j=0) ∧ ∀ A:Finset WalkA, ∑ x∈A, ‖f 2 0 ((d:ℤ) • x) - (if x=0 then 1 else 0)‖^2 ≤ (R * spangle a n)^2 :=by
 choose B x h using P.sail_t p
 let R:ℝ:= ∑ i:SpinIdx,B i; have hx: ∀ i,B i ≤ R:=fun i=> single_le_sum (f:=B) (fun i _=> (x i).le) (mem_univ i)
 have hR:0<R:= (x 0).trans_le (hx _)
 let C:=2*(R+1); have hp:1 ≤ C:=by unfold C; linarith
 refine ⟨C,by linarith,fun n=>?_⟩
 let V:= spangle a n; have hv:0<V:=spangle_pos ..; choose f g h₀ p' using fun i=> P.apron i n V hv
 refine ⟨f,fun k hk t ht=>?_,fun i v a u=> h₀ _ a u v,fun A=> (P.dominant w (p' 2 0) A).trans (pow_le_pow_left₀ hv.le (le_mul_of_one_le_left hv.le hp) _)⟩
 let G:= timbre n f k t-Ω k t
 have h(i):‖G.ofLp i‖ ≤ (R+1)*V:=by
    let v:= beforeT i n s c k t
    apply (norm_sub_le_norm_sub_add_norm_sub (boardZ n f i k t) v ((Ω k t).ofLp i)).trans
    rw [norm_sub_rev v ((Ω k t).ofLp i)]; have hp:= (h i k n t ht).trans (mul_le_mul_of_nonneg_right (hx i) hv.le)
    exact (add_le_add (g i k hk t) hp).trans_eq (by unfold V; ring)
 change ‖G‖≤C*V; refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (zero_le_one.trans hp) hv.le)).1 ?_
 rw [EuclideanSpace.norm_sq_eq]; refine (sum_le_sum (fun i _=> pow_le_pow_left₀ (norm_nonneg _) (h i) 2)).trans ?_; rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]; change ((4:ℕ):ℝ)*_ ≤ _; push_cast; exact le_of_eq (by unfold C; ring)
end UpStart
end YM.CF.Crest.Sleet
