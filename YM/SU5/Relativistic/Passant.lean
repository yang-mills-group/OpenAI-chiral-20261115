import YM.SU5.Relativistic.Vail
/-! # Three-axis eye. Taper, support, reflection budgets all same. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ"=> 2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
attribute [local instance] screen_fin
-- Stakes on full Behind
variable (k : Behind)
abbrev spax (x: WalkA)(k: Behind):= ∏ i:Fin 3,surge (x i) (k i)
def eyeMeasure : Measure Behind:=Measure.pi (fun _:Fin 3=> volume.restrict screen)
instance : IsFiniteMeasure eyeMeasure:= by unfold eyeMeasure; infer_instance
-- split pulse test into two actual regions later. Start measure normalized. 
def gaugeRead (x:WalkA)(f:Behind→ℂ):ℂ:=(((2*Real.pi:ℝ):ℂ)^3)⁻¹ * ∫ t, spax x t*f t∂eyeMeasure

def launch (d:ℕ)(r:ℝ): Set Behind:= Set.pi Set.univ (fun _=>Set.Icc r (r+dropH d+dropH d))
def upland (d:ℕ)(r:ℝ): Set Behind:= Set.pi Set.univ (fun _=>Set.Ioo r (r+dropH d+dropH d))
lemma launch_compact(d:ℕ)(r:ℝ): IsCompact (launch d r) := isCompact_univ_pi fun _=> isCompact_Icc
lemma upland_open(d:ℕ)(r:ℝ): IsOpen (upland d r) := isOpen_set_pi (Set.finite_univ) (fun _ _=>isOpen_Ioo)
lemma upland_interior(d:ℕ)(r:ℝ): upland d r ⊆ interior (launch d r):= interior_maximal (fun _ q i p=>Set.Ioo_subset_Icc_self (q i p)) (upland_open ..)
lemma launched (d:ℕ)(p:9≤d): ∃ r, 0<r ∧ r+dropH d+dropH d< π:=by
 refine ⟨π/2,half_pos pi_pos,?_⟩
 have hv:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
 have hz := u_bound d p hv
 linarith [pi_pos]
where u_bound (d:ℕ)(p:9≤d)(hv:0<(d:ℝ)): dropH d ≤ 2*π/9:=div_le_div_of_nonneg_left (by positivity) (by norm_num) (by exact_mod_cast p) -- order wrong
lemma launch_sun {d:ℕ}{r:ℝ}(hr:0<r)(u:r+dropH d+dropH d<π):launch d r⊆ sunshine:=fun _ p i h=> ⟨hr.trans_le (p i h).1, (p i h).2.trans_lt u⟩
noncomputable def stationed (d:ℕ)(r:ℝ)(x:Behind):ℂ:= ∏ i:Fin 3, (d:ℂ)*(hornA r d (x i):ℂ)
lemma stationed_c(d:ℕ)(r:ℝ):Continuous (stationed d r):=by unfold stationed; fun_prop
lemma stationed_off{d:ℕ}(p:0<d)(r:ℝ)(x:Behind)(h:x∉ upland d r): stationed d r x=0:=by
 obtain ⟨i,v⟩:=not_forall.mp h
 have hp: x i∉Set.Ioo r (r+dropH d+dropH d):=fun x=> v (fun _=>x)
 unfold stationed; exact Finset.prod_eq_zero (mem_univ i) (by rw [hornA_off d r p hp, Complex.ofReal_zero,mul_zero]) -- dependent k exact
lemma fingerSnap {d:ℕ}(p:0<d)(r:ℝ)(hp:0<r)(hq: r+dropH d+dropH d<π)(n:WalkA): gaugeRead ((d:ℤ) • n) (stationed d r)=if n=0 then 1 else 0:=by
 unfold gaugeRead spax stationed; simp_rw [← Finset.prod_mul_distrib, Pi.smul_apply,zsmul_eq_mul, Int.cast_id]; rw [eyeMeasure,integral_fintype_prod_eq_prod (μ:=fun (_:Fin 3)=> volume.restrict screen) (E:=fun _:Fin 3=>ℝ) (f:=fun i:Fin 3=> fun x:ℝ=>surge (↑((d:ℤ)*n i):ℝ) x*((d:ℂ)*(hornA r d x:ℂ)))] -- tune
 change _*∏ i:Fin 3,pluse _ _=_
 simp_rw [hornA_rim p (lt_trans (neg_neg_of_pos pi_pos) hp) hq]; by_cases v:n=0
 · subst n; rw [if_pos rfl]; simp [pi_pos.ne']
 rw [if_neg v, show (∏ i:Fin 3,_)=(0:ℂ) from ?_,mul_zero]
 obtain ⟨i,t⟩:= Function.ne_iff.mp v; exact Finset.prod_eq_zero (mem_univ i) (if_neg t)

section rise
-- smooth support unity extension 
variable {W:Set Behind}(t:IsCompact W)
include t
lemma continue_g(f:Behind→ℂ)(p:ContinuousOn f W)(u:∀ x∉interior W,f x=0):Continuous f:=by
 classical
 rw [show f=W.indicator f from funext fun i=> by by_cases t:i∈W; rw [Set.indicator_of_mem t]; rw [Set.indicator_of_notMem t,u _ (fun h=>t (interior_subset h))]]
 refine continuous_indicator ?_ ((t.isClosed.closure_eq.symm) ▸ p)
 exact fun i h=> u i h.2
lemma continue_k{f:Behind×ℝ →ℂ}(p:ContinuousOn f (W ×ˢ Set.Icc (-π) π))(u:∀ x:Behind×ℝ,x.1∉ interior W →f x=0):ContinuousOn f (Set.univ ×ˢ Set.Icc (-π) π):=by
 let L:= interior W
 have he:ContinuousOn f (Lᶜ ×ˢ Set.Icc (-π) π):=by refine ContinuousOn.congr (f:=fun _=>0) continuousOn_const ?_; exact fun _ h=> u _ h.1
 have hc: Set.univ ×ˢ Set.Icc (-π) π=(W ×ˢ Set.Icc (-π) π)∪(Lᶜ ×ˢ Set.Icc (-π) π):=by
    ext p; simp only [Set.mem_prod,Set.mem_union,Set.mem_univ,true_and,mem_compl_iff]; have h:p.1∈ W∨ p.1∉ L:= or_iff_not_imp_left.mpr fun q e=> q (interior_subset e)
    tauto
 rw [hc]; exact ContinuousOn.union_of_isClosed p he (t.isClosed.prod isClosed_Icc) (isOpen_interior.isClosed_compl.prod isClosed_Icc)
end rise
end YM.CF.Crest.Sleet
