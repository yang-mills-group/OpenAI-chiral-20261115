import YM.CF.Newt.Tier
import YM.Push.STATIONARY_UNIFORM.Response
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Melody
import YM.CF.Jet.Mask
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior Finset MeasureTheory
 Push Push.Uniform Metric ContinuousLinearMap
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
section norm
variable {X E ι τ:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype ι][Fintype τ]
  {a C d t:ℝ}{k m n Z:ℕ}{c:Side}{I:Fin k→ι}
lemma stall (L: (Positions ι) [×k]→L[ℝ] E)(b:Site c)(p:ι → Site c)(h:∀ q:Fin k→ι, ‖L fun i=>bolt (q i)‖ ≤ C* Real.exp (-a*spanSites p b q))(hp:Multiplicity p Z)(ht:0≤C)(hv:0<a):
 ‖L‖≤ C*(1+Z*countCost a)^k:=by
 let t:ℝ:=Z*countCost a; have hx : 0≤t:= mul_nonneg (by positivity) (count_pos hv).le
 refine Planned.AtomRegular.op_le_of_unit (show 0≤C*(1+t)^k by positivity) fun v hp'=>?_
 let Q(i:Fin k)(j:ι) := v i j • bolt j
 have he : v=(fun i=> ∑ j, Q i j):=funext fun i=>(combine (v i)).symm
 rw [he,L.map_sum Q]
 have ht(q: Fin k→ι): ‖L (fun i => Q i (q i))‖≤ C*∏ i, Decay a b (p (q i)):=by
    rw [show _=(∏ i,v i (q i)) • L (fun i=>bolt (q i)) from L.map_smul_univ _ _,norm_smul]
    have hw: ‖∏ i,v i (q i)‖ ≤ 1:= by
        rw [Real.norm_eq_abs,abs_prod]; exact prod_le_one (fun i _=> abs_nonneg _) (fun i _=> (norm_le_pi_norm (v i) _).trans (hp' i))
    refine (mul_le_of_le_one_left (norm_nonneg _) hw).trans ((h _).trans ?_)
    unfold Decay spanSites; rw [Nat.cast_sum,Finset.mul_sum,Real.exp_sum]
 apply (norm_sum_le ..).trans; apply (Finset.sum_le_sum (fun j _=> ht j)).trans
 rw [← Finset.mul_sum,← Fintype.prod_sum (fun _ : Fin k=>fun j=>Decay a b (p j))]
 simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; apply mul_le_mul_of_nonneg_left _ (by assumption)
 exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _=>(decay_pos ..).le) ((hp.count _ hv b).trans (le_add_of_nonneg_left zero_le_one)) _
abbrev Fish(I:Type) [Fintype I]:= Positions I
lemma pin {l:(ι⊕τ) → Site c}{f:Fish (ι⊕τ)→ℝ}{x:Fish (ι⊕τ)} (p: Scatter l a (n+1) f x C)(h:ContDiffAt ℝ ω f x)(hp:Multiplicity l Z)(ht:0≤C)(hv:0<a): Jet.Allows n (Slope f) x (C*(1+Z*countCost a)^n):=by
 let t:ℝ:=Z*countCost a; have hx : 0≤t:= mul_nonneg (by positivity) (count_pos hv).le
 refine Jet.allows_pi (f:=Slope f) (show 0≤C*(1+t)^n by positivity) fun i=>?_
 let u(y:Fish (ι⊕τ)):=Slope f y i; let e:ι⊕τ:=.inr i; let z:=bolt e
 have he : u= apply ℝ ℝ z ∘ fderiv ℝ f :=by funext y; unfold u Slope Push.Uniform.entry; rw [iteratedFDeriv_one_apply]; rfl
 have hh : ContDiffAt ℝ ω (fderiv ℝ f) x:=h.fderiv_right (by simp)
 have h' : ContDiffAt ℝ n u x:= he.symm ▸ (apply ℝ ℝ z).contDiff.contDiffAt.comp x (hh.of_le le_top)
 refine ⟨h',fun i hi=>?_⟩; change ‖iteratedFDeriv ℝ i u x‖ ≤ _
 refine (stall (iteratedFDeriv ℝ i u x) (l e) l ?_ hp ht hv).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show 1≤1+t by linarith) hi) ht)
 intro q
 let w := Fin.snoc (α:=fun _ : Fin (i+1)=>ι⊕τ) q e -- types
 rw [he,ContinuousLinearMap.iteratedFDeriv_comp_left _ hh le_top]
 have hl : spanSites l (l (w (Fin.last i))) w =spanSites l (l e) q:=by unfold spanSites w; simp [Fin.sum_univ_castSucc]
 have hX:=p (i+1) (by omega) w (Fin.last i); rw [hl] at hX; refine le_trans ?_ hX; unfold entry
 rw [iteratedFDeriv_succ_apply_right]
 have ha: Fin.init (α:=fun _=> Fish (ι⊕τ)) (fun j=>bolt (w j))=fun i=>bolt (q i):=by ext; simp [Fin.init,w]
 rw [ha,show w (Fin.last i)=e from Fin.snoc_last ..]
 exact le_rfl
lemma lower_n : ‖lowerCol (ι:=ι) (τ:=τ)‖≤1:= by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro v; change ‖meetVar (0: Fish ι) v‖≤_; simp [norm_meet]
lemma tree_der (y: Fish (ι⊕τ)){f:Fish (ι⊕τ)→ℝ}(p:ContDiffAt ℝ ω f y):
 ∀ b:Fish τ,fderiv ℝ (Slope f) y (lowerCol b)= block f y *ᵥ b:=by
 obtain ⟨⟨x,v⟩,rfl⟩ := (partSpace ι τ).symm.surjective y
 obtain ⟨h,hv⟩:= slope_block (show ContDiffAt ℝ ω f (meetVar x v) from p)
 intro b
 have hh := (h.differentiableAt (by simp)).hasFDerivAt.comp v (meet_derivative x v)
 change _ = block f (meetVar x v) *ᵥ b
 rw [← hv b,hh.fderiv]; rfl
def paintO: Matrix τ τ ℝ →L[ℝ] Fish τ →L[ℝ] Fish τ:= LinearMap.toContinuousLinearMap { toFun := fun x => LinearMap.toContinuousLinearMap x.mulVecLin, map_add':=fun x y=>by ext1 i; exact add_mulVec _ _ _, map_smul':=fun x y=>by ext1 i; exact smul_mulVec _ _ _ }
lemma stiffness {l:(ι⊕τ) → Site c}{f:Fish (ι⊕τ)→ℝ}{x:Fish (ι⊕τ)} (p: Scatter l a (n+1+1) f x C)(h:ContDiffAt ℝ ω f x)(hp:Multiplicity l Z)(ht:0≤C)(hv:0<a):
 Jet.Allows n (fun y=>paintO (block f y)) x (C*(1+Z*countCost a)^(n+1)):=by
 let T := ContinuousLinearMap.compL ℝ (Fish τ) (Fish (ι⊕τ)) (Fish τ) |>.flip (lowerCol)
 have hT : ‖T‖≤1:= by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro t; refine le_trans (ContinuousLinearMap.opNorm_comp_le t lowerCol) ?_; rw [one_mul]; exact mul_le_of_le_one_right (norm_nonneg t) lower_n
 apply (((pin p h hp ht hv).slide.linear T hT).mono (one_mul _).le).germ
 filter_upwards [h.eventually (by simp)] with i hi
 exact ContinuousLinearMap.ext (tree_der i hi)
lemma paintO_p(A: Matrix τ τ ℝ)(x: Fish τ): paintO A x=A *ᵥ x:=rfl
end norm
end YM.CF.Newt
