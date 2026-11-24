import YM.SU5.Selected.Bary

/-!
# Purity in the stationary W system of the selected arc

For any representation-specific decomposition of norms; easier than appealing
to quasi-local abstract faithfulness. In our application B includes slab clocks
and lattice translations! We don't prove this assertion about the restriction
to an algebra without these operators.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory
open Function Filter Set Topology NormedSpace MeasureTheory Measure ContinuousMap WeakDual
open scoped Topology InnerProductSpace BigOperators NNReal ENNReal ComplexOrder
variable {A B W : Type*} [CommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {D:Submodule ℂ W} [CompleteSpace D]

lemma actsForm (X:B→ₚ[ℂ]ℂ)(b c:B) : implement X b (vectorForm X c)=vectorForm X (b*c):=by
  change _=implement X _ (vector X); rw [map_mul]; rfl
lemma nrmForm (X:B→ₚ[ℂ]ℂ) (b:B) : ‖vectorForm X b‖^2 = (X (star b * b)).re:=by rw [← form_is]; exact (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm
namespace Transaction
variable (T:Transaction A B D) (x:Resident A) (h:T.FixedPhase x)

include h
lemma extreme_station (X:B→ₚ[ℂ]ℂ)(g:X 1=1) {C : ℝ}
    (w:∀ b, (X (star b*b)).re ≤ C^2*((T.selected x) (star b * b)).re) : X=T.selected x := by
  let L:= T.selected x
  let φ:= vectorForm L; let Ψ:=vectorForm X; let t:= Ψ.toLinearMap.extendOfNorm φ.toLinearMap
  have hv(b:B): ‖Ψ b‖≤ |C| * ‖φ b‖ := by
    have hp: (X (star b*b)).re ≤ |C|^2*(L (star b*b)).re:= (sq_abs C).symm ▸ w b
    rw [← nrmForm,←nrmForm] at hp; apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1; rw [mul_pow]; exact hp
  have he(b:B): t (φ b)= Ψ b:= LinearMap.extendOfNorm_eq (f:=Ψ.toLinearMap) (e:=φ.toLinearMap) (frequency L) ⟨_,hv⟩ _
  let v:= t.adjoint (vector X)
  have hX(u:B)(p:u∈T.steps): Ψ u= Ψ 1:= by
    rw [← sub_eq_zero,← map_sub]
    have hu:= hv (u-1); rw [map_sub (f:=φ), show φ u=φ 1 from (T.fixed_Ω x _ p).trans (vector_unit L).symm,sub_self,norm_zero,mul_zero] at hu
    exact norm_le_zero_iff.mp hu
  have hf(u:B)(p:u∈T.steps):implement L u v=v:= by
    apply (frequency L).eq_of_inner_right ℂ; intro a
    rw [←ContinuousLinearMap.adjoint_adjoint (implement _ _),ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ ((star (implement L u)) (φ a)) v=inner ℂ (φ a) v
    unfold φ; rw [←map_star, actsForm L]; unfold v; rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (t (φ _)) _=inner ℂ (t (φ a)) _
    rw [he,he]; unfold Ψ; rw [← actsForm,map_star] -- tune adjoint
    change inner ℂ ((implement X u).adjoint _) _=_
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (inner ℂ (Ψ a)) ((hX u p).trans (vector_unit X))
  obtain ⟨c,hc⟩:= h _ hf
  have hd(a:B): X a= star c * L a := by
    calc X a= inner ℂ (vector X) (t (φ a)) := by rw [he]; exact (read_is X a).symm
         _= inner ℂ v (φ a) := (ContinuousLinearMap.adjoint_inner_left t (φ a) _).symm -- args?
         _= _ := by rw [hc,inner_smul_left,show inner ℂ (vector L) (φ a)= L a from read_is L a]; rfl
  have ha: L 1=1:= T.selected_one x
  have hk:=hd 1; rw [g,ha,mul_one] at hk
  exact DFunLike.ext X _ (fun i=> (hd i).trans (by rw [←hk,one_mul]))

theorem cannot_split {F G : B→ₚ[ℂ]ℂ}(p:F 1=1)(q:G 1=1) (a b:ℝ) (h₁:0<a)(h₂:0<b)
    (e:∀ x':B, T.selected x x'=(a:ℂ)*F x'+(b:ℂ)*G x'):
    F=T.selected x ∧ G=T.selected x := by
  have ht(a b:ℝ)(F G:B→ₚ[ℂ]ℂ)(p:F 1=1)(h₁:0<a)(h₂:0<b)
      (e:∀ t, (T.selected x t).re=a*(F t).re+b*(G t).re): F=T.selected x:= by
    refine T.extreme_station x h F p (C:=Real.sqrt a⁻¹) (fun v=>?_)
    rw [Real.sq_sqrt (by positivity),e]
    have hx: 0≤(G (star v*v)).re:= (RCLike.nonneg_iff (K:=ℂ)|>.mp (G.map_nonneg (star_mul_self_nonneg _))).1
    rw [mul_add,inv_mul_cancel_left₀ h₁.ne']
    exact le_add_of_nonneg_right (by positivity)
  have hg(t): (T.selected x t).re=a*(F t).re+b*(G t).re:=by rw [e]; simp
  exact ⟨ht a b F G p h₁ h₂ hg, ht b a G F q h₂ h₁ (fun t=> (hg t).trans (add_comm ..))⟩
end Transaction
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory.Transaction.cannot_split
