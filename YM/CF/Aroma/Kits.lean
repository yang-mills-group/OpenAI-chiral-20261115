import YM.CF.Aroma.Boots
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]{N:Side}
abbrev Air(N:Side):= Site (More N)→ℝ
def rake (t:Cover):Air N→L[ℝ] Air N:=
 (show Air N→ₗ[ℝ] Air N from { toFun:=fun f x=>f (x+wrap (More N) (2 • t)), map_add':=fun a b=>rfl,map_smul':=fun a b=>rfl}).toContinuousLinearMap

def mil (t:Cover) : Cab n N→L[ℝ] Cab n N := (twist (clime t)).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
lemma mil_h (t)(x: Cab n N):mil t x=twist (clime t) x:=rfl
lemma bin_hub: subHub (fun _:Site N=>bins n) = jump (Equiv.refl (Site N)) (fun _=>bins n):=by symm; apply probe; intro x k i j; simp [jump_apply,ite_mul,mul_comm]
def flatV(n:Type*)[Fintype n][DecidableEq n](N:Side): Cab n N:= jump (Equiv.refl _) (fun _=> bins n)
lemma flatA : flatV n N*flatV n N=flatV n N∧star (flatV n N)=flatV n N:=by
 unfold flatV; rw [←bin_hub]; constructor; · rw [show (subHub fun _:Site N=> bins n)*(subHub fun _=>bins n)=_ from heart (Equiv.refl _) _ _]; simp only [binsSq]; rfl
 rw [subhub_star,binsAdj] -- tune
lemma curb(t:Cover):twist (clime t) (flatV n N)=flatV n N:=by
 ext ⟨x,i⟩ ⟨y,j⟩; rw [creep]; by_cases h:x=y<;>simp only [flatV,jump_apply,Equiv.refl_apply, add_left_inj,h,mul_zero, ite_true,ite_false]
 · rw [Rush.wind,fee_one,one_mul]

def CurveH (J: Air N → Cab n N):Prop:= ∀ t:Cover,(J ∘ (rake t))=ᶠ[𝓝 0](mil t ∘ J)
abbrev InJ(n:Type*)[Fintype n][DecidableEq n](N:Side):=Air N→Cab n N
def JD (J:InJ n N):= fderiv ℝ J 0
def JG (J:InJ n N):=fderiv ℝ (fderiv ℝ J) 0
def Met (J:InJ n N)(x:Air N):Cab n N:= J x*star (J x)+(1-flatV n N)
lemma met_curve (J:InJ n N)(H:CurveH J): CurveH (Met J):=by
 intro t; filter_upwards [H t] with z hz; simp only [Function.comp_apply,mil_h] at *; unfold Met; rw [hz,map_add,map_mul,map_star,map_sub,map_one,curb]
lemma met_ray (J:InJ n N)(h:ContDiffAt ℝ ω J 0):ContDiffAt ℝ ω (Met J) 0:=by unfold Met; exact (h.mul (((starL ℝ).toContinuousLinearMap.contDiff).contDiffAt.comp _ h)).add contDiffAt_const
section move
variable {E V:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup V][NormedSpace ℝ V]
lemma firstY(t:E→L[ℝ] E)(p:V→L[ℝ] V)(f:E→V)(x:E)(h:DifferentiableAt ℝ f x)(k:DifferentiableAt ℝ f (t x))(e:f ∘ t=ᶠ[𝓝 x] p ∘ f) (w:E) : fderiv ℝ f (t x) (t w)=p (fderiv ℝ f x w):=by
 have H := ((h.hasFDerivAt |>.continuousAt)); have hu := k.hasFDerivAt.comp x t.hasFDerivAt; have hx:=p.hasFDerivAt.comp x h.hasFDerivAt; exact DFunLike.congr_fun ((hu.congr_of_eventuallyEq e.symm).unique hx) w
lemma secondY(t:E→L[ℝ] E)(p:V→L[ℝ] V)(f:E→V)(h:ContDiffAt ℝ ω f 0)(e:f ∘ t=ᶠ[𝓝 0] p ∘ f) (w u:E): fderiv ℝ (fderiv ℝ f) 0 (t w) (t u)= p (fderiv ℝ (fderiv ℝ f) 0 w u):=by
 let F:=fderiv ℝ f
 have hv: DifferentiableAt ℝ F 0 := (h.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
 let L(v:E): (E→L[ℝ] V)→L[ℝ] V:= ContinuousLinearMap.apply ℝ V v
 have he : ((L (t u) ∘ F) ∘ t)=ᶠ[𝓝 0] (p ∘ (L u ∘ F)) :=by
   have ht:Tendsto t (𝓝 0) (𝓝 0):=by simpa [ContinuousAt] using (show ContinuousAt t 0 from t.continuous.continuousAt)
   have hy:= h.eventually (by simp) -- check
   filter_upwards [hy,ht.eventually hy,eventually_eventually_nhds.mpr e] with x hx hg hb; exact firstY t p f x (hx.differentiableAt (by simp)) (hg.differentiableAt (by simp)) hb u
 have hh : HasFDerivAt ((L (t u) ∘ F) ∘ t) (((L (t u)).comp (fderiv ℝ F 0)).comp t) 0:=by
    apply HasFDerivAt.comp; swap; · exact t.hasFDerivAt
    rw [map_zero]; exact (L _).hasFDerivAt.comp _ hv.hasFDerivAt
 have hQ:= p.hasFDerivAt.comp 0 ((L u).hasFDerivAt.comp 0 hv.hasFDerivAt)
 exact DFunLike.congr_fun ((hh.congr_of_eventuallyEq he.symm).unique hQ) w
end move
lemma honk(t:Cover)(J:InJ n N)(h:ContDiffAt ℝ ω J 0)(H:CurveH J)(w): JD J (rake t w)= mil t (JD J w):=by
 have he : DifferentiableAt ℝ J ((rake t) 0):=by rw [map_zero]; exact h.differentiableAt (by simp)
 have hx:= firstY (rake t) (mil t) J 0 (h.differentiableAt (by simp)) he (H t) w; rw [map_zero] at hx; exact hx
lemma homes(t:Cover)(J:InJ n N)(h:ContDiffAt ℝ ω J 0)(H:CurveH J)(x z:Air N): JG J (rake t x) (rake t z)=mil t (JG J x z):=secondY _ _ _ h (H t) x z
end YM.CF.Aroma
