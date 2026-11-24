import YM.CF.BPress.Lute.Show
import YM.CF.BPress.Smooth.SU
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
/-! Smooth patch assembly tools. Smooth SU fillers doing the column-bundle proof in finite rectangles. `∞` means genuinely smooth; parentheses.[footprint]=only needed pointwise. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute
open Function Filter Finset NormedSpace Complex Metric Spin InnerProductSpace Fock
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {X Y K : Type*}[Fintype K][DecidableEq K]
-- tool helpers
namespace Fort
open Mesa
abbrev Hotel:=Set.Icc (0:ℝ) 1
variable [NormedAddCommGroup X][NormedSpace ℝ X]
def Friendly (s:Set X){Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y] (f:X→Y): Prop:=∀ x∈s,ContDiffAt ℝ ∞ f x
@[simp] lemma H0 : (0:ℝ)∈Hotel:= Set.left_mem_Icc.mpr zero_le_one
@[simp] lemma H1 : (1:ℝ)∈Hotel:= Set.right_mem_Icc.mpr zero_le_one
abbrev inward : ℝ→ℝ:=Real.smoothTransition
def jogger(a b:ℝ)(t:ℝ):=inward ((t-a)/(b-a))
lemma jogB(a b x:ℝ):jogger a b x∈Hotel:=⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
@[fun_prop] lemma jog_smooth(a b:ℝ): ContDiff ℝ ∞ (jogger a b):=Real.smoothTransition.contDiff.comp (by fun_prop) -- tune
lemma jog_hi{a b:ℝ}(p:a<b){t:ℝ}(u:b≤t): jogger a b t=1:=Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (sub_pos.mpr p)]; linarith)
lemma jog_lo{a b:ℝ}(p:a<b){t:ℝ}(u:t≤a): jogger a b t=0:=Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr u) (sub_nonneg.mpr p.le))

lemma key_entry (i j:K) : ContDiff ℝ ∞ (fun u:Op K=> u i j):=by
 let A:Op K→ₗ[ℝ] ℂ:=⟨⟨fun u=> u i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩; exact A.toContinuousLinearMap.contDiff
lemma a_smooth {n:ℕ} (A:Keys (n+1)) : ContDiffAt ℝ ∞ aside A:= Lute.mat_smooth aside A fun i j=>(key_entry _ _).contDiffAt
lemma l_smooth {n:ℕ}(A:Keys n): ContDiffAt ℝ ∞ layer A:=by
  apply Lute.mat_smooth; intro i j; refine Fin.cases ?_ (fun i=>?_) i <;> refine Fin.cases ?_ (fun j=>?_) j
  all_goals simp only [layer₁,layer₂,layer₃]
  all_goals first| exact contDiffAt_const | exact (key_entry _ _).contDiffAt
lemma d_smooth : ContDiff ℝ ∞ (Matrix.det:Op K→ℂ) := by
  show ContDiff ℝ ∞ (fun x:Op K=>x.det)
  simp_rw [Matrix.det_apply]; apply ContDiff.sum; intro i _
  have ht : ContDiff ℝ ∞ (fun X:Op K => ∏ j,X (i j) j) := contDiff_prod (fun j _=> key_entry _ _)
  rcases Int.units_eq_one_or i.sign with h|h <;> rw [h]; simpa using ht; simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul]; exact ht.neg
lemma r_def (a b:Ket K): rotary a b=1-(inner ℂ (a-b) a)⁻¹ • plate (a-b):= rfl
lemma s_smooth (i:K)(A:Op K) : ContDiffAt ℝ ∞ (shaft i) A:=by
  let T : Op K→ₗ[ℝ] Ket K:=⟨⟨shaft i,?add⟩,?s⟩
  case' add=> intro X Y; unfold shaft; rw [Matrix.add_mulVec]; rfl
  case' s => intro c X; change shaft i (c • X)=c • shaft i X; unfold shaft; rw [Matrix.smul_mulVec]; rfl
  exact T.toContinuousLinearMap.contDiff.contDiffAt
lemma r_smooth(a b:Ket K)(ha:‖a‖=1)(hb:‖b‖=1)(u:a≠b): ContDiffAt ℝ ∞ (rotary a) b:=by
  have he(k:K): ContDiffAt ℝ ∞ (fun x:Ket K=> (a-x).ofLp k) b := ((PiLp.proj (p:=2) (𝕜:=ℝ) (fun _: K=>ℂ) k).contDiff.contDiffAt).comp b (contDiffAt_const.sub contDiffAt_id)
  apply Lute.mat_smooth; intro i j; simp_rw [r_def]; simp only [plate, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.of_apply]
  apply ContDiffAt.sub contDiffAt_const; exact ((ContDiffAt.inv ((contDiffAt_const.sub contDiffAt_id).inner ℂ contDiffAt_const) ((difference_non ha hb u).2)).mul ((he i).mul ((Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt.comp b (he j)))))
lemma w_smooth(j:K)(A:Op K): ContDiffAt ℝ ∞ (wrapR j) A:=by
 unfold wrapR; apply ContDiffAt.mul contDiffAt_id; apply Lute.mat_smooth; intro i k; by_cases h:i=k; swap; · simp only [Matrix.diagonal_apply_ne _ h]; exact contDiffAt_const
 rw [h]; simp only [Matrix.diagonal_apply_eq]; split; exact (Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt).comp A d_smooth.contDiffAt; exact contDiffAt_const
/-- boost puncture section to op norm C∞ -/
def dock (a b:Ket K)(j:K)(A:Op K):= wrapR j (rotary a b*A)
lemma dock_ball {a b:Ket K}{i j:K}{A:Op K}(h:i≠j)(U:trueS A)(p:‖a‖=1)(v:shaft i A=a)(q:‖b‖=1)(l:a≠b): trueS (dock a b j A)∧shaft i (dock a b j A)=b ∧ ContDiffAt ℝ ∞ (fun b'=>dock a b' j A) b:=by
 unfold dock; obtain ⟨d,f⟩:=rotary_n p q l; obtain ⟨e,w⟩:=wrap_n ((unitary _).mul_mem d U.1) j
 refine ⟨e,?_,(w_smooth j _).comp b ((r_smooth a b p q l).mul contDiffAt_const)⟩; -- use shaft general
 have ht(K' V:Op K): shaft i (K'*V)= jet K' (shaft i V):= by unfold shaft jet; rw [Matrix.mulVec_mulVec]; -- name tune
 rw [w i h,ht,v]; exact f
lemma star_smooth(a:Op K) : ContDiffAt ℝ ∞ star a:= (starL' ℝ).toContinuousLinearMap.contDiff.contDiffAt
-- Square patch union
abbrev sqX:=Hotel ×ˢ Hotel
def sqY:= sqX ∩ {u | u.1=0∨u.1=1∨u.2=0∨u.2=1}
lemma edgeC: IsCompact sqY:= (isCompact_Icc.prod isCompact_Icc).inter_right ((isClosed_eq continuous_fst continuous_const).union ((isClosed_eq continuous_fst continuous_const).union ((isClosed_eq continuous_snd continuous_const).union (isClosed_eq continuous_snd continuous_const))))
lemma north(x:ℝ)(p:x∈Hotel) : ((x,1):ℝ×ℝ) ∈ sqY:=⟨ ⟨p,H1⟩,Or.inr (Or.inr (Or.inr rfl))⟩ -- tuple notation parse
lemma west(x:ℝ)(p:x∈Hotel) : ((0,x):ℝ×ℝ) ∈ sqY:=⟨ ⟨H0,p⟩,Or.inl rfl⟩
lemma east(x:ℝ)(p:x∈Hotel) : ((1,x):ℝ×ℝ) ∈ sqY:=⟨ ⟨H1,p⟩,Or.inr (Or.inl rfl)⟩
lemma south(x:ℝ)(p:x∈Hotel) : ((x,0):ℝ×ℝ) ∈ sqY:=⟨⟨p,H0⟩,Or.inr (Or.inr (Or.inl rfl))⟩
lemma front {u:ℝ×ℝ}(p:u∈sqY) : u.1 ∈ Hotel ∧ u.2∈Hotel:=p.1
variable (A B C D:ℝ→X)
def plank(t:ℝ)(a b:X):= (1-t) • a+t • b
@[simp] lemma palm (a b:X): plank 0 a b=a∧ plank 1 a b=b:=by simp [plank]
structure Compat (A B C D:ℝ→X):Prop where
 lb : A 0=B 0
 west : A 1=C 0
 bottom : B 1 = D 0
 top : D 1=C 1
def sky (u:ℝ×ℝ): X:= plank u.1 (A u.2) (D u.2)+plank u.2 (B u.1) (C u.1)-plank u.1 (plank u.2 (A 0) (A 1)) (plank u.2 (D 0) (D 1))
lemma sky_stock (p:Compat A B C D) (u:ℝ): sky A B C D (0,u)=A u∧ sky A B C D (u,0)= B u ∧ sky A B C D (u,1)= C u ∧sky A B C D (1,u)= D u:=by simp [sky,plank, ← p.lb,← p.west,p.bottom,← p.top]
lemma sky_law (a:Friendly Hotel A)(b:Friendly Hotel B)(c: Friendly Hotel C)(d: Friendly Hotel D): Friendly sqX (sky A B C D):=by
 intro x p; have hp:=p.1; have he:=p.2; have plan(k:ℝ × ℝ →ℝ)(f g:ℝ × ℝ→X)(c:ContDiffAt ℝ ∞ k x)(u:ContDiffAt ℝ ∞ f x)(v:ContDiffAt ℝ ∞ g x):ContDiffAt ℝ ∞ (fun i=> plank (k i) (f i) (g i)) x := ((contDiffAt_const.sub c).smul u).add (c.smul v)
 refine ((plan _ _ _ contDiffAt_fst ((a x.2 he).comp x contDiffAt_snd) ((d x.2 he).comp x contDiffAt_snd)).add (plan _ _ _ contDiffAt_snd ((b x.1 hp).comp x contDiffAt_fst) ((c x.1 hp).comp x contDiffAt_fst))).sub ?_; exact plan _ _ _ contDiffAt_fst (plan _ _ _ contDiffAt_snd contDiffAt_const contDiffAt_const) (plan _ _ _ contDiffAt_snd contDiffAt_const contDiffAt_const) -- elaboration
lemma cover (A: ℝ×ℝ→X)(p:Friendly sqY A) : ∃ B:ℝ×ℝ→X,Friendly sqX B∧ Set.EqOn B A sqY:=by
 have hx:= sky_stock (fun i=>A (0,i)) (fun i=>A (i,0)) (fun i=>A (i,1)) (fun i=> A (1,i)) ⟨rfl,rfl,rfl,rfl⟩; refine ⟨_,sky_law (fun i=>A (0,i)) (fun i=>A (i,0)) (fun i=>A (i,1)) (fun i=> A (1,i)) ?_ ?_ ?_ ?_,?_⟩; rotate_left 4
 · rintro ⟨i,x⟩ p; obtain rfl|rfl|rfl|rfl: i=0∨i=1∨x=0∨x=1:=p.2; exact (hx x).1; exact (hx x).2.2.2; exact (hx i).2.1; exact (hx i).2.2.1
 all_goals intro x h; first| exact (p _ (west x h)).comp x (f:=fun x=>(0,x)) (by fun_prop)|exact (p _ (east x h)).comp x (f:=fun x=>(1,x)) (by fun_prop)|exact (p _ (north x h)).comp x (f:=fun x=>(x,1)) (by fun_prop)|exact (p _ (south x h)).comp x (f:=fun x=>(x,0)) (by fun_prop)
end Fort
end YM.CF.BPress.Lute
