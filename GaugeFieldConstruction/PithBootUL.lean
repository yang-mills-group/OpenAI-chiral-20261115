import GaugeFieldConstruction.ConvictBootUL
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Analysis Points Set MeasureTheory Measure Complex Bulb
open scoped Topology BigOperators ContDiff Classical
variable {n:ℕ}(a:Axis)(p:Points n)(b:Bulb)(k:Fin n)
variable {X:Type*}(J:Axis→Axis→X)(Q: ChefUL (X:=X))(F:Fin n→X)(w:∀ n F,ContinuousOn (Q n F) (conf n))
lemma TaxfulUL (b:Bulb)(f:E4→ℂ)(e:∀ x∈b.run,ContinuousAt f x): Integrable (fun x=> b x • f x):=by
 refine Continuous.integrable_of_hasCompactSupport (continuous_iff_continuousAt.mpr (fun x=>?_)) b.c.smul_right
 by_cases h:x∈b.run
 · exact b.d.continuous.continuousAt.smul (e x h)
 refine continuousAt_const.congr (?_ : (fun _ : E4=>(0:ℂ)) =ᶠ[𝓝 x] fun y=> b y • f y)
 filter_upwards [notMem_tsupport_iff_eventuallyEq.mp h] with y hy; change 0=b.f y • f y; rw [show b.f y=0 from hy,zero_smul]
noncomputable abbrev MintUL(i:Axis)(x:E4):= ovensUL J Q a F i (Points.cons x p)
variable (H:PathUL J Q)
include w H
variable (y:E4)
lemma mintUL(h: Points.cons y p∈conf (n+1))(i:Axis):ContDiffAt ℝ ∞ (MintUL a p J Q F i) y:=((PureUL J Q (Fin.cons (J i a) F) w H _ h).contDiffAt ((conf_open _).mem_nhds h)).comp (f:=fun y=>Points.cons y p) y (AlumUL.contDiff.contDiffAt.comp (g:=fun z:E4 × Points n=>AlumUL z) y (f:=fun x:E4=> (x,p)) (contDiffAt_id.prodMk contDiffAt_const)) -- tune
lemma OilUL(h: Points.cons y p∈conf (n+1)): ∑ i:Axis, D (basis i) (MintUL a p J Q F i) y=0:=by
 rw[← ((SolidUL a (Points.cons y p) 0 J Q (Fin.cons (J a a) F) w H).resolve_right (fun s=>s h))]
 apply Finset.sum_congr rfl; intro i _
 let N(z:E4):= Points.cons z p
 have hp: Function.update (Fin.cons (α:=fun _=>X) (J a a) F) 0 (J i a)= Fin.cons (J i a) F:=by funext j; refine Fin.cases ?_ (fun i=>?_) j <;> simp
 have t:= ((PureUL J Q (Fin.cons (J i a) F) w H _ h).contDiffAt ((conf_open _).mem_nhds h)).differentiableAt (by simp)
 let U:E4 →L[ℝ] Points (n+1):= AlumUL ∘L ContinuousLinearMap.inl ℝ _ _
 have he: HasFDerivAt N U y:= AlumUL.hasFDerivAt.comp y ((hasFDerivAt_id ..).prodMk (hasFDerivAt_const p y))
 rw[hp]; change fderiv ℝ (Q (n+1) (Fin.cons (J i a) F) ∘ N) y (basis i)= _; rw [fderiv_comp y t he.differentiableAt,he.fderiv,ContinuousLinearMap.comp_apply,show U (basis i)=mirDirYL 0 i from ?_]; · rfl
 ext1 j; change Points.cons (basis i) 0 j= _; refine Fin.cases ?_ (fun j=>?_) j <;>simp [Points.cons,mirDirYL, NSF.Points.direction]
lemma ShunUL (q:∀ x∈ b.run, Points.cons x p∈conf (n+1)): ∑ i:Axis,raysCostYL b i (ovensUL J Q a F i) p=0:=by
 let T:= MintUL a p J Q F
 have ht(i:Axis)(x:E4)(u:x∈b.run):ContDiffAt ℝ ∞ (T i) x:= mintUL a p J Q F w H x (q x u) i
 have h₁(i:Axis):Integrable (fun x:E4=> D (basis i) b.f x • T i x):= TaxfulUL (b.LED i) _ fun x u=> (ht i x (Bulb.strands (Bulb.cone _ i u))).continuousAt
 have h₂(i:Axis): Integrable (fun x:E4=>b.f x • D (basis i) (T i) x):= TaxfulUL b _ fun x u=>by
   change ContinuousAt (fun y=> fderiv ℝ (T i) y (basis i)) x; exact ((ht i x u).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
 have he(i:Axis):(∫ x,b.f x • D (basis i) (T i) x)=-∫ x, D (basis i) b.f x • T i x := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (h₁ i) (h₂ i) (TaxfulUL b _ fun x u=> (ht i x u).continuousAt) (fun y _=> b.d.differentiable (by simp) y) (fun y u=> (ht i y u).differentiableAt (by simp))
 have ho(y:E4):(∑ i:Axis,b.f y • D (basis i) (T i) y)=0:=by
   by_cases u:y∈b.run; · rw [← Finset.smul_sum, show (∑ i:Axis,D (basis i) (T i) y)=0 from OilUL a p J Q F w H y (q y u),smul_zero]
   simp [image_eq_zero_of_notMem_tsupport u]
 rw [← neg_eq_zero]; change -(∑ i:Axis, ∫ x,D (basis i) b.f x • T i x)=0; rw [← Finset.sum_neg_distrib]; simp_rw [← he]; rw [← integral_finsetSum _ fun i _=>h₂ i]; simp_rw [ho]; simp
lemma BindMUL (v:BreatherMars b k p): D (mirDirYL k a) (Q n F) p=∑ i:Axis,raysCostYL b i (ovensUL J Q a F i) p:=by
 choose B u e using H n p v.bounds
 let T:= B k; let U:Bulb:=⟨T.f-b.f,T.d.sub b.d,T.c.sub b.c⟩
 have q:BreatherMars T k p:= u k
 have hp(x:E4)(hk:x∈U.run): Points.cons x p∈ conf (n+1):= first_conf _ v.bounds (by
   intro j g; change p j=x at g; rw [←g] at hk
   refine ((notMem_tsupport_iff_eventuallyEq (f:=U.f)).mpr ?_) hk; by_cases t:j=k
   · subst j; filter_upwards [q.home,v.home] with x h v; change T.f x - b.f x=0; rw [show T.f x=1 from h,show b.f x=1 from v,sub_self]
   filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (q.apart _ t),notMem_tsupport_iff_eventuallyEq.mp (v.apart _ t)] with x s v; change T.f x-b.f x=0; rw [show T.f x=0 from s,show b.f x=0 from v,sub_self])
 rw [FlueUL a p J Q B u e F w k,← sub_eq_zero,← Finset.sum_sub_distrib,← ShunUL a p U J Q F w H hp]; apply Finset.sum_congr rfl; intro i _
 let F':=MintUL a p J Q F i; change (∫ x:E4,D (basis i) T.f x • F' x) - (∫ x:E4,D (basis i) b.f x • F' x)= ∫ x:E4,D (basis i) U.f x • F' x
 have he(y:Bulb)(t:BreatherMars y k p):Integrable (fun x:E4=>D (basis i) y.f x • F' x):= TaxfulUL (y.LED i) _ fun x o=> (mintUL a p J Q F w H x (RoomMars _ _ _ t x (Bulb.cone _ _ o)) i).continuousAt
 rw [← integral_sub (he _ q) (he _ v)]
 apply integral_congr_ae; refine Eventually.of_forall fun x=> ?_
 have hz : D (basis i) U.f x=D (basis i) T.f x - D (basis i) b.f x:=by unfold D; rw [show U.f=T.f-b.f from rfl,fderiv_sub (T.d.differentiable (by simp) x) (b.d.differentiable (by simp) x)]; rfl
 simp only [hz,sub_smul]
#print axioms BindMUL
end YM.GaugeFieldConstruction.Fathom
end
