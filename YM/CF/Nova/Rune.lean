import YM.CF.Nova.Era
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nova
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc Pic MeasureTheory Vale RG Wilson
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {m L B N:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b c v K a l r t w η τ:ℝ}{P:Grasp Y B e}{H:Pearl P}(D:Span H K b v c l r n)(p:n≤ (CSide m B).val)
-- Bare specialization, positive scale coefficient keeps shared kinetic, integrates exactly.
def primal(q:Clip)(n:Side)(β:ℝ)(x:ℝ)(U:Config group n):ℝ:= (Calm group n x).indicator (fun u=>Real.exp (-(β * basicP q u))) U
lemma prim_m(q:Clip)(n:Side)(β x:ℝ):Integrable (primal q n β x) (prior group n):= by
 let F := fun u:Config group n=> Real.exp (-(β * basicP q u)); have h:Continuous F:=Real.continuous_exp.comp (Continuous.mul continuous_const (ren_c q)|>.neg); exact (h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).indicator (calm_m ..)
lemma prim_p(q:Clip)(n:Side)(β x:ℝ)(U):0 ≤ primal q n β x U:=by unfold primal; by_cases h:U∈Calm group n x; rw [Set.indicator_of_mem h]; exact (Real.exp_pos _).le; rw [Set.indicator_of_notMem h]
lemma prim_score(q:Clip)(n:Side)(β:ℝ)(x:ℝ)(p:0<x):0 < ∫ i, primal q n β x i∂prior group n :=by
 letI : (prior group n).IsOpenPosMeasure:=by unfold prior; infer_instance
 let s:= support (primal q n β x); apply (integral_pos_iff_support_of_nonneg _ (prim_m q n β x)).mpr; swap; · exact fun i=> prim_p q n β x i
 have hp:1∈ interior s:=by rw [mem_interior_iff_mem_nhds]; filter_upwards [calm_p group n x p] with X hx; apply (show X∈ s from ?_); change primal _ _ _ _ _ ≠ 0; rw [primal,Set.indicator_of_mem hx]; exact (Real.exp_pos _).ne'
 exact Measure.measure_pos_of_mem_nhds _ (mem_interior_iff_mem_nhds.mp hp)
include D p
lemma tab_z(T:Clip)(β x τ σ:ℝ)(M:Jill.Male)(u:0<x)(s:x≤σ)(t:0<τ)(h:τ≤1)(l:(CSide m B).val^10*τ ≤ min v 1)(f:∀ U:Config group (Domain m B), flags σ U=∅→∃ f:Cart (Domain m B), ∃ d:Candle, speedB d (Domain m B)∧ lawnK (gauge f U) (Kea.tax d) τ):Tab H id (prior group (Domain m B)) (primal T (Domain m B) β x) (fun x=> changeM P x M) M (K*(CSide m B).val) τ 0 1:=by
 let n':= Domain m B; let N':= CSide m B
 let A:=primal T n' β x; let S:= Calm group n' x
 have he(u:Config group n')(g:u∈S) : flags σ u=∅:=by
   have he:u∈S:=g; rw [Finset.eq_empty_iff_forall_notMem]; intro i p; obtain ⟨j,h,w⟩:= (flags_spec ..).mp p; have ht:i∈flags x u:=(flags_spec ..).mpr ⟨j,h,s.trans_lt w⟩; rw [show flags x u=∅ from he] at ht; simp_all
 let V:= D.stmt; have ht:= D.plan m p; let F:=CapX m B e; have hp(u:Config group n')(y:u∈S): Guard u e:=by obtain ⟨g,d,v,w⟩:= f _ (he _ y); exact (CostKin D p M u g (spiral _ v) w t h l).1
 refine ⟨⟨wEquiv n',fun x=> ⟨welt_p x,fun i=> ⟨wE ..,?_⟩⟩⟩,zero_lt_one,prim_p T n' β x,prim_m ..,?_,fun i g=>f _ (he _ ?_),fun i g=> ⟨0,Pays.nil,by simp⟩⟩ -- holes
 · change 1*A i≤A _; rw [one_mul]; refine le_of_eq ?_; unfold A primal; by_cases l:i∈ S
   · have hg:wEquiv n' x i ∈ S := by change flags _ _=∅; rw [wE,flags_t]; exact l
     rw [Set.indicator_of_mem l,Set.indicator_of_mem hg,wE,basic_c]
   rw [Set.indicator_of_notMem l,Set.indicator_of_notMem]; intro t; apply l; change flags _ _=∅ at t; change flags _ _=∅; rwa [wE,flags_t] at t
 swap; · by_contra l; have he:i∉ S:= l; rw [primal, Set.indicator_of_notMem he] at g; exact (lt_irrefl _ g)
 -- simplify inst.Pays
 let X(y:F):= changeM P y.val M; let G0:= changeM (m:=m) P; let G(y:F):=beamM m B (X y)
 have hc:Continuous G:= continuous_const.inner (show Continuous X from concur H D.stmt D.eP D.p _ ht.1); have hu:ContinuousOn (fun y=> beamM m B (changeM P y M)) {U:Config group n'|Guard U e}:=continuousOn_iff_continuous_restrict.mpr hc
 let K:= fun U:Config group n'=>Real.exp (-(β*basicP T U)); have hz:Continuous K:=Real.continuous_exp.comp (Continuous.mul continuous_const (ren_c T)|>.neg)
 let B'(i):= K i • beamM m B (changeM P i M); have hy:IntegrableOn B' {U:Config group n'|Guard U e} (prior group n'):= (hz.continuousOn.smul hu).integrableOn_compact (Phase.cover_closed ..|>.isCompact)
 have hK:(fun i:Config group n'=> A i • (beamM m B (changeM P i M)))=S.indicator B':=by funext i; by_cases h:i∈S; rw [Set.indicator_of_mem h]; unfold A primal; rw [Set.indicator_of_mem h]; unfold A primal; rw [Set.indicator_of_notMem h,zero_smul, Set.indicator_of_notMem h]
 change Integrable (fun i:Config group n'=>A i • _) _; rw [hK]; exact (integrable_indicator_iff (calm_m ..)).mpr (hy.mono_set (fun i u=> hp _ u))
end YM.CF.Nova
