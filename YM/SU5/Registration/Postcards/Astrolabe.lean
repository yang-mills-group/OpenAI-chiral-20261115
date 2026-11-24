import YM.SU5.Registration.Postcards.Pilgrim
import YM.SU5.FiniteGaugeData.Dally.Apso

/-!
 # Euclidean crossing (116) by finite averages escaping to infinity.
 
 Enough in this version to run many usual *Eu boost-plane* tests. No full-cone estimate
 used in the cluster pricing, in E or in M! (Need equality of unconditioned point-moment at the indicated
 tests as structural angular estimate.) Our method uses real-angle co-rotation even
 in the payments evaluating (116). Works with REAL displacements large even in every axis,
 need not supply time-ground projector equality to joint projection of unconditioned.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Passage
open Boundary Mink Analysis Function Set Filter OS.Semigroup
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
open CF.Buffered.Afterglow.Tower.VacuumSelection
open CF.Buffered.Afterglow.Hierarchy.Seld
open CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Carton
variable {H : Hilbert} (S : OS.Semigroup H timeAxis)
open ContinuousLinearMap
-- we take a short turn, payments already at real Eu positions. Generate space rotations etc by composing only these three tφ planes (proof later). Coins separate ANY origin along both pictures co-rotating.
def ampleStep (v:E4): Prop:=∀ i:Axis,0<v i
lemma ample_open : IsOpen {v:E4|ampleStep v}:=by
 simp_rw [ampleStep,Set.setOf_forall]; exact isOpen_iInter_of_finite fun i=> isOpen_lt continuous_const ((PiLp.continuous_apply ..))
lemma ample_time (v:E4)(p:ampleStep v):0<YM.time v:=p _
abbrev sizedStep:= Option (Bool × Axis)
def compactStep :E4:= WithLp.toLp 2 fun _=>1
noncomputable def compass :sizedStep→ E4
 | none => compactStep
 | some (true,i) => basis i+compactStep
 | some (false,i)=> Real.sqrt 2 • basis i+compactStep
lemma aim_compass (i:sizedStep) : ampleStep (compass i):=by
 cases i with
 | none=> exact fun _=> zero_lt_one
 | some i=> rcases i with ⟨i,j⟩; cases i<;> (intro k; by_cases p:k=j<;> simp [p, compass, compactStep]) ; exact lt_of_le_of_lt (Real.sqrt_nonneg _) (lt_add_one _)
-- helper
lemma price_axis (N : AddSubgroup E4) (h:IsClosed (N:Set E4)) (y:E4) (p:y∈N)(q:(Real.sqrt 2) • y∈ N) (s:ℝ): s • y ∈ N:=by
 let m: ℝ →+ E4:= { toFun t:= t • y, map_zero':= zero_smul _ _, map_add' a b:=add_smul .. }; let T:=N.comap m
 have hz:IsClosed (T:Set ℝ):=h.preimage (show Continuous m from continuous_id.smul continuous_const)
 have hp:AddSubgroup.closure ({Real.sqrt 2,1}:Set ℝ) ≤ T:=(AddSubgroup.closure_le _).mpr (pair_subset_iff.mpr ⟨q,(by change (1:ℝ)•y∈N; rwa [one_smul])⟩)
 have he: Dense (AddSubgroup.closure ({Real.sqrt 2,1}:Set ℝ): Set ℝ):= dense_addSubgroupClosure_pair_iff.mpr (by simpa using irrational_sqrt_two)
 exact closure_minimal (SetLike.coe_subset_coe.mpr hp) hz (he s)
lemma compact_cost : Priced compass:=by
 let f:= compass; let T:= AddSubgroup.closure (range compass); let N:= T.topologicalClosure
 have h(i:sizedStep): f i∈ N:= T.le_topologicalClosure (AddSubgroup.subset_closure (mem_range_self i))
 intro x; let g := EuclideanSpace.basisFun Axis ℝ
 have he:(∑ i : Axis,x i • basis i)=x:=by simpa only [g, EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,basis] using g.sum_repr x
 change x∈N; rw [← he]; apply AddSubgroup.sum_mem N; intro i _
 have hp : basis i+compactStep∈N:=h (some (true,i)); have hu: Real.sqrt 2 • basis i+compactStep∈N:=h (some (false,i))
 exact price_axis N T.isClosed_topologicalClosure (basis i) (by simpa using N.sub_mem hp (show compactStep∈ N from h none)) (by simpa using N.sub_mem hu (show compactStep∈N from h none)) _
lemma compact_turn {I:Type}(f:I→E4)(q:Priced f)(r:Ortho) : Priced (Ortho.move r ∘ f):=by
 let N:= AddSubgroup.closure (range (Ortho.move r ∘ f)); let Q:= N.topologicalClosure; have hp: AddSubgroup.closure (range f) ≤ Q.comap r.motion.toLinearEquiv.toAddMonoidHom:= (AddSubgroup.closure_le _).mpr (by
    rintro i ⟨v,rfl⟩; exact N.le_topologicalClosure (AddSubgroup.subset_closure (mem_range_self (f:=Ortho.move r ∘ f) v)))
 obtain h:= N.isClosed_topologicalClosure.preimage r.motion.continuous
 intro x; obtain ⟨v,rfl⟩:= r.motion.surjective x
 exact closure_minimal (SetLike.coe_subset_coe.mpr hp) h (q v)
abbrev plane (j:SpaceAxis) (t:ℝ):= Ortho.oneParameter (Ortho.plane timeAxis j.castSucc) t
lemma eventually_compass (j:SpaceAxis):∀ᶠ t:ℝ in 𝓝 0,∀ k:sizedStep, ampleStep (Ortho.move (plane j t) (compass k)):=by
 refine eventually_all.mpr (fun i=> eventually_all.mpr (fun k=>?_)) -- unfold ampleStep issue
 let f(t):= Ortho.move (plane j t) (compass i) k; refine (Work.A13.hasDerivAt_coord _ _ _ (0:ℝ)).continuousAt.tendsto.eventually (lt_mem_nhds ?_); change 0<f 0; rw [show f 0=compass i k from (by unfold f plane; rw [Work.A13.oneParameter_zero,Ortho.move_one])]; exact aim_compass i k
/-- any word-distance threshold (use scalar on all axes both). -/
lemma high_fee (U:Ortho) (v:E4)(p:ampleStep v)(q:ampleStep (Ortho.move U v))(C:ℝ) : ∃ x:E4, (∀ i:Axis,C<x i)∧ (∀ i:Axis,C< Ortho.move U x i):=by
 have hX(x:E4)(hx:ampleStep x): ∀ᶠ t:ℝ in atTop,∀ i:Axis,C < (t•x:E4) i:= by
   refine eventually_all.mpr fun i=>?_; filter_upwards [eventually_gt_atTop (C/x i)] with a ha; exact (div_lt_iff₀ (hx i)).1 ha
 obtain ⟨w,p,g⟩:= ((hX v p).and (hX _ q)).exists; exact ⟨w•v,p,by rw [show Ortho.move U (w•v)=w•Ortho.move U v from U.motion.map_smul w v]; exact g⟩
end YM.SatinWFixed.Passage
open YM.SatinWFixed.Passage
#print axioms compact_turn
#print axioms compact_cost
#print axioms eventually_compass
