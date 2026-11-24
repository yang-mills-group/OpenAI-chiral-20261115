import GaugeFieldConstruction.Coronal
import GaugeFieldConstruction.UshioQc
import YM.Dash.Regular
/-!
# Point price machine. Tie smoothness from U5. local covering principle.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10000
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Set Filter MeasureTheory Measure Complex Analysis Points Bulb
open scoped ContDiff Topology BigOperators
variable {n:ℕ}
lemma SubWeedM (p:Points n→ℝ)(hp:ContDiff ℝ ∞ p) (v:Test n) : tsupport (weigh p hp v) ⊆ tsupport p:=by
 apply closure_mono; intro x hx e; change p x=0 at e; exact hx (by change p x • (v x:ℂ)=0; simp[e])
lemma SubWithdrawM (p:Points n→ℝ)(hp:ContDiff ℝ ∞ p)(v:Test n) : tsupport (v-weigh p hp v) ⊆ tsupport v:=by
 apply closure_mono; intro x hx e; change v x=0 at e; exact hx (by change v x-p x • (v x:ℂ)=0; simp[e])
-- additive allowed-tests. Finite subcover. Works for all simultaneous coordinates. Variants translated.
lemma patchMars (A:Test n→Prop)(za:A 0)(hA:∀ i j,A i→A j→A (i+j))
    (h:∀ x∈conf n, ∃ s∈𝓝 (x:Points n), ∀ p:Test n, tsupport p⊆s→A p)(p:Test n): A p :=by
 classical
 let V: Set (Points n) := tsupport p
 have hK:IsCompact V:=p.hasCompactSupport
 have hu (x:V) : ∃ r:ℝ,0<r ∧ ∀ q:Test n,tsupport q ⊆ Metric.closedBall (x.val) (2*r) → A q:=by
    obtain ⟨s,e,t⟩:=h x.val (p.tsupport_subset x.property)
    obtain ⟨r,he,hq⟩:=Metric.nhds_basis_closedBall.mem_iff.mp e
    refine ⟨r/2,by positivity,fun q s'=> t q ?_⟩; rw[show 2*(r/2)=r by ring] at s'; exact s'.trans hq
 choose r hr hs using hu
 let U (x:V):=Metric.ball x.val (r x)
 have hp : V ⊆ ⋃ i:V,U i:=fun x hx=> mem_iUnion.mpr ⟨(⟨x,hx⟩:V),Metric.mem_ball_self (hr _)⟩
 obtain ⟨T,hT⟩:= hK.elim_finite_subcover U (fun i=>Metric.isOpen_ball) hp
 have hit (l:Finset V)(q:Test n)(hq:tsupport q⊆⋃ i∈l, U i): A q:=by
    induction l using Finset.induction_on generalizing q with
    | empty =>
        have hz:q=0:= TestFunction.ext fun x => by
           apply image_eq_zero_of_notMem_tsupport; intro hx; simpa using hq hx
        rwa [hz]
    | @insert i s H Hi =>
        let g:ContDiffBump i.val:=⟨r i,2*r i,hr _,by linarith[hr i]⟩
        let m:=weigh g g.contDiff q; let t:=q-m
        have ht:tsupport t⊆⋃ i∈s,U i:=by
           intro x hx
           obtain ⟨j,hj⟩:=mem_iUnion.mp (hq (SubWithdrawM _ _ _ hx))
           obtain ⟨hh,hx'⟩:=mem_iUnion.mp hj
           rcases Finset.mem_insert.mp hh with hh|hh
           · subst j
             exfalso
             refine (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
             filter_upwards [Metric.isOpen_ball.mem_nhds hx'] with y hy; change q y-g y • (q y:ℂ)=0; rw [g.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_smul,sub_self]
           exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hh,hx'⟩⟩
        have hy:tsupport m⊆Metric.closedBall (i.val) (2*r i):= Subset.trans (SubWeedM _ _ q) g.tsupport_eq.le
        exact (show t+m=q from sub_add_cancel q m) ▸ hA t m (Hi _ ht) (hs i m hy)
 exact hit T p hT
lemma ownMars (x:E4)(X : Fin n→ E4) (i:Fin n) (h:∀j≠i,x≠X j): ∃ k:ℝ,0<k∧∀j,j≠i→X j ∉ Metric.closedBall x k:=by
 have he(j:Fin n): ∀ᶠ k in 𝓝 (0:ℝ),j≠i → (X j∉Metric.closedBall x k) :=by
    by_cases u:j=i; · exact Eventually.of_forall fun _ hy=> (hy u).elim
    have hp:0<dist (X j) x:=dist_pos.mpr (Ne.symm (h j u))
    exact (gt_mem_nhds hp).mono fun v hv _ e=>not_lt.mpr (Metric.mem_closedBall.mp e) hv
 exact ((show ∀ᶠ r in 𝓝[>] (0:ℝ),0<r from self_mem_nhdsWithin).and ((eventually_nhdsWithin_of_eventually_nhds (eventually_all.mpr he)))).exists
lemma HoursMars (x:Points n)(i:Fin n)(b:Bulb)(u:b.lit (x i))(v:∀ j,j≠i→ x j∉ b.run) : ∀ᶠ y in 𝓝 x, b.lit (y i)∧∀j,j≠i→ y j∉ b.run:=by
 have hx:= (eventually_eventually_nhds.mpr u); have hm: Continuous fun x:Points n=>x i:=by fun_prop
 refine ((hm.continuousAt.tendsto (x:=x)).eventually hx).and (eventually_all.mpr (fun j=>?_))
 by_cases t:j=i
 · exact Eventually.of_forall fun _ h=> (h t).elim
 have U:IsClosed b.run:=isClosed_tsupport _; have c:Continuous fun x:Points n=>x j:=by fun_prop
 exact ((c.tendsto _).eventually (U.isOpen_compl.mem_nhds (v j t))).mono fun x hx _=>hx
lemma needMars (x:Points n)(h:x∈conf n)(i:Fin n):∃ b:Bulb,b.lit (x i)∧∀ j,j≠i→ x j ∉ b.run:=by
 obtain ⟨r,hr,q⟩:=ownMars (x i) x.ofLp i (fun j hj=> (show Injective x.ofLp from h).ne hj.symm)
 let g: ContDiffBump (x i):=⟨r/2,r,by positivity,by linarith⟩
 refine ⟨⟨g,g.contDiff,g.hasCompactSupport⟩,g.eventuallyEq_one,fun j hj=>?_⟩; change x j∉tsupport g; rw [g.tsupport_eq]; exact q j hj
#print axioms patchMars
end YM.GaugeFieldConstruction.Fathom
