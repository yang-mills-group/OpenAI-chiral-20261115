import YM.Sextet.Quadrature
import YM.SU5.Aria.Dyad
 
/-!
# Lemma `eq:mist`, mechanism (strong-vector)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Sextet.Quadrature
open Metric Function Set MeasureTheory Filter
open scoped Topology
open YM.CF.Buffered.Afterglow.Tower.Aria
section
variable (I:Type*) [Fintype I] (X:Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
  (β:Type*) [AddGroup β]

/-- Abstract axial mixed motions on the dense group of a mesh-stack. `P` on vectors
will be specified by the mist average conclusion later in the theorem; doesn't have to
be given as an orthogonal projector. -/
structure Stage where
  η:ℕ→ℝ
  loc:β→Pose I
  tag:ℕ→Grid I→+β
  U:β→X→L[ℂ]X
  pos:∀i,0<η i
  shrink:Tendsto η atTop (𝓝 0)
  labels:∀i q,loc (tag i q)=node (η i) q
  eventual (z:β):∀ᶠi in atTop, ∃q, tag i q=z
  contract:∀z x, ‖U z x‖≤‖x‖
  operate:∀z w x, U z (U w x)=U (z+w) x
end

namespace Stage
variable {I:Type*} [Fintype I] {X:Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {β:Type*}
  [AddGroup β] (S:Stage I X β)

section Fare
variable [NormedSpace ℝ X] (f:Pose I→X)

def load (i:ℕ)(q:Grid I) :X:=S.U (S.tag i q) (f (node (S.η i) q))
def fare (i:ℕ) : X := (S.η i)^Fintype.card I • ∑ᶠ q,S.load f i q

variable {f} (hf:HasCompactSupport f)
include hf
omit [NormedSpace ℝ X] in
lemma secured (i:ℕ) : HasFiniteSupport (S.load f i) := by
  refine (family _ (S.pos i) hf).subset ?_
  intro v u
  refine fun h=> u ?_
  have h:f (node (S.η i) v)=0:=h
  rw [load,h,map_zero]

lemma fare_add {g:Pose I→X} (hg:HasCompactSupport g) (i:ℕ) :
    S.fare (f+g) i=S.fare f i+S.fare g i := by
  unfold fare
  have e:S.load (f+g) i=(fun q=>S.load f i q + S.load g i q):=funext fun v=>map_add ..
  rw [e,finsum_add_distrib (S.secured hf i) (S.secured hg i),smul_add]
lemma fare_sub {g:Pose I→X} (hg:HasCompactSupport g) (i:ℕ) :
    S.fare (f-g) i=S.fare f i-S.fare g i := by
  unfold fare
  have e:S.load (f-g) i=(fun q=>S.load f i q - S.load g i q):=funext fun v=>map_sub ..
  rw [e,finsum_sub_distrib (S.secured hf i) (S.secured hg i),smul_sub]
omit hf
lemma fare_smul [IsScalarTower ℝ ℂ X] (d:ℂ) (i:ℕ) :
    S.fare (d • f) i=d • S.fare f i := by
  unfold fare
  rw [smul_comm d,smul_finsum d]
  have e:S.load (d • f) i=(fun q=> d • S.load f i q):=funext fun v=>map_smul ..
  rw [e]

/-- Pay on all fare inputs, no motion hypotheses where not tested. -/
lemma bills {K:Set (Pose I)} (k:IsCompact K) : ∃ c:ℝ,0<c ∧ ∀ᶠi in atTop,∀y:Pose I→X,
    support y⊆K→∀d:ℝ,0≤d→(∀r, ‖y r‖ ≤ d)→‖S.fare y i‖≤c*d := by
  obtain ⟨c,p,h⟩:=eventually_bills (X:=X) S.pos S.shrink k
  refine ⟨c,p,h.mono fun i t y u d g b=> ?_⟩
  apply t (S.load y i) _ _ g (fun q=>(S.contract ..).trans (b _))
  intro q v
  refine u (show y (node (S.η i) q) ≠ 0 from fun a=>v ?_)
  rw [load,a,map_zero]

def nudge (z:β) (f:Pose I→X) : Pose I→X := S.U z ∘ f

def roll (z:β) (f:Pose I→X) (y:Pose I) := f (y-S.loc z)
lemma fares_match (z:β) :
    ∀ᶠ i in atTop, S.fare (S.nudge z f) i=S.fare (S.roll z f) i := by
  filter_upwards [S.eventual z] with i hi
  obtain ⟨v,rfl⟩:=hi
  let e:=Equiv.addRight v
  unfold fare
  apply congrArg _ (finsum_eq_of_bijective (f:= S.load _ i) (g:=S.load _ i) e e.bijective ?_)
  intro q
  unfold load nudge e roll Function.comp
  rw [S.operate,Equiv.coe_addRight,S.labels,node_add,add_sub_cancel_right,map_add]
end Fare

def mean (D:Mist β) (x:X) := D.mean fun z=> S.U z x
omit [Fintype I] in
lemma mean_dist (D:Mist β) (x y:X) : dist (S.mean D x) (S.mean D y) ≤ dist x y := by
  refine D.mean_budget_dist _ _ _ (D.solves _ fun z=>?_)
  rw [dist_eq_norm,←map_sub,dist_eq_norm]
  exact S.contract ..
omit [Fintype I] in
lemma mean_zero (D:Mist β) : S.mean D 0=0 := by unfold mean;simp_rw [map_zero]; exact D.mean_const _

section MeanFare
variable {f: Pose I→X} (b:HasCompactSupport f)
include b
omit S [Fintype I] [NormedSpace ℂ X] in
lemma support_image (v:X→X)(a:v 0=0) : HasCompactSupport (v ∘ f) := by
  refine .of_support_subset_isCompact b ?_
  intro x p; refine subset_closure ?_; intro k
  apply p; rw [Function.comp_apply,k,a]

omit [Fintype I] in
lemma mean_support (D:Mist β) : HasCompactSupport (S.mean D ∘ f) :=
  support_image b _ (S.mean_zero D)
variable [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
lemma mean_fee (D:Mist β) (i:ℕ) :
    S.fare (S.mean D ∘ f) i=D.mean fun z=> S.fare (S.nudge z f) i := by
  induction D with
  | point z=>rfl
  | midP A C h g=>
    change S.fare ((1/2:ℂ) • ((S.mean A ∘ f)+(S.mean C ∘ f))) i=_
    rw [S.fare_smul,S.fare_add (S.mean_support b _) (S.mean_support b _),h,g]
    rfl

omit [IsScalarTower ℝ ℂ X] in
/-- Rolling by sufficiently small reached displacements cannot durably distinguish the
prices, by uniform continuity of the original test using group property. No hypothesis of
continuity of U. Even uniform clearance in the displacements (NOT a uniform `∀ᶠ i`,
which uses mesh registration of each fixed displacement). -/
lemma nudge_bound (g:Continuous f) {ε:ℝ} (p:0<ε) :
    ∃d:ℝ,0<d∧∀z:β,‖S.loc z‖<d →
      ∀ᶠi in atTop,dist (S.fare (S.nudge z f) i) (S.fare f i)≤ε := by
  obtain ⟨R,r⟩:= b.isBounded.subset_closedBall 0
  let B:=closedBall (0:Pose I) (R+1)
  obtain ⟨c,cp,u⟩:=S.bills (K:=B) (isCompact_closedBall ..)
  let a:=ε/c
  have ap:0<a:=div_pos p cp
  obtain ⟨d,e,v⟩:=uniformContinuous_iff.mp (b.uniformContinuous_of_continuous g) a ap
  refine ⟨min d 1,lt_min e zero_lt_one,fun z h=>?_⟩
  obtain ⟨h,h'⟩:=lt_min_iff.mp h
  have r0 {y} (q:f y≠0) : ‖y‖≤R:=mem_closedBall_zero_iff.mp (r (subset_closure (s:=support f) q))
  have k : support (S.roll z f) ⊆ B := by
    intro x w
    have t:‖x-S.loc z‖≤R:=r0 w
    refine mem_closedBall_zero_iff.mpr ?_
    nth_rw 1 [← sub_add_cancel x (S.loc z)]; exact (norm_add_le ..).trans (add_le_add t h'.le)
  have yb : HasCompactSupport (S.roll z f) := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall ..) k
  filter_upwards [S.fares_match (f:=f) z, u] with i h₁ h₂
  rw [h₁,dist_eq_norm,←S.fare_sub yb b]
  have eq:c*a=ε := mul_div_cancel₀ _ cp.ne'
  refine le_trans (h₂ _ ?_ a ap.le ?_) eq.le
  · intro x y
    by_cases j:S.roll z f x=0
    · refine mem_closedBall_zero_iff.mpr ((r0 (y:=x) fun t=>?_).trans (le_add_of_nonneg_right zero_le_one))
      apply y; simp [t,j]
    exact k j
  intro q
  rw [Pi.sub_apply,←dist_eq_norm,roll]
  exact (v (by simpa [dist_eq_norm] using h)).le

variable (D:ℕ→Mist β)
  (owned:∀ε:ℝ,0<ε→∀ᶠ n in atTop, (D n).holds fun z=>‖S.loc z‖< ε)
  (P:X→X) (l:∀x,Tendsto (fun n=>S.mean (D n) x) atTop (𝓝 (P x)))
include owned
lemma nudge_mean (g:Continuous f) {ε:ℝ} (p:0<ε) :
    ∀ᶠ n in atTop,∀ᶠ i in atTop, dist (S.fare (S.mean (D n) ∘ f) i) (S.fare f i)≤ ε := by
  classical
  obtain ⟨d,q,h⟩:=S.nudge_bound b g p
  filter_upwards [owned d q] with n dn
  have t (z:β) (u:(D n).reaches z) := h _ ((D n).holds_at.mp dn z u)
  filter_upwards [((D n).hasReach.eventually_all).mpr t] with i hi
  rw [S.mean_fee b]
  exact (D n).ceiling _ _ ε ((D n).holds_at.mpr hi)

omit owned b
include l
omit [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X] [Fintype I] in
lemma result_dist (x y:X) : dist (P x) (P y) ≤ dist x y :=
  le_of_tendsto' ((l x).dist (l y)) (fun _=>S.mean_dist ..)
omit [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X] [Fintype I] in
lemma result_zero : P 0=0 :=
  tendsto_nhds_unique (l 0) (tendsto_const_nhds.congr fun _=>(S.mean_zero ..).symm)

include b
omit [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X] [Fintype I] in
lemma mean_close (g:Continuous f) {ε:ℝ} (p:0<ε) :
    ∀ᶠ n in atTop,∀x,dist (S.mean (D n) (f x)) (P (f x))≤ε := by
  let K:=insert 0 (f '' tsupport f)
  have cover(x): f x∈K := by
    by_cases fx:f x=0
    · exact Or.inl fx
    exact Or.inr ⟨x,subset_closure (s:=support f) fx,rfl⟩
  obtain ⟨A,_,a,e⟩:=((show IsCompact K from (b.image g).insert _).finite_cover_balls (e:=ε/3) (by positivity))
  have h(r:X) (_:r∈A) := tendsto_nhds.mp (l r) (ε/3) (by positivity)
  filter_upwards [a.eventually_all.mpr h] with n hn x
  have t:=e (cover x)
  simp only [Set.mem_iUnion,mem_ball,exists_prop] at t
  obtain ⟨y,yA,hx⟩:=t
  exact (dist_triangle ..).trans ((add_le_add (S.mean_dist _ (f x) y)
    ((dist_triangle ..).trans (add_le_add (hn y yA).le (S.result_dist D P l ..)))).trans (by rw [dist_comm y];linarith))

omit [IsScalarTower ℝ ℂ X] in
lemma result_close (g:Continuous f) {ε:ℝ} (p:0<ε) :
    ∀ᶠ n in atTop,∀ᶠ i in atTop,
      dist (S.fare (S.mean (D n) ∘ f) i) (S.fare (P ∘ f) i)≤ε := by
  obtain ⟨C,c,k⟩:=S.bills b
  have u:=S.result_zero D P l
  filter_upwards [S.mean_close b D P l g (div_pos p c)] with n hn
  filter_upwards [k] with i hi
  rw [dist_eq_norm,←S.fare_sub (S.mean_support b _) (support_image b _ u)]
  simp_rw [dist_eq_norm] at hn
  refine (hi _ ?_ _ (div_pos p c).le hn).trans_eq (mul_div_cancel₀ _ c.ne')
  intro x hx; refine subset_closure (s:=support f) (fun t=>hx ?_)
  change f x=0 at t
  simp [t,u,mean_zero]

include owned
lemma unpaid (g:Continuous f) :
    Tendsto (fun i=>dist (S.fare f i) (S.fare (P ∘ f) i)) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε e=>?_
  have h:0<ε/3:=by positivity
  obtain ⟨n,m,p⟩:=((S.nudge_mean b D owned g h).and (S.result_close b D P l g h)).exists
  filter_upwards [m,p] with i t q
  rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]
  exact ((dist_triangle ..).trans (add_le_add ((dist_comm ..).le.trans t) q)).trans_lt (by linarith)

/-- Ordinary single-grid price converges strongly to integral using the continuous extension
on projected vectors, independent of the choice of `Mist`. -/
theorem expand [CompleteSpace X] (hf:Continuous f)
    {F:Pose I→X} (g:Continuous F) (k:HasCompactSupport F)
    (matchNode:∀i q,S.U (S.tag i q) (P (f (node (S.η i) q)))=F (node (S.η i) q)) :
    Tendsto (S.fare f) atTop (𝓝 (∫x,F x)) := by
  have p:Tendsto (S.fare (P ∘ f)) atTop (𝓝 (∫x,F x)) := by
    refine (ages g k S.pos S.shrink).congr fun i=>?_
    have t:S.load (P∘f) i=(fun q=>F (node (S.η i) q)):=funext (matchNode i)
    unfold fare; rw [t]
  exact p.congr_dist ((S.unpaid b D owned P l hf).congr fun i=>dist_comm ..)
end MeanFare
end Stage
end YM.Sextet.Quadrature
