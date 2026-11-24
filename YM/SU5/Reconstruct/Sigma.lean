import YM.SU5.Reconstruct.Base
import Mathlib.Order.Filter.Curry
set_option autoImplicit false
set_option maxHeartbeats 230000
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis.Regularizing
/-! Filter bookkeeping for projections before every gap.
    Uniform in independent mark charges from given level each time. -/
open Function Set Filter Metric MeasureTheory Measure InnerProductSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy Vacancy.Average Sunbelt Spectral OS Analysis Semigroup
open scoped Topology InnerProductSpace NNReal ENNReal
variable {D:Type*}{A: D → Type*}{X:Type*}
variable (L:Filter D)
def uniform (A:D→ Type*) := comap (Sigma.fst (β:=A)) L -- curry with ∀ variations
lemma at_uniform : Tendsto (Sigma.fst (β:=A)) (uniform L A) L:=tendsto_comap
lemma uniform_event {p : Sigma A → Prop} : (∀ᶠ z in uniform L A,p z) ↔ ∀ᶠ d in L,∀ i,p ⟨d,i⟩:=by
 constructor
 · rintro ⟨q,t,h⟩; exact (show ∀ᶠ i in L,i∈q from t).mono fun i u z=> h (show (⟨i,z⟩:Sigma A).1∈ q from u)
 intro h
 exact ((at_uniform (A:=A) L).eventually h).mono (fun i p=>p i.2)

lemma avg_move {U:Type*}[NormedAddCommGroup U][NormedSpace ℂ U][∀i,Fintype (A i)][∀i,Nonempty (A i)] (F : Sigma A→U)(y:U)
    (h : Tendsto F (uniform L A) (𝓝 y)) : Tendsto (fun i=>Average.center (fun z:A i=> F ⟨i,z⟩)) L (𝓝 y):=by
 refine Metric.tendsto_nhds.mpr (fun ε k=>?_)
 filter_upwards [(uniform_event L).mp (Metric.tendsto_nhds.mp h (ε/2) (half_pos k))] with i u
 rw [← Average.constant (A:=A i) y]
 exact (Average.norm_dist fun a=> (u a).le).trans_lt (half_lt_self k)
lemma avg_price {U:Type*}[NormedAddCommGroup U][NormedSpace ℂ U][∀i,Fintype (A i)][∀i,Nonempty (A i)] (F G : Sigma A→U)
    (h:Tendsto (fun i:Sigma A=>dist (F i) (G i)) (uniform L A) (𝓝 0)) : Tendsto (fun i=> dist (Average.center (fun z:A i=> F ⟨i,z⟩)) (Average.center (fun z:A i=> G ⟨i,z⟩))) L (𝓝 0):=by
  refine Metric.tendsto_nhds.mpr fun ε k=>?_
  filter_upwards [(uniform_event L).mp (h.eventually (gt_mem_nhds (half_pos k)))] with i v
  rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]; exact (Average.norm_dist (fun k=> le_of_lt (show _ < _ from v k))).trans_lt (half_lt_self k)

abbrev FrameRef := ℕ×ℕ
noncomputable def zoom : Filter FrameRef := Filter.curry atTop atTop
instance profuse : NeBot zoom := ⟨by
   intro h
   have hv : ∀ᶠ z in zoom,False:= by rw [h]; exact eventually_bot
   change ∀ᶠ u:ℕ in atTop,∀ᶠ v:ℕ in atTop,False at hv
   rcases hv.exists with ⟨n,h⟩; exact h.exists.elim (fun _ p=>p)⟩
lemma zoom_out : Tendsto Prod.fst zoom atTop:= by intro s p; change ∀ᶠ i in atTop, ∀ᶠ _v:ℕ in atTop, i∈s; exact (show ∀ᶠ i in atTop,i∈s from p).mono fun _ k=>Eventually.of_forall fun _=>k
lemma zoom_in : Tendsto Prod.snd zoom atTop:= by intro s p; change ∀ᶠ _i:ℕ in atTop, ∀ᶠ j:ℕ in atTop,j∈s; exact Eventually.of_forall fun _=>p
lemma convergence [TopologicalSpace X](f:FrameRef→X)(y:ℕ→X)(e:X)(p:∀ i:ℕ,Tendsto (fun j:ℕ=>f (i,j)) atTop (𝓝 (y i)))(q:Tendsto y atTop (𝓝 e)):
    Tendsto f zoom (𝓝 e) := by
 intro s h; obtain ⟨S,t,b,c⟩:= mem_nhds_iff.mp h
 change ∀ᶠ i:ℕ in atTop,∀ᶠ j:ℕ in atTop,f (i,j)∈s
 filter_upwards [q.eventually (b.mem_nhds c)] with j k; exact (p j) (Filter.mem_of_superset (b.mem_nhds k) t)

variable (M:Mesh)
abbrev TilePoint (n:FrameRef) := Fin (M.L^n.2)
instance tile_lives (n:FrameRef) : Nonempty (TilePoint M n) := avg_lives ..
def pencilMark (n:FrameRef)(u:TilePoint M n) := notch M (n.1+n.2) (u.val:ℤ)
lemma kerf (n:FrameRef)(v:TilePoint M n): 0 ≤ (pencilMark M n v:ℝ) ∧ (pencilMark M n v:ℝ) ≤ mill M n.1:=by
 change 0 ≤ bell M _ _ ∧ bell M _ _ ≤ _
 rw [natural_time]; refine ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.mpr ?_⟩
 have h: whenly M (n.1+n.2) (M.L^n.2)=mill M n.1:=by
   rw [whenly,Nat.cast_pow]; have p:= mill_finer M n.1 (n.1+n.2) (by omega); rwa [show n.1+n.2-n.1=n.2 by omega] at p
 exact ((when_le M _ _ _).mpr v.isLt.le).trans_eq h
lemma pens {f:D→FrameRef}{v : ∀ i,TilePoint M (f i)} (p:Tendsto f L zoom): Tendsto (fun i => (pencilMark M (f i) (v i):ℝ)) L (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall fun i=> (kerf M (f i) (v i)).1) (Eventually.of_forall fun i=> (kerf M (f i) (v i)).2) ((NNReal.tendsto_coe.mpr (vanishes M)).comp (zoom_out.comp p))

-- product average: peel coordinates as many times as necessary.
lemma trimmed {I Z U : Type*}[Fintype I][Fintype Z][Nonempty Z] [DecidableEq I][NormedAddCommGroup U][NormedSpace ℂ U]
   (i:I)(f:(I→Z)→U)(h:∀y a b,f (Function.update y i a)=f (Function.update y i b)) (z:Z):
   Average.center f = Average.center (fun a:I→Z=> f (Function.update a i z)) := by
  exact Average.eq_of _ _ fun y=> by nth_rw 1 [← Function.update_eq_self i y]; exact h y (y i) z -- name check
lemma stripe {I Z U:Type*}[Fintype I][Fintype Z][DecidableEq I][NormedAddCommGroup U][NormedSpace ℂ U]
   (i:I)(f:(I→Z)→U):Average.center f = Average.center (fun z:Z=> Average.center (fun y: Other I i→ Z=> f ((Equiv.funSplitAt i Z).symm (z,y)))):=by
  rw [←Average.trade (Equiv.funSplitAt i Z).symm f,Average.domino]
lemma splice {I Z U : Type*}[Fintype I][Fintype Z][Nonempty Z][DecidableEq I][NormedAddCommGroup U][NormedSpace ℂ U]
   (i:I)(f:(I→Z)→U): Average.center f = Average.center (fun z:Z=> Average.center (fun a:I→Z=> f (Function.update a i z))) := by
 -- trade point, inserted update gives const center rearrangements
 rw [stripe i]
 apply Average.eq_of; intro z
 rw [stripe i]
 let W : Z×(Other I i→ Z) ≃ (I→ Z):=(Equiv.funSplitAt i Z).symm
 let y := Average.center (fun a:Other I i→Z=> f (W (z,a)))
 have he(x:Z)(a:Other I i→Z) : Function.update (W (x,a)) i z=W (z,a):=by
    funext j; by_cases p : j=i
    · subst j; simp [W]
    simp [W,p]
 -- note point uses Classical.propDecidable mismatch W
 change y= Average.center (fun u:Z=> Average.center (fun b:Other I i→ Z=> f (Function.update (W (u,b)) i z)))
 rw [show y=Average.center (fun _ : Z=> y) from (Average.constant (A:=Z) y).symm] -- will fail. adjust
 apply Average.eq_of; intro x; apply Average.eq_of; intro b; rw [he]
end YM.SelectionAnalysis.Regularizing
