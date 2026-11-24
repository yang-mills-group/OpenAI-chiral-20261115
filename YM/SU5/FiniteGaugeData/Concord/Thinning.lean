import YM.SU5.FiniteGaugeData.Concord.BoxOffice
import YM.SU5.FiniteGaugeData.Marked.Variation.Crimson
/-!
# Array and cones

Retain the very SAME elected limit E on all observing levels, and UV readings I at every period
of that Course. Will thin again (both sequences) to draw simultaneous transfers in this very
state; proofs, not just pointwise-in-observing-choices, e.g. can use custom ConeFilter on
inner/outer *qualified* supports.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ}{Y:Course Λ (VolumeCape.Dream.Nimbus l)}{H:Real.exp 1 ≤ Λ.x}
local notation "FAM"=> Family (tent Y H)
variable {i k p u v:ℕ→ℕ}

abbrev Paths (Y:Course Λ (VolumeCape.Dream.Nimbus l))(i k:ℕ→ℕ)(p:ℕ→ℕ) :=
  ∀ᶠ r in atTop, legacy Y (i r) (k (p r))

-- convert to a uniform (row/cutoff) filter on the cone. Definition independent of support/gates.
def ConeFilter (Y:Course Λ (VolumeCape.Dream.Nimbus l))(i k:ℕ→ℕ) : Filter (ℕ×ℕ) :=
  Filter.comap Prod.fst atTop ⊓ Filter.principal {t : ℕ × ℕ| legacy Y (i t.1) (k t.2)}

namespace ConeFilter
lemma criterion {t:ℕ×ℕ→Prop} : (∀ᶠ r in ConeFilter Y i k,t r) ↔
    ∀ᶠ r in atTop,∀ j, legacy Y (i r) (k j) → t (r,j):=by
  rw [ConeFilter,eventually_inf_principal,eventually_comap]
  constructor
  · exact fun t=> t.mono fun r p j=> p (r,j) rfl
  exact fun h=> h.mono fun r p ⟨i,j⟩ t l=> by cases t; exact p j l

lemma late_left : Tendsto Prod.fst (ConeFilter Y i k) atTop:= by unfold ConeFilter; exact tendsto_iff_comap.mpr inf_le_left
lemma late_right (h:StrictMono i)(p:StrictMono k) : Tendsto Prod.snd (ConeFilter Y i k) atTop:=by
  apply Filter.tendsto_atTop.2; intro t; apply criterion.mpr
  filter_upwards [absent Y i h (k t)] with r g j l
  by_contra! H
  exact g (l.trans ((Y.uv_grows.comp p).monotone H.le))
lemma issued : ∀ᶠ t in ConeFilter Y i k, legacy Y (i t.1) (k t.2):= criterion.mpr (Eventually.of_forall fun _ _ p=>p)
lemma uses (p:StrictMono k): (ConeFilter Y i k).NeBot:= by
  rw [←frequently_true_iff_neBot]; intro h; obtain ⟨r,t⟩:= (criterion.mp h).exists
  obtain ⟨j,u⟩:= (cadence Y k p (i r)).exists; exact t j u trivial
lemma follow (h : Paths Y i k p) : Tendsto (fun r=>(r,p r)) atTop (ConeFilter Y i k):= by
  refine tendsto_def.mpr ?_; intro s w
  filter_upwards [criterion.mp (show ∀ᶠ t in ConeFilter Y i k,t∈s from w),h] with r v t using v (p r) t
-- useful later: every predicate eventual on every qualifying path iff uniform, no metric needed
lemma iff_paths (h:StrictMono k){p:ℕ×ℕ→Prop} : (∀ᶠ t in ConeFilter Y i k,p t) ↔ ∀ q:ℕ→ℕ, Paths Y i k q → ∀ᶠ r in atTop, p (r,q r):=by
  constructor; exact fun v q t=> (follow t).eventually v
  intro v; choose b hb using fun r=> (cadence Y k h (i r)).exists
  let A(r:ℕ) := ∃ j, legacy Y (i r) (k j) ∧ ¬ p (r,j)
  let f(r:ℕ):= if h:A r then Classical.choose h else b r
  have he:∀ᶠ r in atTop,p (r,f r):= v f (Eventually.of_forall fun r=> by
    unfold f; split
    · next t=> exact (Classical.choose_spec (show A r from t)).1
    exact hb r)
  refine criterion.mpr (he.mono fun r u j q=> Classical.byContradiction fun t=> ?_)
  let c:A r := ⟨j,q,t⟩; rw [show f r=_ from dif_pos c] at u; exact (Classical.choose_spec c).2 u

lemma tendsto_iff_paths (h:StrictMono k) {A:Type*}[TopologicalSpace A]{f:ℕ×ℕ→ A}{x:A} :
    Tendsto f (ConeFilter Y i k) (𝓝 x) ↔ ∀ q:ℕ→ℕ, Paths Y i k q → Tendsto (fun r=>f (r,q r)) atTop (𝓝 x):=by
  constructor; exact fun u q v=> u.comp (follow v)
  intro t; exact tendsto_def.mpr (fun a h'=> (iff_paths h (Y:=Y) (i:=i) (p:=fun t=> f t ∈ a)).mpr (fun q u=> tendsto_def.mp (t q u) _ h'))

lemma thin (a:StrictMono u) (_:StrictMono v) : Tendsto (Prod.map u v) (ConeFilter Y (i∘u) (k∘v)) (ConeFilter Y i k):=by
  apply tendsto_def.mpr; intro s p; apply criterion.mpr
  exact (a.tendsto_atTop.eventually (criterion.mp (show ∀ᶠ t in ConeFilter Y i k,t∈s from p))).mono fun x p y h=> p (v y) h
end ConeFilter

namespace Smaller
lemma couplet {A:Type*}[PseudoMetricSpace A]{f:ℕ→ℕ→A}{g:ℕ→ A}{q:A}(d: Couplet i k f g q (Paths Y i k))(h:StrictMono k)(a:StrictMono u) (b:StrictMono v): Couplet (i∘u) (k∘v) f g q (Paths Y (i∘u) (k∘v)):=
  let f':=fun z:ℕ×ℕ=> f (i z.1) (k z.2); let t:Tendsto (f' ∘ (Prod.map u v)) (ConeFilter Y (i∘u) (k∘v)) (𝓝 q) := ((ConeFilter.tendsto_iff_paths (Y:=Y) (i:=i) h (f:=f')).mpr d.paths).comp (ConeFilter.thin a b)
  ⟨fun n=> (d.inner n).comp b.tendsto_atTop,d.periods.comp a.tendsto_atTop,fun _ h=> t.comp (ConeFilter.follow h)⟩
lemma cabinet (d:Cabinet Y H i k)(a:StrictMono u)(b:StrictMono v): Cabinet Y H (i∘u) (k∘v) :=
  ⟨d.grow_i.comp a,d.grow_k.comp b,fun x y=> d.ticket (u x) (v y),fun x y z t=> by obtain ⟨g,w,H⟩:= d.prices x y z t; exact ⟨g,w,couplet H d.grow_k a b⟩⟩
lemma universal {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(t:Universal Y H i k F E)(a:StrictMono u)(b:StrictMono v):Universal Y H (i∘u) (k∘v) F E:=
  ⟨cabinet t.pick a b,fun s f h=>couplet (t.together s f h) t.pick.grow_k a b,t.gaugeMatter⟩
end Smaller

variable {s:ℕ}{S:Finset Cover}(V: Cabinet Y H i k)
local notation "Ω"=> ConeFilter Y i k

include V
lemma court : ∀ᶠ n in ConeFilter Y i k, Stadium Y H S s (i n.1) := (V.grow_i.tendsto_atTop.comp ConeFilter.late_left).eventually (crowd ..)
lemma timely_visit (s:ℕ) : ∀ᶠ p in ConeFilter Y i k, PairIdx Y s (i p.1) (k p.2) := by
  filter_upwards [((Y.uv_grows.comp V.grow_k).tendsto_atTop.comp (ConeFilter.late_right V.grow_i V.grow_k)).eventually_gt_atTop s, ConeFilter.issued] with p v h
  exact ⟨V.ticket _ _ h,v⟩
lemma box_visit : ∀ᶠ n in ConeFilter Y i k, SeasonPass Y H S s (i n.1) (k n.2) :=
  (Eventually.and (court V) (timely_visit V s)).mono fun _ t=> ⟨t.1,t.2⟩
lemma row_use (s n:ℕ) : ∀ᶠ p in atTop, PairIdx Y s n (k p) := ((V.grow_k.tendsto_atTop.eventually_ge_atTop ((Y.voyage n).kick)).and ((Y.uv_grows.comp V.grow_k).tendsto_atTop.eventually_gt_atTop s))
lemma row_box {n:ℕ}(p:Stadium Y H S s n): ∀ᶠ m in atTop,SeasonPass Y H S s n (k m) := (row_use V s n).mono fun _ h=>⟨p,h⟩

lemma homes_cone (s:ℕ)(S:Finset Cover) : ∀ᶠ n in ConeFilter Y i k,Hosp (tips S) (side Y (i n.1) s):=by
  refine (((momentum Y s).comp V.grow_i.tendsto_atTop|>.comp ConeFilter.late_left).eventually (suitable (tips S) (tent Y H))).mono ?_
  exact fun m h=> Eq.mp (congrArg (Hosp (tips S)) (terrain Y H (Y.ir (i m.1)) s)) h
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.Smaller.universal
#print axioms YM.CF.Buffered.Concord.homes_cone
