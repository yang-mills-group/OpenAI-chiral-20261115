import YM.SU5.FiniteGaugeData.Tapestry.Samples
import YM.SU5.FiniteGaugeData.Marked.Variation.Crimson
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Extraction compatible with the given local dual system

Select further subsequences of the *same* course witnessing operator-norm
success for the sharp inter-level maps; purchases include geometric prices on
the **whole admitted cone of selected cutoffs**. No conclusion about uniqueness
of subsequential limits.
-/
set_option quotPrecheck false
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H: Real.exp 1 ≤ Λ.x)
variable (S:Finset Cover)(s i k:ℕ)
local notation "K"=> tent Y H
local notation "V"=> followBox (Λ:=Λ) (l:=l) S
local notation "Q"=> Swatch S →L[ℂ] Swatch (followBox (Λ:=Λ) (l:=l) S)
-- Zero extension to fit the two-step selection. Not representing an actual
-- step when clipped!
noncomputable def coupon : (Swatch S →L[ℂ] Swatch (followBox (Λ:=Λ) (l:=l) S)):= if h:Spanned Y S s i k then offer Y H S s ⟨(i,k),h⟩ else 0
lemma coupon_spanned {g:Spanned Y S s i k} : coupon Y H S s i k=peddle Y H S s i k (Spanned.turn Y S s g):=(dif_pos g)
lemma compact_coupon : IsCompactOperator (coupon Y H S s i k):=by
  unfold coupon; split
  next h=> exact compact_barter S Y H s ⟨(i,k),Spanned.turn Y S s h⟩
  next _=> exact isCompactOperator_zero -- tune syntax next
lemma coupon_limit_class : ∃ A : Set (Swatch S →L[ℂ] Swatch (followBox (Λ:=Λ) (l:=l) S)), IsCompact A ∧ ∀ i k, coupon Y H S s i k∈ A := by
  let A:= closure (Set.range (offer Y H S s))
  have h:IsCompact A:= (offer_tb Y H S s).closure.isCompact_of_isComplete isClosed_closure.isComplete
  refine ⟨insert 0 A,h.insert _,fun i k=>?_⟩; unfold coupon; split
  · apply Set.mem_insert_of_mem; exact subset_closure (Set.mem_range_self _)
  exact Set.mem_insert ..

abbrev propeller (r:ℕ) := (1/2:ℝ)^r
abbrev Clay (Λ:Preparation) (l:ℕ):= (S:Finset Cover) → ℕ→(Swatch S→L[ℂ]Swatch (followBox (Λ:=Λ) (l:=l) S)) -- whitespace tuning
abbrev Rack (Λ:Preparation) (l:ℕ):= (S:Finset Cover) → ℕ→ℕ→(Swatch S→L[ℂ]Swatch (followBox (Λ:=Λ) (l:=l) S))

variable {a b: ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}

lemma alongRows {X:Type*}[PseudoMetricSpace X]{χ:ℕ→ℕ→Prop}(h:∀ i,∃ k,χ i k)(f:ℕ→ℕ→X)(z:X)(p:∀ (e:ℕ→ℕ),(∀ᶠ i in atTop, χ i (e i)) → Tendsto (fun i=>f i (e i)) atTop (𝓝 z)):
  ∀ ε:ℝ,0<ε→∀ᶠ i:ℕ in atTop,∀ k,χ i k→ dist (f i k) z < ε:=by
  intro ε v; let w(i:ℕ):= if t:∃ k,χ i k ∧ ε≤dist (f i k) z then Classical.choose t else Classical.choose (h i)
  have hw(i): χ i (w i):=by
    unfold w; split
    next t=> exact (Classical.choose_spec t).1
    next _=> exact Classical.choose_spec _
  filter_upwards [Metric.tendsto_nhds.mp (p w (Eventually.of_forall hw)) ε v] with i h
  intro k hk; by_contra! he; have t:∃ k,χ i k ∧ ε≤dist (f i k) z:=⟨k,hk,he⟩
  unfold w at h; rw [dif_pos t] at h; exact h.not_ge (Classical.choose_spec t).2

include Y
private lemma coupletThin {X:Type*}[PseudoMetricSpace X]{u v:ℕ→ℕ}(f:Tendsto u atTop atTop)(g:Tendsto v atTop atTop)(c:StrictMono b){p:ℕ→ℕ→X}{x w}
    (h:Couplet a b p x w (fun z=>∀ᶠ i in atTop,legacy Y (a i) (b (z i)))) : Couplet (a∘u) (b∘v) p x w (fun z=>∀ᶠ i in atTop,legacy Y (a (u i)) (b (v (z i)))):= by
  refine ⟨fun n=>(h.inner n).comp g, h.periods.comp f, fun t e=>?_⟩
  apply Metric.tendsto_nhds.mpr; intro ε E
  have H:= alongRows (χ:=fun i k=> legacy Y (a i) (b k)) (fun i=> (cadence Y b c (a i)).exists) (fun i k=> p (a i) (b k)) w h.paths ε E
  filter_upwards [f.eventually H,e] with i t v'
  exact t _ v'
variable (D:Universal Y H a b I E)
include D
lemma subsystems (u v:ℕ→ℕ)(p:StrictMono u)(t:StrictMono v) : Universal Y H (a∘u) (b∘v) I E := by
  refine ⟨⟨D.pick.grow_i.comp p,D.pick.grow_k.comp t,fun r s=>D.pick.ticket (u r) (v s),?_⟩, fun s x h=> coupletThin Y p.tendsto_atTop t.tendsto_atTop D.pick.grow_k (D.together s x h), D.gaugeMatter⟩
  intro s S a x; obtain ⟨V',z,H'⟩ := D.pick.prices s S a x; exact ⟨V',z,coupletThin Y p.tendsto_atTop t.tendsto_atTop D.pick.grow_k H'⟩ -- V local notation?

omit D
abbrev Burgundy (a b:ℕ→ℕ)(I:ℕ→Family (tent Y H)→ℕ→ℂ)(E:ℕ→Family (tent Y H)→ℂ) (S:Finset Cover)(s r:ℕ) :=
  let m:= momentm Y (a r) s
  Hosp S ((tent Y H).c m) ∧ ∀ (f:Family (tent Y H)), InTest (tent Y H) true S false f→∀ A:ℝ, (∀ x,‖f m x‖≤A) →
    ‖I s f (a r)-E s f‖ ≤ propeller r*A ∧ ∀ j,legacy Y (a r) (b j)→ ‖sharp Y H s (a r) (b j) f-E s f‖ ≤ propeller r*A
lemma burgundyFurther (p:∀ (S:Finset Cover)(s:ℕ),∀ᶠ r in atTop,Burgundy Y H a b I E S s r) (u v:ℕ→ℕ)(x:StrictMono u) :
    ∀ᶠ r in atTop, Burgundy Y H (a∘u) (b∘v) I E S s r:=by
  filter_upwards [x.tendsto_atTop.eventually (p S s)] with i h
  refine ⟨h.1,fun y q A B=>?_⟩
  have he: propeller (u i)*A ≤ propeller i * A:= mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) (StrictMono.id_le x i)) ((norm_nonneg _).trans (B (1,1)))
  exact ⟨((h.2 y q A B).1).trans he,fun j ht=> ((h.2 y q A B).2 (v j) ht).trans he⟩

structure Exhibition (a b:ℕ→ℕ)(I:ℕ→Family (tent Y H)→ℕ→ℂ)(E:ℕ→Family (tent Y H)→ℂ) (F:Rack Λ l)(U:Clay Λ l): Prop where
 univ_ : Universal Y H a b I E
 parallel (S:Finset Cover)(s:ℕ):∀ᶠ r in atTop, Burgundy Y H a b I E S s r
 status (r j): legacy Y (a r) (b j) ↔ r ≤ j
 inner (S:Finset Cover)(s i:ℕ) : Tendsto (fun k=> coupon Y H S s i (b k)) atTop (𝓝 (F S s i))
 road (S:Finset Cover)(s:ℕ):∀ᶠ r:ℕ in atTop, Matinee Y S s (a r)∧∀ j, r ≤ j→ Spanned Y S s (a r) (b j) ∧ dist (coupon Y H S s (a r) (b j)) (U S s) ≤ propeller r
 IR (S:Finset Cover)(s:ℕ): Tendsto (fun i : ℕ=> F S s (a i)) atTop (𝓝 (U S s))

include D
-- optional growth variant choose later
lemma catwalk : ∃ u v F U, StrictMono u ∧ StrictMono v ∧ Exhibition Y H (a∘u) (b∘v) I E F U := by
  obtain ⟨q,z,Q'⟩:= Satin.crimson Y H D
  let X:= Finset Cover × ℕ
  obtain ⟨x,hx⟩:= exists_surjective_nat X
  let Z(n:ℕ):= (Iic n).image x
  let c:= a∘q
  have e(x':X):∀ᶠ i:ℕ in atTop,x'∈ Z i:=by obtain ⟨l,rfl⟩:=hx x'; exact (eventually_ge_atTop l).mono fun j h=> mem_image_of_mem x (mem_Iic.mpr h)
  let f(x:X):= Swatch x.1 →L[ℂ] Swatch (followBox (Λ:=Λ) (l:=l) x.1)
  let g(x:X)(i k:ℕ) := coupon Y H x.1 x.2 i k
  letI (x:X) : PseudoMetricSpace (f x):=inferInstanceAs <| PseudoMetricSpace (Swatch x.1 →L[ℂ] Swatch (followBox (Λ:=Λ) (l:=l) x.1))
  obtain ⟨v,t,L',J,h,m,W⟩:= YM.SU5.FiniteGaugeData.LocalLimit.Rings.two_steps (f:=f) g
    (fun (i:ℕ)(x:X)=>Matinee Y x.1 x.2 i) (fun (i k:ℕ)(x:X)=>Satin.PairIdx Y x.2 i k)
    (legacy Y) Z propeller (fun x=> coupon_limit_class Y H x.1 x.2) (fun x=>seasons Y H x.1 x.2) (fun i x _=>eventualPairIdx Y x.2 i) (cadence Y id strictMono_id) (absent Y id strictMono_id) (fun i=>pow_pos (by norm_num) _)
    c b (D.pick.grow_i.comp z) D.pick.grow_k
  have l(S:Finset Cover)(s:ℕ):∀ᶠ i in atTop,Burgundy Y H c b I E S s i:= Q' S s
  refine ⟨q∘v,t,(fun S s=>L' (S,s)),(fun S s=>J (S,s)),z.comp h,m, subsystems Y H D _ _ (z.comp h) m, fun S s=>burgundyFurther Y H S s l v t h,W.card,fun S s i=> W.cut (S,s) i,?_,fun S s=> W.ir (S,s)⟩
  intro S s; filter_upwards [e (S,s)] with i k
  have g:= W.cont i (S,s) k
  exact ⟨g,fun j t=> let W':= W.line i j t (S,s) k; ⟨⟨W'.1,g⟩,W'.2⟩⟩
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.catwalk
