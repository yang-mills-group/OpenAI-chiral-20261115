import YM.SU5.FiniteGaugeData.Marked.Stage

/-!
# Remove clipping for fixed tests. Transfer to the actual unprimed history.

In particular for any path meeting the cone eventually the cutoff tends to
infinity by the cone itself, so comparisons paid subject to that cone (also
on arbitrary Borel tests with a sup cost) shrink. Charge the sup comparison
for each *fixed* test, after the diagonal lemma on the partner (warm) law.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {K:Calibration} {H:Histories K}{l:ℕ} (c:Circuit K H l)
namespace Circuit
variable {c} {i k:ℕ→ℕ}
structure Setlist (c:Circuit K H l) (i k:ℕ→ℕ):Prop where
  γ : StrictMono i
  ζ : StrictMono k
  funds : ∀ a b, c.inCone (i a) (k b) → Wick H (c.volume (i a)) (c.cut (k b))
  read (S:Finset Cover)(u:Chorus)(x:Purse S):
    ∃ F z, Couplet i k (trimmed H l c S u x) F z (fun f=> ∀ᶠ n in atTop,c.inCone (i n) (k (f n)))
namespace Setlist
variable (p:Setlist c i k)
def night : Process K where
  m:= c.volume ∘ i
  sides _:= c.admitted _
  grows := c.v_grows.comp p.γ.tendsto_atTop
  n:=fun _=> c.cut∘k
  grows_n _:= (c.uv.comp p.ζ).tendsto_atTop
local notation "φ" => p.night.atUV H
local notation "invoiced" a:max => (∀ᶠ r:ℕ in atTop,(p.night.m r).val^5 ≤ p.night.n r (a r))
include p
lemma pass (m:ℕ): ∀ᶠ n in atTop, c.inCone (i m) (k n):= p.ζ.tendsto_atTop.eventually (c.visits _)
lemma permit (m:ℕ): ∀ᶠ n in atTop,Wick H (p.night.m m) (p.night.n m n):= (p.pass m).mono (p.funds m)
lemma funds_cone {a:ℕ→ℕ} (q:invoiced a): ∀ᶠ r in atTop,Wick H (p.night.m r) (p.night.n r (a r)):= q.mono fun n h=> p.funds n _ h
lemma strides {a:ℕ→ℕ} (q:invoiced a) : Tendsto (fun r=> p.night.n r (a r)) atTop atTop := by
  have he:= (tendsto_pow_atTop (α:=ℕ) (by decide : (5:ℕ) ≠ 0)).comp ((c.ir.comp p.γ).tendsto_atTop)
  refine tendsto_atTop.2 fun n=>?_
  filter_upwards [q,he.eventually_ge_atTop n] with r v h
  exact h.trans v

structure Hit (c:Circuit K H l)(i k:ℕ→ℕ)(p:Setlist c i k)(f:Family K)(z:ℂ):Prop where
  iter : Iterated H (night p) f z
  joint (a:ℕ→ℕ)(h:∀ᶠ r:ℕ in atTop, (p.night.m r).val^5 ≤ p.night.n r (a r)) : Tendsto (fun r=> p.night.atUV H r (a r) f) atTop (𝓝 z)

local notation "M" => (p.night).m
local notation "Q" => (p.night).n

lemma entered (S:Finset Cover)(u:Chorus)(w:Bracket S u)(x:Purse S):
    ∀ᶠ m in atTop, ∀ t:ℕ,c.inCone (i m) (k t)→ trimmed H l c S u x (i m) (k t)=hearth H (M m) (Q m t) (note K x.val u (M m)) := by
  filter_upwards [p.night.grows.eventually (room H l S)] with y v n h
  unfold trimmed; rw [dif_pos ⟨w,v (c.vis _) _ (p.funds y n h)⟩]; rfl

lemma fading (S:Finset Cover) (u:Chorus)(w:Bracket S u)(x:Purse S) (a:ℕ→ℕ) (h:invoiced a) :
    Tendsto (fun r=> φ r (a r) (note K x.val u)-hearth H (M r) (Q r (a r)) (note K x.val u (M r))) atTop (𝓝 0) := by
  obtain ⟨D,e⟩:= x.property.env.cost
  have hp : 0 ≤ D:= (norm_nonneg _).trans (e (1,1))
  refine Metric.tendsto_nhds.mpr fun r hr=> ?_
  have hx:0<r/(D+1):=by positivity
  filter_upwards [(p.strides h).eventually (cone_ratio H hx),p.funds_cone h] with n v hv
  have H':= ((note_t K u x.property w.tines).support (M n)).env
  rw [dist_zero_right]
  apply (v (M n) hv.allowed _ H' D (fun t=> (pitched K u _ _ t).trans (e _))).trans_lt
  calc
    r/(D+1)*D < r/(D+1)*(D+1):=by nlinarith only [hx]
    _ = r := div_mul_cancel₀ _ (by positivity)

lemma sung_hit (S:Finset Cover)(u:Chorus)(w:Bracket S u)(x:Purse S): ∃ z:ℂ, Hit c i k p (note K x.val u) z:=by
  obtain ⟨F,z,t⟩:=p.read S u x; let X := note K x.val u
  have ht (m:ℕ): Envelope (X (M m)) := ((note_t K u x.property w.tines).support (M m)).env
  refine ⟨z,⟨⟨F ∘ i,?_,t.periods⟩,?_⟩⟩
  · filter_upwards [p.entered S u w x] with m hm
    let g j:= hearth H (M m) (Q m j) (X (M m)); have he:Tendsto g atTop (𝓝 (F (i m))):=
      (t.inner (i m)).congr' ((p.pass m).mono fun j e=> hm j e)
    have hz:= ((all_ratio_fixed H (p.night.sides m) (X (M m)) (ht m)).comp (p.night.grows_n m))
    change Tendsto (fun k=> φ m k X-g k) atTop (𝓝 0) at hz
    simpa only [sub_add_cancel,zero_add,X,comp_apply] using hz.add he
  intro a q
  let g j:=hearth H (M j) (Q j (a j)) (X (M j)); have he:Tendsto g atTop (𝓝 z):=by
    refine (t.paths a q).congr' ((q.and (p.entered S u w x)).mono (fun j h=> h.2 (a j) h.1))
  simpa only [g,X,sub_add_cancel,zero_add] using (p.fading S u w x a q).add he


lemma Hit.zero : Hit c i k p (0:Family K) 0:=by
  have h a b:φ a b 0=0:=by have e:=Process.cap_scale H (night p) 0 (0:Family K) a b; simpa only [zero_smul,zero_mul] using e
  constructor
  · refine ⟨0,Eventually.of_forall fun m=>?_,tendsto_const_nhds⟩; simp_rw [h]; exact tendsto_const_nhds
  intro v _; simp_rw [h]; exact tendsto_const_nhds
lemma Hit.scale (x:Family K)(z:ℂ)(c₁:ℂ)(h:Hit c i k p x z): Hit c i k p (c₁ • x) (c₁*z):= by
  refine ⟨h.iter.times c₁,fun a w=>?_⟩; simpa only [Process.cap_scale] using (h.joint a w).const_mul c₁
lemma Hit.more {x y:Family K}{z z':ℂ}(hx:TestFamily K true x)(hy:TestFamily K true y)(h:Hit c i k p x z)(g:Hit c i k p y z'): Hit c i k p (x+y) (z+z') := by
  refine ⟨h.iter.more hx hy g.iter,fun a w=>?_⟩
  refine ((h.joint a w).add (g.joint a w)).congr' ((p.funds_cone w).mono fun n e=> ?_)
  obtain ⟨s,X⟩:=hx.paid; obtain ⟨t,Y⟩:=hy.paid
  let N:=M n; have hs:= (X.support N).env; have ht:= (Y.support N).env
  dsimp only [Process.atUV,Histories.cap,atZero]; rw [Pi.add_apply,mark_add e.loom_m hs ht (e.shot.cap_grant.paid 0 e.step).1,add_div]
lemma access {f:Family K} (h:TestFamily K true f):∃ z, Hit c i k p f z:=by
  obtain ⟨S,t⟩:=h.paid
  refine Submodule.span_induction (s:=atoms K S false) (p:=fun f _=>∃ z,Hit c i k p f z) (fun f pA=>?_) ⟨0,Hit.zero p⟩ ?_ ?_ (Sound.whole t)
  · obtain ⟨f',u,v,w,h',rfl⟩:=pA; exact p.sung_hit S u ⟨w,h'⟩ ⟨f',v⟩
  · intro x y hx hy h k; obtain ⟨z,h₀⟩:=h; obtain ⟨v,v'⟩:=k
    exact ⟨z+v,Hit.more p ⟨⟨S,Sound.test_span hx⟩,fun w=>by contradiction⟩ ⟨⟨S,Sound.test_span hy⟩,fun w=>by contradiction⟩ h₀ v'⟩
  intro a x _ h; obtain ⟨z,g⟩:=h; exact ⟨a*z,Hit.scale p x z a g⟩

def listener(f:Family K):ℂ:= if h:TestFamily K true f then (p.access h).choose else 0
lemma arrives : Settled H (night p) true (listener p):=by
  have e(f:Family K)(h:TestFamily K true f):Hit c i k p f (listener p f):=by rw [listener,dif_pos h]; exact (p.access h).choose_spec
  exact ⟨fun f h=>(e f h).iter,fun _=>⟨c.cut∘k,rfl,fun f h a v=>(e f h).joint a v⟩⟩
end Setlist

lemma marquee (c:Circuit K H l)(pay:ℕ→ℕ→Prop)(gp:∀ i,∀ᶠ k:ℕ in atTop,pay i k):
    ∃ i k:ℕ→ℕ, ∃ p:Setlist c i k, ∃ E, Settled H p.night true E ∧ ∀ a b,c.inCone (i a) (k b)→pay (i a) (k b):=by
  obtain ⟨i,k,g,v,H,h⟩:= recital (c:=c) pay gp
  let p:Setlist c i k:= ⟨g,v,fun a b h=> (H a b h).2,h⟩
  exact ⟨i,k,p,p.listener,p.arrives,fun a b h=>(H a b h).1⟩
end Circuit
end YM.CF.Buffered.Afterglow
#print axioms YM.CF.Buffered.Afterglow.Circuit.marquee
