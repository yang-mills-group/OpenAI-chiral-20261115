import YM.SU5.FiniteGaugeData.Tower.Diagram
import Organdy.Treasury
import YM.SU5.Selected.Vacuum

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection

section
variable {K:Calibration}{I:Type*}{b:Filter I}{S T:Finset Cover}{n N:I→Side}{e:∀ i,K.c (n i)=N i}
 {Y W:(i:I)→Mark (N i)}{F G:I→Buffered.Family K}{x z:Buffered.Family K}
lemma Bolt.product (a:Bolt b S n e Y F x) (p:Bolt b T n e W G z):
 Bolt b (S∪T) n e (Y*W) (F*G) (x*z):=by
 have ee:(K.c ∘ n)=N:=funext e;subst N
 exact ⟨a.queue.multiply p.queue,fun i=>congrArg₂ (·*·) (show F i (n i)=Y i from a.sees i) (show G i (n i)=W i from p.sees i)⟩
lemma Bolt.revolve (j:Axis)(v:ℤ) (a:Bolt b S n e Y F x):
 Bolt b (reflectedBox j v S) n e (fun i=>reflMark j v (Y i)) (fun i=>mirror K j v (F i)) (mirror K j v x):=by
 have ee:(K.c ∘ n)=N:=funext e;subst N
 exact ⟨a.queue.revolve j v,fun i=>congrArg (reflMark j v) (show F i (n i)=Y i from a.sees i)⟩
lemma Bolt.sitePlus(a:Bolt b S n e Y F x)(t:S⊆T):
 Bolt b T n e Y F x:=⟨a.queue.sitePlus t,a.sees⟩
end

/- Same cofinal ultrafilter, all heights & demands; arrows pass any nested appointments.
 Moreover period & cutoff essentially P.period i.1 P.cutoff i.2 if desired. -/
abbrev Pair := ℕ × ℕ
abbrev garnish : Filter Pair := Filter.atTop.curry Filter.atTop
instance : garnish.NeBot:= by rw [←frequently_true_iff_neBot]; intro h; obtain ⟨_,v⟩:=(eventually_curry_iff.mp h).exists; obtain ⟨_,u⟩:=v.exists;exact u trivial
noncomputable def session:Ultrafilter Pair:=Ultrafilter.of garnish

section rate
variable {I:Type*}
/-- Allow extra generality, for a cofinal Appointment using P. -/
structure RateNet (l:Filter I)(P:Spine)(i k:I→ℕ):Prop where
 freely {A:ℕ→ℕ→Prop}:
    (∀ᶠ r in atTop,∀ᶠ t in atTop,A (P.period r) (P.cutoff t))→∀ᶠ z in l,A (i z) (k z)

variable {P:Spine}
lemma booking {B:ℕ→ℕ→Prop}(g:∀ᶠ i in atTop,∀ᶠ k in atTop,B i k):
  ∃ i k,RateNet (↑session:Filter Pair) P i k ∧ (∀ z,B (i z) (k z))∧
      ∀ᶠ z in (↑session:Filter Pair), i z=P.period z.1 ∧ k z=P.cutoff z.2 :=by
 let φ(z:Pair):= (P.period z.1,P.cutoff z.2)
 let S:Filter Pair:=session

 have c: ∀ᶠ z in S,B (φ z).1 (φ z).2:= (Ultrafilter.of_le garnish) (eventually_curry_iff.mpr <|
    (P.law.pick.grow_i.tendsto_atTop.eventually g).mono fun i h=>P.law.pick.grow_k.tendsto_atTop.eventually h)
 haveI:S.NeBot:=(inferInstance: (↑session :Filter Pair).NeBot)
 obtain ⟨p,b⟩:=c.exists
 let a(z:Pair):= if B (φ z).1 (φ z).2 then φ z else φ p
 refine ⟨fun z=>(a z).1,fun z=>(a z).2,⟨fun {A} h=>?_⟩, fun z=>?_, ?_⟩
 · filter_upwards [c, (show ∀ᶠ z in S,A (φ z).1 (φ z).2 from (Ultrafilter.of_le garnish) (eventually_curry_iff.mpr h))] with z t u; simpa only [a,if_pos t]
 · simp only [a];split <;> assumption
 filter_upwards [c] with z t; simp only [a,if_pos t]; exact ⟨rfl,rfl⟩

namespace RateNet
variable {i k:I→ℕ}{l:Filter I}(A:RateNet l P i k)
include A

lemma both {B:ℕ→ℕ→Prop}(h:∀ᶠ r in atTop,∀ᶠ t in atTop,B r t):
  ∀ᶠ z in l,B (i z) (k z):= A.freely <|
   (P.law.pick.grow_i.tendsto_atTop.eventually h).mono fun _ u=> P.law.pick.grow_k.tendsto_atTop.eventually u

lemma atPrice (s:ℕ){f:Buffered.Family P.calibration}(h:TestFamily P.calibration true f):
 Tendsto (fun z=>sharp P.run P.large s (i z) (k z) f) l (𝓝 (P.E s f)):=by
 let c:=P.law.together s f h
 refine Metric.tendsto_nhds.mpr fun ε e=> ?_
 apply A.freely (A:=fun i k=>dist (sharp P.run P.large s i k f) (P.E s f)< ε)
 filter_upwards [Metric.tendsto_nhds.mp c.periods _ (half_pos e)] with r u
 filter_upwards [Metric.tendsto_nhds.mp (c.inner (P.period r)) _ (half_pos e)] with t v
 exact (dist_triangle _ _ _).trans_lt (show _ from (add_lt_add v u).trans_le (by linarith))

lemma onQueue (s:ℕ){F:I→Buffered.Family P.calibration}{x:Buffered.Family P.calibration}
 {S:Finset Cover}(p:Q l S F x):
 Tendsto (fun z=>sharp P.run P.large s (i z) (k z) (F z)) l (𝓝 (P.E s x)):=by
 obtain ⟨C,a,y⟩:=charged P.run P.large s S
 refine Metric.tendsto_nhds.mpr fun ε e=>?_
 let η:=ε/2/(C+1)
 have h: C*η ≤ ε/2:= (mul_le_mul_of_nonneg_right (show C≤C+1 by linarith) (by unfold η; positivity)).trans_eq (by unfold η; field_simp)

 have k': ∀ᶠ z in l, Ferry P.run s (i z) (k z) ∧
     ∀ f, InTest (tent P.run P.large) true S false f →
      pay f η → ‖sharp P.run P.large s (i z) (k z) f‖ ≤ ε/2:=
    A.both (B:=fun i k=>Ferry P.run s i k ∧
     ∀ f, InTest (tent P.run P.large) true S false f →
      pay f η → ‖sharp P.run P.large s i k f‖ ≤ ε/2) (Eventually.of_forall fun n=> (y.and (ferry_later P.run s n)).mono fun r ⟨j,d⟩=>⟨d,fun f g t=> (j n d.depth f g η (t _)).trans h⟩)
 filter_upwards [k',p.car η (by unfold η; positivity),Metric.tendsto_nhds.mp (A.atPrice s (aux_test p.toBe)) _ (half_pos e)] with z ⟨d₀,d⟩ η₁ v
 let h₀:=d (F z-x) (InTest.subOp (p.goes z) p.toBe) η₁
 rw [sharp_sub P.run P.large s (aux_test (p.goes z)) (aux_test p.toBe) d₀,←dist_eq_norm] at h₀
 exact (dist_triangle _ _ _).trans_lt ((add_lt_add_of_le_of_lt h₀ v).trans_le (by linarith))

end RateNet
end rate

section
variable {I:Type*}(P:Spine) (s:ℕ)(i:I→ℕ)
abbrev moment (v:I):=momentm P.run (i v) s
abbrev tunnel (v:I):=side P.run (i v) s

lemma patronise : ∀ v,P.calibration.c (moment P s i v)=tunnel P s i v :=
   fun v=>terrain P.run P.large (P.run.ir (i v)) s
variable {P s i} {k:I→ℕ}{l:Filter I}
lemma Bolt.pays
 {Y:(v:I)→Mark (tunnel P s i v)}{S:Finset Cover}{F:I→Buffered.Family P.calibration}
 {x:Buffered.Family P.calibration}
 (b:Bolt l S (moment P s i) (patronise P s i) Y F x)
 (A:RateNet l P i k):
 Tendsto (fun z=>Journey.compass P.run (i z) (k z) s (Y z)) l (𝓝 (P.E s x)):=by
 refine (A.onQueue s b.queue).congr fun z=>?_
 rw [← b.sees]; rfl

end
#print axioms Bolt.pays
