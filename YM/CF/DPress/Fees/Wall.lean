import YM.CF.DPress.Fees.Note
/-! Cone and resources by witnessed bounds. Never need to define norms on arbitrary (non-price qualified) functions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.Fees
open Function Lattice MeasureTheory Filter Metric Analytic Finset
open scoped Topology Classical BigOperators
variable {X Y I J:Type*} {a b R:ℝ}
variable {u:X→Y} {U : Dial Y} (A:I→ Dial X){V:Dial X}{x:X}
abbrev hood (u:X→Y)(V:Dial Y): Dial X:= (fun g=>g∘u) '' V
lemma landing : Budget U (u x) a ↔ Budget (hood u U) x a:= by constructor; rintro p; exact ⟨p.p,fun i ⟨g,v,r⟩=> r ▸ p.t g v⟩; intro p; exact ⟨p.p,fun i g=>p.t (i ∘ u) ⟨i,g,rfl⟩⟩
abbrev cover (T:Set I):Dial X:= ⋃ i∈ T,A i
lemma covering (T:Set I): Budget (cover A T) x a↔ 0≤a ∧ ∀ i∈T,Budget (A i) x a:=by constructor; rintro t; exact ⟨t.p,fun i g=>⟨t.p,fun j v=>t.t _ (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨g,v⟩⟩)⟩⟩; rintro ⟨p,v⟩; constructor; exact p; intro i g; obtain ⟨j,u,g⟩:= Set.mem_iUnion₂.mp g; exact (v j u).t _ g
abbrev Credit(X:Type*) := X→ ℝ→Prop
structure Receipt (Φ:Credit X)(U:Dial X):Prop where
 perspective(x:X) (a:ℝ) : Φ x a → Budget U x a
 funds (x:X) (a:ℝ): (∃ b,Φ x b) → Budget U x a → Φ x a
variable {l:X}{f:ℂ→X}(v:ℝ→ℂ)
lemma Brings.hold (p:Brings R (u∘f) (u x) U): Brings R f x (hood u U):=fun i ⟨g,v,g'⟩=>g' ▸ p g v
lemma Brings.covered (T:Set I) (p:∀ i∈ T,Brings R f x (A i)) : Brings R f x (cover A T):=by intro g v; obtain ⟨i,t,v⟩:=Set.mem_iUnion₂.mp v; exact p _ t _ v
variable {Φ:Credit X}{G:Credit Y}
namespace Receipt
variable (p:Receipt Φ V)
include p
lemma relax (u:Φ x a)(h:a≤b): Φ x b:=p.funds x b ⟨a,u⟩ ((p.perspective x a u).up h)
lemma field (v:∃ a,Φ x a): Live V x:=⟨v.choose,p.perspective _ _ v.choose_spec⟩
lemma paid (v: ∃ a,Φ x a): Φ x (meter V x) := p.funds _ _ v (Live.pays (field p v))
lemma earned (q:Φ x a) : meter V x ≤ a := (p.perspective x a q).less
lemma approved (r:Brings R f x V)(c:∀ z∈ank R,Φ (f z) a)(v:∃ a,Φ x a)(w:1<R): Φ x (a/(R-1)):= p.funds x _ v (r.win (fun i t=>p.perspective _ _ (c i t)) w)
omit p
lemma move (p:Receipt G U): Receipt (G∘u) (hood u U):=⟨ fun x a t=>landing.mp (p.perspective _ _ t),fun x a t v=> p.funds (u x) a t (landing.mpr v)⟩
variable (φ:I→Credit X) (S:Finset I)(H:J→I→ℝ)(Rx:∀ i∈S, Receipt (φ i) (A i))(hp:∀ j,∀ i∈ S,0≤H j i)
-- The three usages: qualifier over i + optional outer max over J supports. For one root use singleton. To convert from rents.When all OTHER budgets held for i (needed to guarantee minimum), or subset mask; this qualifier records prod over i even when H j i=0 all j. Later conditioning issue allocate all i unless Θ.Areas. 
abbrev Measures : Credit X:= fun x v=>0≤v ∧ ∃ r:I→ℝ,(∀ i∈ S,φ i x (r i))∧∀ j:J,(∑ i∈S,H j i*r i) ≤ v
abbrev Relay:= cover (fun j=>staff A (H j) S) Set.univ
include hp Rx
lemma collects : Receipt (Measures φ S H) (Relay A S H):=by
 constructor; · rintro x a ⟨t,r,v,g⟩; exact (covering _ _).2 ⟨t,fun j _=> (staff_up A (H j) (hp j) r (fun i p=> (Rx i p).perspective _ _ (v i p))).up (g j)⟩
 rintro x a ⟨b,z,r,v,g⟩ t; let f(i:I):= meter (A i) x; have ht(i)(w:i∈S):= (Rx i w).field (x:=x) ⟨r i,v i w⟩; exact ⟨t.p, f,fun i p=>(Rx i p).funds _ _ ⟨r i,v i p⟩ (Live.pays (ht _ p)),fun i=> staff_due _ _ (hp i) ((covering _ _|>.1 t).2 i (Set.mem_univ _)) ht⟩ -- tune Measure notation
omit hp Rx
end Receipt
end YM.CF.DPress.Fees
