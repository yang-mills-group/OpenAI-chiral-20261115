import YM.SU5.FiniteGaugeData.Tower.Linearity
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Roof charts with **upper** W moving, 1

When we replant W on the period box from PairsC, all links and paths on a
common length budget, even for all forests and all poses, are picked from
one *finite* library of functions OF X : PairsC. This will pay even the Borel
parts of the upper gauge constitutive laws where the readings aren't field-
uniform continuous. Keep the library regardless of actual perturbation.
-/
open Tree

section library
variable {X P Q V ι:Type*}[MeasurableSpace X][MeasurableSpace P][MeasurableSpace Q][MeasurableSpace V]

structure Palette (F:ι→X→P):Prop where
  bounded: Set.Finite (Set.range F)
  lawful(i:ι):Measurable (F i)
namespace Palette

lemma constant(p:P):Palette (fun (_:ι)(_:X)=>p):=⟨(Set.finite_singleton (fun _=>p)).subset (fun _ h=>by obtain ⟨_,rfl⟩:=h; rfl),fun _=>measurable_const⟩
lemma reindex{σ:Type*}{F:σ→X→P}(p:Palette F)(e:ι→ σ):Palette (F ∘ e):=⟨p.bounded.subset (by rintro f ⟨i,rfl⟩; exact Set.mem_range_self (e i)),fun i=>p.lawful (e i)⟩
lemma post {F:ι→X→P}(p:Palette F)(f:P→Q)(h:Measurable f):Palette (fun i=> f ∘ (F i)):=⟨((p.bounded.image (fun g=> f ∘ g)).subset (by rintro g ⟨i,rfl⟩; exact ⟨_,Set.mem_range_self i,rfl⟩)),fun i=>h.comp (p.lawful i)⟩
lemma choose_set {A:Set (X→P)}(h:Set.Finite A)(x:∀ a∈A,Measurable a){F:ι→X→P}(k:∀ i,F i∈ A):Palette F:=⟨h.subset (Set.range_subset_iff.mpr k),fun i=> x _ (k i)⟩
lemma instruction{σ:Type*}[Finite σ](F:σ→ι→X→P)(e:∀ s,Palette (F s))(p:ι→σ): Palette (fun i x=> F (p i) i x):=by
 apply choose_set (Set.finite_iUnion fun s=> (e s).bounded) ?_ ?_
 · rintro a h; obtain ⟨s,t⟩:=Set.mem_iUnion.mp h; obtain ⟨j,rfl⟩:=t; exact (e s).lawful j
 intro i; apply Set.mem_iUnion.mpr; exact ⟨p i,Set.mem_range_self i⟩
lemma couple {F:ι→X→P}{g:ι→X→Q}(p:Palette F)(t:Palette g):Palette (fun i x=> (F i x,g i x)):=by
 let a:(X→P)×(X→Q)→X→P×Q:=fun x z=>((x.1) z,(x.2) z)
 refine ⟨((p.bounded.prod t.bounded).image a|>.subset ?_),fun i=>(p.lawful i).prodMk (t.lawful i)⟩
 rintro _ ⟨i,rfl⟩; exact ⟨(F i,g i),⟨Set.mem_range_self i,Set.mem_range_self i⟩,rfl⟩
lemma both {F:ι→X→P}{g:ι→X→Q}(p:Palette F)(t:Palette g)(f:P→Q→V)(e: Measurable (Function.uncurry f)):Palette (fun i x=> f (F i x) (g i x)):= (p.couple t).post (Function.uncurry f) e

lemma all {σ:Type*}[Finite σ]{F:σ→ι→X→P}(p:∀i,Palette (F i)): Palette (fun j:ι=> fun x a=> F a j x):=by
 let f(a:σ):= Set.range (F a)
 have he: Set.Finite (Set.pi (Set.univ: Set σ) f):= Set.Finite.pi (fun i=> (p i).bounded) -- check
 let g:(σ→X→ P)→X→σ→P:=fun a x j=>a j x
 refine ⟨((he.image g).subset ?_),fun i=>measurable_pi_lambda _ fun j=> (p j).lawful i⟩
 rintro h ⟨i,rfl⟩; exact ⟨fun t=>F t i,fun a _=>Set.mem_range_self _,rfl⟩

lemma purchase [PseudoMetricSpace P][OpensMeasurableSpace P]{T:Set P}(q:IsCompact T){F:ι→X→P}(p:Palette F)(e:∀i x,F i x∈T):Deal F:=by
 let s:= Set.range F; haveI :Fintype s:=p.bounded.fintype
 let g(a:s):X→P:=a.val
 have hp(i:s): Deal (I:=ι) (T:=fun _=>P) (fun _=>g i):=by
    obtain ⟨y,p'⟩:=i; obtain ⟨a,rfl⟩:=p'; exact deal_of_one (p.lawful a) q (e a)
 exact Deal.assembly _ hp (fun i=> ⟨F i,Set.mem_range_self i⟩)

lemma clip_su {F:ι→X→SU.E}(p:Palette F):Deal F:=p.purchase isCompact_univ (fun _ _=>Set.mem_univ _)
end Palette
end library

section lookup
open Palette
variable {X:Type*}[MeasurableSpace X]
variable (S:Finset Cover){I:Type*}(n:I→Side)(F:X→LinksC)(h:Measurable F)(e:(i:I)→Edge (Seat (n i)))
include S h
-- regardless of whether x is first or second link argument. Edge location
-- needn't be near evaluated S. Includes ANY wrap. No Tivoli needed.
lemma album_g :Palette (fun (i:I)(x:X)=> Satin.graft S (n i) (F x) (e i):I→X→SU.E):=by
 let addr (i:I):Option ((↥S)×Axis):= if t:∃ a:S,Satin.pole S (n i) a=(e i).1 then some (Classical.choose t,(e i).2) else none
 let q (i:Option (↥S×Axis)) : X→SU.E:= match i with |none=>fun _=>1 | some u=>fun x=>F x (u.1,u.2)
 have hp (i)(x:X): Satin.graft S (n i) (F x) (e i)= q (addr i) x:=by
    unfold addr Satin.graft; split <;> rfl
 simp_rw [hp]
 apply Palette.reindex (F:=q) _ addr
 exact ⟨Set.finite_range _,fun z=>by obtain _|u:=z; exact measurable_const; exact (measurable_pi_apply (X:=fun _:Edge Cover=>SU.E) ((u.1:Cover),u.2)).comp h⟩

omit S h
section travel
variable (t:(i:I)→ X→ Pane (n i))(p:∀ e:(i:I)→Edge (Seat (n i)),Palette (fun i x=>t i x (e i)))
include p
lemma palette_step (w:(i:I)→ Seat (n i))(s:I→Step): Palette (fun (i:I)(x:X)=> (s i).read (t i x) (w i)):=by
 let F(b:Bool)(i:I):=match b with | false => fun x=> (t i x) (w i,(s i).dir) | true=>fun x=> ((t i x) (w i-step (s i).dir,(s i).dir))⁻¹
 have ht(b:Bool):Palette (F b):=by
    cases b; exact p _; exact (p (fun i=> (w i-step (s i).dir,(s i).dir))).post Inv.inv continuous_inv.measurable
 suffices he:(fun (i:I)(x:X)=> (s i).read (t i x) (w i))=(fun i x=>F (s i).neg i x) from he ▸ instruction _ ht _
 funext i x; unfold F Step.read Lattice.Step.used; cases v:(s i).neg <;> rfl

lemma palette_walk (D:ℕ)(w:(i:I)→ Seat (n i))(a:I→Walk)(h:∀i,(a i).length≤ D):Palette (fun (i:I)(x:X)=> travel (t i x) (w i) (a i)):=by
 induction D generalizing w a with
 | zero=> simpa only [List.length_eq_zero_iff.mp (Nat.le_zero.mp (h _)),travel] using Palette.constant (ι:=I) (X:=X) (1:SU.E)
 | succ D ih=>
    -- pad the empty walk case
    let f(i:I):Step:= (a i).headD (posDir 0)
    let W(i:I):= w i+(f i).vec
    have hp:= ih W (fun i=> (a i).drop 1) (by intro i; simp; specialize h i; omega)
    let ψ i x:=(f i).read (t i x) (w i); let Φ(b:Bool) (i:I)(x:X):= if b then (ψ i x) * travel (t i x) (W i) ((a i).drop 1) else 1
    have hΦ(b:Bool):Palette (Φ b):=by cases b <;> simp only [Φ, Bool.false_eq_true,↓reduceIte]; exact Palette.constant _; exact (palette_step n t p w f).both hp (·*·) (continuous_fst.mul continuous_snd).measurable
    suffices he:(fun (i:I)(x:X)=> travel (t i x) (w i) (a i))=(fun i x=> Φ (!(a i).isEmpty) i x) from he ▸ instruction _ hΦ _
    funext i x; unfold Φ W ψ f; cases hi:a i <;> simp [travel]
end travel
end lookup
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Palette.purchase
