import YM.SU5.Aria.Footpath
import YM.SU5.Selected.Separable
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

variable (P) in
abbrev BFits (w:ℕ) (S:Finset Cover):Prop:=
   ∀i,Between K i (-b*w) (b*w) S
structure BEntry (P:Spine)(j:Axis)(w:ℕ)(f:P.Test):Prop where
  pos : 0<w
  holds : ∃ S:Finset Cover, f ∈ bay P.calibration S true ∧
     Between P.calibration j 0 (ruler P.par.block*w) S

variable {S T:Finset Cover}
lemma BFits.empty (P:Spine)(w:ℕ): P.BFits w ∅:= fun i z t=>by simp at t
lemma BFits.mono (p:P.BFits w S)(t:w≤v):P.BFits v S:=by
 have he : b*w ≤ b*v:=by gcongr; exact (ruler_gene _).le
 intro i z h; obtain ⟨hq,hv⟩:=p i _ h; rw [neg_mul] at hq ⊢; constructor <;> omega
lemma BFits.union (p:P.BFits w S)(q:P.BFits w T):P.BFits w (S∪T):=
 fun i z h=> Or.elim (mem_union.mp h) (p i _) (q i _)
lemma BFits.relocate (p:P.BFits w S)(i:Axis)(n:ℤ)(hn:n+w≤v)(hn':w-n≤ (v:ℤ)):
    P.BFits v (plow K i n S):=by
 have hp : P.BFits v S:= p.mono (by omega); intro j z h
 obtain ⟨y,q,rfl⟩:=plow_stays _ _ _ _ h; rw [moves]; split
 · next u=>
    have ht:=p j _ q
    have ha:=mul_le_mul_of_nonneg_left hn (ruler_gene (Λ).block).le
    have hf:=mul_le_mul_of_nonneg_left hn' (ruler_gene (Λ).block).le
    obtain ⟨h,t⟩:=ht
    change (-b*(v:ℤ)+_ ≤ y j + b*n)∧_
    change (_∧ y j+b*n+_≤ _); constructor <;> linarith
 exact hp j _ q
variable (P) in
lemma eventually_BFits (S:Finset Cover): ∀ᶠ w:ℕ in atTop,P.BFits w S:=by
 have hg : ∀ j:Axis,∀ᶠ w:ℕ in atTop, Between K j (-b*w) (b*w) S:=by
   intro j; apply (S.eventually_all).mpr; intro z _
   filter_upwards [eventually_ge_atTop ((z j).natAbs+(K).ℓ)] with w hw
   have h:(w:ℤ) ≤ b*w:=le_mul_of_one_le_left (by positivity) (ruler_gene _)
   rw [neg_mul]; constructor <;> omega
 exact eventually_all.mpr hg

lemma BFits.inside (p:P.BFits w S)(n:ℤ)(j:Axis)(h:(w:ℤ)≤n)(q:n+w≤v):
    Between K j 0 (b*v) (plow K j n S):=by
 intro z t; obtain ⟨he,hp⟩:=Between.relocate _ _ (p j) n z t
 have ha:=mul_le_mul_of_nonneg_left h (ruler_gene (Λ).block).le
 have hf:=mul_le_mul_of_nonneg_left q (ruler_gene (Λ).block).le
 change b*n+_+_ ≤ _ at he
 change _≤ b*n+_ at hp
 constructor <;> linarith
lemma BFits.admit (p:P.BFits w S)(u:f∈bay K S true)(n:ℤ)(j:Axis)(h:(w:ℤ)≤n)(q:n+w≤v)(hv:0<v):
    P.BEntry j v (P.shifts j n f):=
  ⟨hv,_,P.shifts_support _ _ _ u,p.inside n j h q⟩
lemma Apron.admit (D:P.Apron)(j:Axis): P.BEntry j (D.u j+D.u j) (P.shifts j (D.u j:ℤ) D.F):=
 ⟨add_pos (D.pos j) (D.pos j),_,P.shifts_support _ _ _ D.bay,by rw [Nat.cast_add]; exact D.inside_shift P j⟩

lemma BEntry.one (P:Spine)(j:Axis)(p:0<w): P.BEntry j w 1:= ⟨p,∅,one_mem _,fun _ h=>by simp at h⟩
lemma BEntry.zero (P:Spine)(j:Axis)(p:0<w): P.BEntry j w 0:= ⟨p,∅,zero_mem _,fun _ h=>by simp at h⟩
lemma BEntry.add (p:P.BEntry j w f)(q:P.BEntry j w g): P.BEntry j w (f+g):=by
 obtain ⟨u,S,h,t⟩:=p; obtain ⟨_,T,e,y⟩:=q
 exact ⟨u,S∪T,(bay K (S∪T) true).add_mem (tallerBay _ _ _ subset_union_left h) (tallerBay _ _ _ subset_union_right e), fun i v=>Or.elim (mem_union.mp v) (t i) (y i)⟩
lemma BEntry.smul (p:P.BEntry j w f)(a:ℂ): P.BEntry j w (a•f):=by
 obtain ⟨u,S,h,t⟩:=p; exact ⟨u,S,(bay K S true).smul_mem h a,t⟩
lemma BEntry.sub (p:P.BEntry j w f)(q:P.BEntry j w g): P.BEntry j w (f-g):=by
 simpa [sub_eq_add_neg] using p.add (q.smul (-1))
lemma BEntry.sum {I:Type*}(p:0<w)(d:Finset I)(f:I→P.Test)(h:∀i∈d,P.BEntry j w (f i)):P.BEntry j w (∑i∈d,f i):=by
 induction d using Finset.induction with
 | empty=> simp only [Finset.sum_empty]; exact zero P j p
 | insert i d hi ih=> rw [sum_insert hi]; exact (h i (mem_insert_self ..)).add (ih (fun k hk=> h k (mem_insert_of_mem hk)))
lemma BEntry.right (p:P.BEntry j w f)(h:w≤v):P.BEntry j v f:=by
 obtain ⟨u,S,t,z⟩:=p
 have ht:b*w ≤ b*v:= by gcongr; exact (ruler_gene _).le
 exact ⟨u.trans_le h,S,t,fun k hk=>⟨(z _ hk).1,le_trans (z _ hk).2 ht⟩⟩
lemma BEntry.left (p:P.BEntry j w f)(n:ℕ):P.BEntry j (n+w) (σ n f):=by
 obtain ⟨u,S,t,z⟩:=p; refine ⟨by omega,_,P.shifts_support j n S t,?_⟩
 intro i e
 obtain ⟨z,q⟩:=Between.relocate K j z (n:ℤ) i e
 have h : 0≤b*n:=mul_nonneg (ruler_gene _).le (by positivity)
 change b*(n:ℤ)+0+_ ≤ _ at z
 change _≤ b*(n:ℤ)+_ at q
 rw [Nat.cast_add,mul_add]; constructor <;> omega
lemma BEntry.pad (p:P.BEntry j w f)(n m:ℕ):P.BEntry j (n+w+m) (σ n f):=
 (p.left n).right (by omega)

noncomputable def BEntry.card (p:P.BEntry j w f)(s:ℕ):P.Card j s w:=by
 let S:=p.holds.choose; have h:=p.holds.choose_spec.1; have t:=p.holds.choose_spec.2
 exact ⟨P.positiveVox j s S f h (fun i e => (t i e).1),S,h,t⟩
lemma BEntry.ofCard (F:P.Card j s w)(h:0<w)(he:P.entryTest j s F=f): P.BEntry j w f:=by
 rw [←he]; exact ⟨h,F.property⟩
lemma BEntry.agrees (p:P.BEntry j w f){F:P.Card j s w}(he:P.entryTest j s F=f): p.card s=F:=
 Subtype.ext (Subtype.ext (show f.val=_ from congrArg Subtype.val he.symm))

lemma BEntry.concat (p:P.BEntry j w f)(q:P.BEntry j v g): P.BEntry j (w+v) (f*σ w g):=
  ofCard (edit Y H 0 j false w v (p.card 0) (q.card 0)) (add_pos p.pos q.pos) (Subtype.ext (editor ..))
lemma BEntry.raise (p:P.BEntry j w f)(s t:ℕ)(h:s≤t):P.BEntry j (L^(t-s)*w) (P.conveying s (t-s) f):=
 ofCard (furnished Y H s π j false w (p.card s) t h) (mul_pos (pow_pos (Λ).R.L.property _) p.pos) rfl
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
