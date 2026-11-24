import YM.CF.BPress.Contour.Tiers
import YM.CF.BPress.Contour.Tart
import YM.CF.BPress.Palmer.School
/-! lemma:B-contour expansions part. Expanded integrals multiply with a single common core-and-field realization, conditional on disjoint all data-block supports. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Contour
open RG Wilson Push.SectorMeasure Finset MeasureTheory Function Palmer Ledger Branch
open scoped Classical Topology BigOperators
variable {Y I:Type}{Φ:Y→ Type*}[DecidableEq I][Fintype Y][DecidableEq Y][∀ i,MeasurableSpace (Φ i)][∀ i,Nonempty (Φ i)][Nonempty Y]
variable (Z:Y→ Finset Y)(T:I→Finset Y) (D:(Seal Y)→ I→ (∀ i,Φ i)→ℂ)(G:Seal Y→(∀ i,Φ i)→ℂ)
variable (μ ν:∀ i, Measure (Φ i))[∀ i,IsProbabilityMeasure (μ i)][∀ i,IsFiniteMeasure (ν i)] (q:ℝ)(a:I→ℝ) -- q won't use.Envelope
structure Cabin :Prop where
 bill(P) (H:Core Z P):Envelope (G P)
 meter(E i):Envelope (D E i)
 extent(P)(H:Core Z P):ScopedB (G P) (station Z P)
 cond(i:I) (E S): Visible Z (T i) E=Visible Z (T i) S → D E i=D S i
 when(E i):ScopedB (D E i) (watches Z (T i) E)
def lead : Seal Y→ Seal Y:= fun i=>if Core Z i then station Z i else Z (Classical.arbitrary _)
abbrev chart : Finset Y ⊕ I→ Seal Y:=Sum.elim (lead Z) T
lemma chart_g {F:Branch.Field Y}(p:evenT F Z)(q:evenT F T): evenT F (chart Z T):=by
 intro i; cases i with
 | inl i=> change Grove F (lead Z i); unfold lead; split; exact union_g ‹Core Z i› (fun _ _=>p _); exact p _
 | inr i=> exact q _
-- place.E
abbrev lit (P:Finset (Finset Y))(J:Finset I) := berth Z P ∪ J.biUnion T
lemma lit_u(P:Finset (Finset Y⊕I))(p:Fleet Z P.toLeft): lit Z T P.toLeft P.toRight=P.biUnion (chart Z T):=by
 ext i; constructor; · intro v; rcases mem_union.mp v with v|v <;> obtain ⟨f,v,u⟩:=mem_biUnion.mp v; exact mem_biUnion.mpr ⟨.inl f, mem_toLeft.mp v,show i∈lead Z f from (show station Z f=lead Z f from (if_pos (p.1 _ v)).symm) ▸ u⟩; exact mem_biUnion.mpr ⟨.inr f,mem_toRight.mp v,u⟩ -- tune
 intro v; obtain ⟨f,v,g⟩:= mem_biUnion.mp v; cases f with|inr f=> exact mem_union_right _ (mem_biUnion.mpr ⟨f,mem_toRight.mpr v,g⟩)|inl f=> exact mem_union_left _ (mem_biUnion.mpr ⟨f,mem_toLeft.mpr v, (show chart Z T (Sum.inl f)=station Z f from if_pos (p.1 _ (mem_toLeft.mpr v))) ▸ g ⟩) -- `Eq.mp`; tune
private lemma envs {I1: Type*}(S:Finset I1)(F:I1→(∀ i,Φ i)→ℂ)(H:∀ i∈S,Envelope (F i)): Envelope (fun v=>(∏ i∈S, F i v)):=by
 induction S using Finset.induction_on with
 | empty=> simp_rw [prod_empty]; exact Law.fixedP _ 
 | insert i S l ih=> simp_rw [prod_insert l]; exact Law.prodP (H _ (mem_insert_self ..)) (ih (fun i h=> H i (mem_insert_of_mem h)))
abbrev buoy (P:Finset (Finset Y))(v:∀ i,Φ i) := ∏ Q∈ P,G Q v
def lance (P:Finset (Finset Y))(M:Finset I)(v:∀ i,Φ i) := buoy G P v * (∏ i∈ M,D (floor P) i v)
abbrev channel (P:Finset (Finset Y))(M:Finset I):= ∫ v,lance D G P M v ∂century μ ν (floor P)
def line (S:Finset (Finset Y⊕ I)) : ℂ:= if Fleet Z S.toLeft then channel D G μ ν S.toLeft S.toRight else 0
variable {D G Z T}(u:Cabin Z T D G)(h:∀ i,i∈ Z i)
namespace Cabin
include u
lemma sail {P:Finset (Seal Y)}(hp:Fleet Z P):Envelope (buoy G P):=envs P _ fun i v=> u.bill i (hp.1 i v) -- phantom lean
lemma sailsC{P:Finset (Seal Y)}(hp:Fleet Z P) (J: Finset I) : Envelope (lance D G P J):= Law.prodP (u.sail hp) (envs J _ fun i _=>u.meter _ _)
lemma know_boat {P:Finset (Seal Y)}(hp:Fleet Z P):ScopedB (buoy G P) (berth Z P):= ScopedB.prod P _ fun i l=>(u.extent _ (hp.1 _ l)).widen (subset_biUnion_of_mem _ l)
lemma knows {P:Finset (Seal Y)}(hp:Fleet Z P)(M:Finset I): ScopedB (lance D G P M) (lit Z T P M):=by
 refine ScopedB.mul ((u.know_boat hp).widen subset_union_left) (?_); apply ScopedB.prod; intro i v; refine (u.when (floor P) i).widen (union_subset ((subset_biUnion_of_mem T v).trans subset_union_right) ?_); intro j h; obtain ⟨k,t,g⟩:= mem_biUnion.mp h; exact mem_union_left _ (mem_biUnion.mpr ⟨k,hp.stays ▸ filter_subset _ _ t,g⟩)
private lemma soon {P Q:Finset (Seal Y)} {M N:Finset I}(hp:Fleet Z (P∪Q))(d:Disjoint (lit Z T P M) (lit Z T Q N)):∀ i∈M,D (floor (P∪Q)) i=D (floor P) i:=by
 intro i v; apply u.cond; exact hp.saw (d.symm.mono subset_union_left ((subset_biUnion_of_mem T v).trans subset_union_right))
lemma homeB {P Q:Finset (Seal Y)}{M N:Finset I}(p:Fleet Z P)(t:Fleet Z Q)(g:Disjoint (lit Z T P M) (lit Z T Q N))(e:Disjoint P Q)(E:Disjoint M N)(v:∀ i,Φ i): lance D G (P∪Q) (M∪N) v=lance D G P M v*lance D G Q N v:=by
 have he:=p.grow t (g.mono subset_union_left subset_union_left); have hp:=u.soon he g; have hx:=u.soon (show Fleet Z (Q∪P) from union_comm P Q ▸ he) g.symm; rw [union_comm Q P] at hx; unfold lance buoy; rw [prod_union e,prod_union E, Finset.prod_congr rfl (show ∀ i∈M,D (floor (P∪Q)) i v= _ from fun i p=> congrFun (hp i p) v),prod_congr rfl (show ∀ i∈N,D (floor (P∪Q)) i v=_ from fun i t=> congrFun (hx i t) v)]; ring
omit u in
lemma port {P:Finset (Seal Y)} (h:∀ i,i∈ Z i):floor P⊆ berth Z P:= by intro x p; obtain ⟨i,l,g⟩:= mem_biUnion.mp p; exact mem_biUnion.mpr ⟨i,l, pins _ h g⟩
include h
lemma harbor {P Q:Finset (Seal Y)}{M N:Finset I}(p:Fleet Z P)(t:Fleet Z Q)(g:Disjoint (lit Z T P M) (lit Z T Q N))(e:Disjoint P Q)(E:Disjoint M N): channel D G μ ν (P∪Q) (M∪N)=channel D G μ ν P M*channel D G μ ν Q N:=by
 have he:=u.homeB p t g e E; unfold channel; simp_rw [he]; rw [show floor (P∪Q)=floor P∪ floor Q from union_biUnion ..]; exact autumn μ ν _ _ ((port h).trans subset_union_left) ((port h).trans subset_union_left) (u.knows p _) (u.knows t _) g -- tune
lemma ship:Grows (chart Z T) (line Z D G μ ν):=by
 refine ⟨?_,fun P Q d v=>?_⟩; · unfold line; rw [if_pos (by simpa [toLeft] using (Fleet.empty (Z:=Z)))]; simp [channel,floor,lance,buoy,toLeft,toRight]
 unfold line; rw [toLeft_union,toRight_union]; by_cases p:Fleet Z P.toLeft; swap; · rw [if_neg p, if_neg (fun g : Fleet Z _ => p (g.subs subset_union_left)), zero_mul]
 by_cases q:Fleet Z Q.toLeft; swap; · rw [if_neg q, if_neg (fun g : Fleet Z _=> q (g.subs subset_union_right)),mul_zero]; -- tune toRight simp rw
 rw [←lit_u Z T P p, ←lit_u Z T Q q] at d; rw [if_pos p,if_pos q,if_pos (p.grow q (d.mono subset_union_left subset_union_left))]; exact u.harbor μ ν h p q d (disjoint_left.mpr fun _ a b=>disjoint_left.mp v (mem_toLeft.mp a) (mem_toLeft.mp b)) (disjoint_left.mpr fun _ a b=>disjoint_left.mp v (mem_toRight.mp a) (mem_toRight.mp b)) -- tune order
end Cabin
end YM.CF.BPress.Contour
