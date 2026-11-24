import YM.CF.DPress.FD.Stock.Pear
import YM.CF.DPress.FD.Law.Skew
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Spire Skye Cash Deck MeasureTheory SU Lat Finset Wilson Laurent
open Cube (More Guard)
open scoped Topology BigOperators ENNReal NNReal Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{I:Type}[Fintype I]{r d:ℕ}{u t:ℝ}
namespace Gear
abbrev Wheel(n:Side):= Support (More n)
abbrev listS (M:Wheel n)(d:ℕ) :Finset (Wheel n):=(univ.image (soup M d)).filter (Finset.Nonempty)
abbrev W(M:Wheel n)(d:ℕ):= ↥(listS M d)
variable {M: Wheel n} {e e':reach n}
lemma list_x(S:Wheel n) : S∈ listS M d ↔ S.Nonempty∧ ∃ e:reach n, soup M d e=S:=by simp [listS,and_comm]
lemma rawS(S:W M d):S.val.Nonempty∧∃ e:reach n,soup M d e=S.val:= (list_x ..).1 S.property
lemma recept(p:(soup M d e).Nonempty):soup M d e∈ listS M d:= (list_x ..).2 ⟨p,e,rfl⟩
-- soup is whole component. all flag vertices reachable from keys connected to each other at same win. Separation use 2*r+20 on components.
lemma legs_v{x y:Seat n}(h:legs M d x y):legs M d y x:=⟨h.2.1,h.1,(separation_comm ..).trans_le h.2.2⟩
lemma Cnear{x y:Seat n}(p:x∈ ends e)(u:y∈ends e):separation x y ≤1:=by
 rcases mem_insert.mp p with p|p<;> rcases mem_insert.mp u with u|u
 · simp only [p,u,separation_self]; exact Nat.zero_le _
 · rw [p,mem_singleton.mp u]; exact Work.E01.sep_step_le ..
 · rw [u,mem_singleton.mp p,separation_comm]; exact Work.E01.sep_step_le ..
 rw [mem_singleton.mp p,mem_singleton.mp u,separation_self]; omega
lemma meet{id η:Seat n} (q:id∈Cake M d e)(p:η∈Cake M d e) :legs M d id η:=by
 obtain ⟨x,v,h⟩:=(mem_filter.mp q).2; obtain ⟨y,t,r⟩:=(mem_filter.mp p).2; refine ⟨(mem_filter.mp q).1,(mem_filter.mp p).1,?_⟩; have he:=Cnear v t; rw [separation_comm x id] at h; have ht:=separation_triangle x y η; exact (separation_triangle id x η).trans (by omega)
lemma lane_to{x y: Seat n} (p:x∈ soup M d e)(t:y∈soup M d e): Relation.ReflTransGen (legs M d) x y:=by
 obtain ⟨a,t,x⟩:=(mem_filter.mp t).2; obtain ⟨b,z,y⟩:=(mem_filter.mp p).2; apply Relation.ReflTransGen.trans _ (Relation.ReflTransGen.head (meet z t) x); letI : Std.Symm (legs M d) := ⟨fun _ _ v=> legs_v v⟩; exact symm y -- shadows names x,y; check function
lemma arrive{x y:Seat n}(p:x∈soup M d e)(h:y∈ M)(t:Relation.ReflTransGen (legs M d) x y): y∈soup M d e:=by obtain ⟨z,r,g⟩:=(mem_filter.mp p).2; exact mem_filter.mpr ⟨h,z,r,g.trans t⟩
lemma meet_se{x y:Seat n}(v:x∈ soup M d e)(q:y∈soup M d e')(p:separation x y ≤ 2*d+20):soup M d e=soup M d e':=by
 have he:legs M d x y:=⟨(mem_filter.mp v).1,(mem_filter.mp q).1,p⟩; have hl(y:Seat n)(t:y=y):True:=trivial; apply Finset.Subset.antisymm
 · intro i p; exact arrive q (mem_filter.mp p).1 (Relation.ReflTransGen.head (legs_v he) (lane_to v p))
 intro i p; exact arrive v (mem_filter.mp p).1 (Relation.ReflTransGen.head he (lane_to q p))
lemma meet_P{x y:Seat n}{S T:W M d} (p:S ≠ T) (s:x∈ S.val)(t:y∈ T.val): 2*d+20 < separation x y:=lt_of_not_ge (fun k=> by obtain ⟨e,v⟩:=(rawS S).2; obtain ⟨f,z⟩:=(rawS T).2; exact p (Subtype.ext (v.symm.trans ((meet_se (v.symm ▸ s) (z.symm ▸ t) k).trans z))))
lemma disjointΦ {S T:W M d}(p:S≠T):Meeting (BasicIid.P2 (Seat n)) S.val T.val :=fun i x j y v=> by have hx:=meet_P p x y; rw [v,separation_self] at hx; omega
-- $δ wind shells
abbrev Quire(S:Wheel n)(r:ℕ):= halo (2*r+1) S
lemma loft {S T:W M d}(p:S≠T)(h:100*r ≤ d): Meeting (fun i j=> r< separation i j) (Quire S.val r) (Quire T.val r):= by
 intro i t j v; obtain ⟨x,p',hx⟩:=halo_spec.mp t; obtain ⟨y,h',hy⟩:=halo_spec.mp v; by_contra! z; have hg:= meet_P p p' h'; rw [separation_comm y j] at hy; have ht:=separation_triangle i j y; have he:=separation_triangle x i y; omega
lemma worth(T:W M d) (p:¬Disjoint M (win r e)) (t:r≤d) (k:soup M d e=T.val):win r e⊆Quire T.val r:=by
 obtain ⟨x,h⟩:= Finset.not_disjoint_iff_nonempty_inter.mp p; obtain ⟨h,v⟩:= Finset.mem_inter.mp h
 have he:x∈T.val:=by rw [← k]; apply soup_p; rw [cake_p]; exact mem_inter.mpr ⟨h,Turf.windowP t (Finset.Subset.refl _) v⟩
 intro j z; obtain ⟨i,t,l⟩:=halo_spec.mp v; obtain ⟨y,u,w⟩:=halo_spec.mp z; rw [separation_comm i x] at l; have hp:= Cnear t u; have ht:=separation_triangle x i y; exact halo_spec.mpr ⟨x,he,(separation_triangle x y j).trans (by omega)⟩
end Gear
end YM.CF.DPress.FD
