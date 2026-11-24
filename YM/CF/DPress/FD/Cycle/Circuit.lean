import YM.CF.DPress.FD.Cycle.Apart
import Mathlib.Dynamics.PeriodicPts.Lemmas
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD.Cycle
open List Filter Set
open scoped Topology BigOperators ENNReal Classical
open Function
abbrev Coil(I:Type*):= _root_.Cycle I
variable {I J:Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] (S:Equiv.Perm I)
lemma spin_of_append {β:Type*}{f: List I→β}(t:∀ a b:List I,f (a++b)=f (b++a)){x y:List I}(p:x ~r y) : f x=f y:=by obtain ⟨v,h,rfl⟩:= List.isRotated_iff_mod.mp p; rw [List.rotate_eq_drop_append_take h,←t,List.take_append_drop] -- names
section
variable (P: I→Finset C)(f:I→C) (A:Coil I)
def worth (A:Coil I)(P:I→Finset C):ℝ:= Quot.liftOn A (fun x=>evalP P x θ) fun _ _ e=>spin_of_append (f:=fun x:List I=> evalP P x θ) (rotH P) e
def coilW (A:Coil I)(f:I→C):ℝ:= Quot.liftOn A (fun x:List I=>θ (x.map f)) fun _ _ e=> spin_of_append (f:=θ) (θsym) (List.IsRotated.map e f)
lemma worth_C{a:List I}(p:(a:Coil I)=A):evalP P a θ=worth A P:=by subst A; rfl
lemma coilW_C{a:List I}(p:(a:Coil I)=A): θ (a.map f)=coilW A f:=by subst A; rfl
lemma chain_lineB {p:I→I→Prop}(g:A.Chain p){a:List I}(e:(a:Coil I)=A):List.IsChain p a:=by
 subst A; rcases a with -|⟨x,y⟩; simp; have ht:= _root_.Cycle.chain_ne_nil p (List.cons_ne_nil x y); exact List.IsChain.tail (ht.mp g)
end
variable (i j:I)
abbrev visit (i:I):= periodicOrbit S i
abbrev view (i:I) := (List.range (minimalPeriod S i)).map fun j=> S^[j] i
lemma live: i∈ visit S i:= self_mem_periodicOrbit (S.injective.mem_periodicPts i)
lemma vote: visit S i = (view S i:Coil I):= rfl
lemma viewP: (view S i).Nodup:= nodup_periodicOrbit
lemma εnice : 0<minimalPeriod S i:= minimalPeriod_pos_of_mem_periodicPts (S.injective.mem_periodicPts i)
lemma hefty (p:S i ≠ i) :(visit S i).length>1:=by
 have he:minimalPeriod S i≠1:=fun H=> p (minimalPeriod_eq_one_iff_isFixedPt.mp H); rw [periodicOrbit_length]; have h:= εnice S i; omega
lemma hold : j∈ visit S i ↔ visit S j=visit S i:=by
 constructor; swap; · intro h; rw [←h]; exact live ..
 rw [mem_periodicOrbit_iff (S.injective.mem_periodicPts i)]; rintro ⟨t,rfl⟩; exact periodicOrbit_apply_iterate_eq (S.injective.mem_periodicPts i) t
abbrev loops(S:Equiv.Perm I) : Finset (Coil I):= Finset.univ.image (visit S)
lemma lands : visit S i∈ loops S:= Finset.mem_image_of_mem _ (Finset.mem_univ i)
abbrev cave(Q:Coil I):Finset I:=Q.toFinset
lemma patron {i:I}{Q: Coil I}(g:Q∈loops S):i∈ cave Q ↔ visit S i=Q:=by obtain ⟨j,h,rfl⟩:= Finset.mem_image.mp g; unfold cave; rw [vote S j, _root_.Cycle.coe_toFinset, List.mem_toFinset,←vote S j]; exact hold .. -- vote turn
lemma pairwise {A B:Coil I}(e:A∈loops S)(v:B∈loops S)(g:A≠B):Disjoint (cave A) (cave B):= Finset.disjoint_left.mpr fun j a b=>g (((patron S e).1 a).symm.trans ((patron S v).1 b))
-- transformation under permuting the site sets.
variable (G:Equiv.Perm J)(h:I≃J)(t:∀ i:I,h (S i)=G (h i))
include t
lemma lookτ (i:I): view G (h i)=(view S i).map h:=by
 have he: Semiconj h S G:=t; have hk: minimalPeriod S i=minimalPeriod G (h i):= by
    apply minimalPeriod_eq_minimalPeriod_iff.mpr; intro n; change S^[n] i=i ↔ G^[n] (h i)=h i; rw [← (he.iterate_right n i)]; exact h.injective.eq_iff.symm
 unfold view; rw [List.map_map,hk]; exact congrArg (fun z:ℕ→J=> (List.range _).map z) (funext fun j=>(he.iterate_right j i).symm)
lemma beamτ (i:I): visit G (h i)=(visit S i).map h:=by rw [vote,vote,lookτ S G h t]; rfl
end YM.CF.DPress.FD.Cycle
