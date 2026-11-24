import YM.CF.BPress.Lily.Petal
/-! § VolumeB-phase eq:B-Jrep. Letters of species one. Explicit row convention and site localization, not diagonal approximation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Lily
open Function MeasureTheory Filter NormedSpace Finset Fock Lattice Cube Lat Spin Spin.Paint SU SU.Pair Chalk Pf Pressure Branch Bias Dial Nacre Tulip
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{C: Op I}
open Submodule
-- ket symbol.Let's permit all modes; seeded coincidence. Lower list asc ⇒ CHosen word uses DESC order on bra. record reversal identity.
variable (T:Finset I){i j:I} (L:I→FC I) {x:Wave I}
structure Course (T:Finset I)(L:I→ FC I)(x:Wave I):Prop where
 vow(i:I)(p:i∈T): acts (L i) x=0
 twin(i:I)(t:i∈T)(j:I)(p:j∈T):antiB (L i) (L j)=0
 car(i:I)(p:i∈T)(j:I)(u:j∈T):antiB (L i) (star (L j))=if i=j then 1 else 0

-- list of inc asc creators. natural slot integrality
abbrev filament (t:List I):=(t.map (star ∘ L)).prod
abbrev winged (L:I→ FC I)(v:Wave I)(t:List I):= acts (filament L t) v
lemma oddity (t:List I): (t.reverse.map L).prod=star (filament L t):=by induction t with|nil=>simp [filament]|cons a t h=> unfold filament at *; simp [h,List.prod_append,-List.map_reverse]
variable {T L}{l k:List I}
abbrev helmet (L:I→FC I)(i:I):= star (L i)*L i
namespace Course
variable (F:Course T L x)
include F
lemma γ {i:I}(p:i∈ T): L i*L i=0:=by ext; exact add_self_eq_zero.mp (Matrix.ext_iff.mpr (F.twin _ p _ p) _ _)
lemma filled (i)(p:i∈T): helmet L i+ L i*star (L i)=1:= by rw [add_comm]; exact (F.car i p i p).trans (if_pos rfl)
lemma helmComm (p:i∈ T)(h:j∈T)(v:i≠j) : Commute (helmet L i) (star (L j)):=by
 have he:L j* L i= -(L i*L j):= eq_neg_of_add_eq_zero_left (F.twin j h i p); have hh:star (L i)*star (L j)= -(star (L j)*star (L i)):=by rw [←star_mul,he,star_neg,star_mul]
 unfold Commute SemiconjBy helmet; rw [mul_assoc, eq_neg_of_add_eq_zero_left ((F.car i p j h).trans (if_neg v)), mul_neg,←mul_assoc, hh, neg_mul, neg_neg,mul_assoc] -- tune
lemma occupied (p:i∈T): helmet L i * star (L i)=star (L i):=by
 unfold helmet; rw [mul_assoc,eq_sub_of_add_eq' (F.filled i p),mul_sub,mul_one, helmet, ←mul_assoc,←star_mul,F.γ p]; simp -- tune name eq_add...
lemma fulfill (h:l.toFinset⊆T)(p:i∈T) : acts (helmet L i) (winged L x l)= if i∈l then winged L x l else 0:=by
 induction l with| nil=> simp [winged,helmet,filament,act_mul,F.vow i p] | cons j t ih=>
   have hv:t.toFinset⊆T:=fun x a=> h (by simp [List.mem_toFinset.mp a]); have hp:j∈T:=h (by simp); rw [show winged L x (j::t)=acts (star (L j)) (winged L x t) from act_mul ..,← act_mul]; by_cases v:i=j; · subst j; rw [if_pos (List.mem_cons_self ..),F.occupied p]
   rw [(F.helmComm p hp v).eq,act_mul, ih hv]; by_cases h:i∈t <;> simp [h,v]
lemma same_norm (p:l.toFinset ⊆ T)(h: l.Nodup) : inner ℂ (winged L x l) (winged L x l)=inner ℂ x x:=by
 induction l with
 | nil=>simp [winged,filament]
 | cons a l ih=>
   have he:l.toFinset⊆T:= by simpa only [List.toFinset_cons,insert_subset_iff] using And.right (show a∈T∧l.toFinset⊆T from by simpa only [List.toFinset_cons,insert_subset_iff] using p) -- excess
   have hx:a∈T:=p (by simp); let t:=star (L a); let y:=winged L x l; rw [show winged L x (a::l)= acts t y from act_mul ..]; unfold t; rw [act_inner,← act_mul,eq_sub_of_add_eq' (F.filled a hx), act_sub, act_one, F.fulfill he hx, if_neg (List.nodup_cons.mp h).1, sub_zero]; exact ih he (List.nodup_cons.mp h).2
lemma off {l₁ l₂:List I}(p:l₁.toFinset⊆ T)(q:l₂.toFinset⊆ T)(h:i∈l₁)(u:i∉l₂): inner ℂ (winged L x l₁) (winged L x l₂)=0:=by
 have he:= p (List.mem_toFinset.mpr h); nth_rw 1 [← (F.fulfill p he|>.trans (if_pos h))]; have ht:= act_inner (helmet L i) (winged L x l₁) (winged L x l₂); rw [ (show IsSelfAdjoint (helmet L i) from IsSelfAdjoint.star_mul_self _),F.fulfill q he,if_neg u] at ht; rw [ht]; simp -- tune
abbrev stem (T:Finset I):=↥(T.powerset)
abbrev string (Y:stem T):= Y.val.sort
abbrev seaH (x:Wave I)(Y:stem T):=winged L x (string Y) -- L implicit maybe want explicit
lemma frame (Y Z:stem T) :inner ℂ (seaH (L:=L) x Y) (seaH (L:=L) x Z)= if Y=Z then inner ℂ x x else 0:=by
 have he(y:stem T):(string y).toFinset=y.val:=(by simp [string]); have ht(y:stem T): (string y).toFinset⊆ T:= he y|>.symm ▸ mem_powerset.mp y.property; have hf(y z:stem T) (p:¬ y.val ⊆ z.val): inner ℂ (seaH (L:=L) x y) (seaH (L:=L) x z)=0 := by
    obtain ⟨a,p,b⟩:= not_subset.mp p; exact F.off (ht y) (ht z) (by simpa [string] using p) (by simpa [string] using b)
 by_cases h:Y=Z; · subst Z; rw [if_pos rfl]; exact F.same_norm (ht Y) (sort_nodup ..)
 rw [if_neg h]; by_cases e:Y.val⊆Z.val; swap; exact hf _ _ e; exact inner_eq_zero_symm.mp (hf Z Y (fun b=>h (Subtype.ext (Subset.antisymm e b))))
end Course
end YM.CF.BPress.Lily
