import YM.CF.BProof.Mark.ProofX
import YM.CF.BProof.Mapping.Posts
/-! Piece conventions: two closed strips for every gap. Endpoints truly in the Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s:Side}(Y:Yard s)
abbrev Ind := Y.Index
abbrev tag(x:Site s): Y.Index := Mapping.Posts.night Y (time x)
def BTime(x:Per s):=Y.Band (Y.twinsBand x) x
abbrev dark(x:Site s): Prop:= BTime Y (time x)
abbrev hr(x:Site s): Y.Index:=Y.twinsBand (time x)
lemma wide : 2*Y.long<s.val:=by have he:=Y.count_small; have p:=Y.long_lt; omega
lemma codeB {x:Site s}{i:Y.Index}(p:x∈ Y.band i): dark Y x ∧ hr Y x=i:=by have h:=Y.u_part i (time x) (mem_strip.mp p); exact ⟨show dark Y x from (by unfold dark BTime; rw [h]; exact mem_strip.mp p),h⟩
lemma code_tag(i:Y.Index)(x:Site s)(t:x∈ Y.band i): tag Y x=Y.location i (flag (Y.u i) (time x) Y.long):= Mapping.Posts.band Y i (time x) (mem_strip.mp t)
lemma code_gap {i:Y.Index}{x:Site s}(p:x∈Y.gap i): tag Y x=i:= Mapping.Posts.gap _ i (time x) (mem_strip.mp p)
lemma band_pick(x:Site s)(h:dark Y x):x∈Y.band (hr Y x):= mem_strip.mpr h
lemma gap_pick(x:Site s)(h:¬dark Y x): x∈Y.gap (tag Y x):=by
 rcases Y.edge_from (time x) with v|v; exact (h v.le).elim; let i:=hr Y x; have he: x∈Y.gap i:=mem_strip.mpr v.le; rw [code_gap ..]; exact he; exact he
lemma edge_pick (x:Site s)(i:Axis): (∃ j:Y.Index,x∈Y.band j∧x+step i∈Y.band j)∨ ∃ j:Y.Index,x∈Y.gap j∧x+step i∈Y.gap j:=by
 rcases Y.edge_from (time x) with v|v
 · refine .inl ⟨_,mem_strip.mpr v.le, mem_strip.mpr ?_⟩; rw [time_add,time_step]; split; rw [along_succ (by have := Y.lL; omega)]; exact v; rw [add_zero]; exact v.le -- tune
 refine .inr ⟨_,mem_strip.mpr v.le,mem_strip.mpr ?_⟩; rw [time_add,time_step]; split; rw [along_succ (by have :=Y.dD; omega)]; exact v; rw [add_zero]; exact v.le
lemma chip_vic {i:Y.Index}{x:Site s}{r:ℕ}(t:x∈ Y.band i)(h: chip (Y.u i) Y.long x≤r): Y.Vic (tag Y x) r (time x):=by
 let b:= time x; let k:= along (Y.u i) b; have hi:= Y.before_u i (mem_strip.mp (show x∈Y.band i from t)); rw [code_tag Y i x t]; unfold Yard.location; split
 · rename_i p; have he:= (flag_true ..).1 p; apply Y.cold_vic i r (time x) ⟨?_,mem_strip.mp t⟩; unfold cut at he; unfold chip at h; omega
 rename_i p; have he:= (flag_false ..).1 (Bool.eq_false_iff.mpr p); apply Y.hot_vic' i r (time x) ⟨?_,mem_strip.mp t⟩; unfold cut at he; unfold chip at h; omega
lemma meeting {i j:Y.Index}{x:Site s}(h:x∈Y.band i)(u:x∈ Y.gap j):chip (Y.u i) Y.long x=0:=by
 rcases Y.common i (time x) (mem_strip.mp h) (mem_strip.mp u) with h|h; rw [chip,h.1,along_self,_root_.min_eq_left (Nat.zero_le _)]; rw [chip,h.1,Y.u_in,Nat.sub_self,min_eq_right (Nat.zero_le _)]
lemma vic_chip {i j:Y.Index}{x:Site s}(h:x∈Y.band i){r:ℕ}(p:2*r<Y.long)(u:Y.Vic j r (time x)): chip (Y.u i) Y.long x≤r:=by
 rcases Y.vic_split _ _ _ p u with ⟨a,hp⟩|u|⟨a,hp⟩
 · have hv: i=j:= (codeB Y h).2.symm.trans (codeB Y (mem_strip.mpr hp)).2; subst j; have hz:=Y.before_u i hp; unfold chip; omega -- tune elaboration `mem_strip`
 · rw [meeting Y h (mem_strip.mpr u)]; omega
 have hv: i=j+1:=(codeB Y h).2.symm.trans (codeB Y (mem_strip.mpr hp)).2; subst i; unfold chip; omega
lemma immediate (x:Site s)(i:Axis) : separation x (x+step i) ≤1:=by rw [←Way,←slide4]; exact Grid.near_slide ..
lemma along_t (x y:Site s)(i:Y.Index){r t:ℕ}(p:Y.Vic i r (time x))(h:separation x y≤ t): Y.Vic i (r+t) (time y):= Y.vic_trans i _ _ (time y) _ p ((Yard.time_jump x y).trans h)
lemma rlink {x y:Site s}{r t:ℕ}(h:separation x y≤t)(v:2*(r+t)+1 < Y.long)(p:Y.Vic (tag Y x) r (time x)): tag Y y=tag Y x:= Mapping.Posts.vic Y _ _ v (along_t Y x y _ p h)

def dial (i:Y.Index)(x:Site s):ℝ:= (Y.depth i (time x):ℝ)/Y.short
lemma dial_mem {i:Y.Index}{x:Site s}(p:x∈Y.gap i): dial Y i x∈ Zone:= ⟨by unfold dial; positivity,(div_le_iff₀ (Nat.cast_pos.mpr Y.short_pos)).2 (by rw [one_mul]; exact Nat.cast_le.mpr (Y.depth_le i (time x) (mem_strip.mp p)))⟩
lemma dial_step (i:Y.Index)(x:Site s)(v:Axis)(hx:x∈Y.gap i)(t:x+step v∈Y.gap i): |dial Y i (x+step v)-dial Y i x|≤1/Y.short:=by
 let a:=Y.v i; let l:=Y.short; let e:=time x; have ht:0<(Y.short:ℝ):=Nat.cast_pos.mpr Y.short_pos
 have he := mem_strip.mp (show x∈ Y.gap i from hx); have hh:= mem_strip.mp (show x+step v∈ Y.gap i from t)
 unfold dial; rw [time_add, time_step]; rw [time_add,time_step] at hh; by_cases h:v=0; swap; · rw [if_neg h,add_zero,sub_self,abs_zero]; positivity
 rw [if_pos h] at *; rw [← sub_div,abs_div,abs_of_pos ht]; apply div_le_div_of_nonneg_right _ ht.le; unfold Yard.depth Yard.v; split
 · rw [along_succ (by have :=Y.dD; omega),Nat.cast_add_one,add_sub_cancel_left]; simp
 rw [along_succ (by have :=Y.dD; omega)]; rw [along_succ (by have :=Y.dD; omega)] at hh; rw [Nat.cast_sub hh,Nat.cast_sub he,Nat.cast_add_one]; rw [abs_le]; constructor <;> linarith
lemma finishD (i j:Y.Index)(x:Site s)(t:x∈ Y.band i)(e:x∈Y.gap j): dial Y j x= if Y.D i then 0 else 1:=by
 have hl:= Y.short_pos
 rcases Y.common _ _ (mem_strip.mp (show x∈ Y.band i from t)) (mem_strip.mp (show x∈ Y.gap j from e)) with ⟨h,hp⟩|⟨h,hp⟩
 · subst i; rw [dial,h,Yard.depth,Y.v_in j]; by_cases p:Y.D j <;> simp [Y.next j,p,Nat.ne_of_gt hl]
 subst j; rw [dial,h,Yard.depth,along_self]; by_cases p:Y.D i <;> simp [p,Nat.ne_of_gt hl]
end YM.CF.BProof.Trek
