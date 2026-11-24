import YM.CF.BPress.Template
/-!
Time partitions used in all integration change-of-variables. N parity: ODD i. Gap belongs to i preceding it. Closed gap & band overlap at one endpoint, so horiz links may be seen by both. Define reserved sets expressly later. No coincident first/last gap even at period seam.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Sheet Finset
open scoped Topology BigOperators Classical Matrix
namespace Bands
variable {s : Side}{B:BandWidth} (X : Bands s B)
open Tunnel
def Dmark (i : X.Index) := Even i.val
lemma prev_next (i : X.Index): X.Dmark (i+1) ↔ ¬ X.Dmark i:=by
 simp only [Dmark,Nat.even_iff]; rw [RP.vnext]; split_ifs with h
 · rcases X.even with ⟨k,g⟩; omega
 omega
lemma next_prev (i : X.Index): X.Dmark (i-1) ↔ ¬ X.Dmark i:=by nth_rw 2 [← sub_add_cancel i 1]; rw [X.prev_next,not_not]
lemma next_ne (i : X.Index): i+1≠i:= fun v=> (iff_not_self  (a:= X.Dmark i) <| by nth_rw 1 [←v]; exact X.prev_next i) -- tune
lemma prev_ne (i : X.Index): i-1≠i:=fun v=> X.next_ne i (show i+1=i from (congrArg (·+1) v).symm.trans (sub_add_cancel ..))
@[simp] lemma mark_o (i : X.Index): (X.mark i).o=X.start i:= rfl
@[simp] lemma ditch_o (i : X.Index) : (X.ditch i).o=X.stop i:= rfl
@[simp] lemma mark_last (i : X.Index): (X.mark i).last=X.stop i:= rfl
@[simp] lemma ditch_last (i : X.Index): (X.ditch i).last=X.start (i+1):= X.stop_next i
@[simp] lemma mark_n (i : X.Index): (X.mark i).n=B.marked:=rfl
@[simp] lemma ditch_n (i : X.Index) : (X.ditch i).n.val=B.D:= rfl
@[simp] lemma mark_mem (i : X.Index): (X.mark i).mem=X.band i:= rfl
@[simp] lemma ditch_mem (i : X.Index): (X.ditch i).mem=X.gap i:=rfl
lemma mark_clock (i : X.Index){k:ℕ}(p:k<B.full.val): (X.mark i).rise k=X.clock (i,⟨k,p⟩):=(X.clock_eq i ⟨k,p⟩).symm
lemma ditch_clock (i : X.Index){k:ℕ}(p:k<B.D): (X.ditch i).rise k=X.clock (i,⟨B.marked.val+k, show B.marked.val+k<_ by rw [B.full_eq]; omega⟩):=by rw [X.clock_eq]; simp only [Tunnel.rise,ditch_o,stop,Nat.cast_add,add_assoc]
-- parity D covers through after ditch; proofs
lemma ditch_disjoint {i j : X.Index} (p : i ≠ j): Disjoint (X.gap i) (X.gap j) := by
 have he(i j : X.Index)(t : i≠j){k l:ℕ}(v:k<B.D)(g:l ≤ B.D): (X.ditch i).rise k ≠ (X.ditch j).rise l:=by
    rcases lt_or_eq_of_le g with g|g; intro e; rw [X.ditch_clock i v, X.ditch_clock j g] at e; exact t (congrArg Prod.fst (X.clock.injective e)); subst l; intro e; rw [X.ditch_clock i v, show (X.ditch j).rise B.D=_ from X.ditch_last j] at e -- tune
    rw [← X.mark_o (j+1), ← (X.mark (j+1)).rise_zero, X.mark_clock (j+1) B.full.property] at e; have hu:= congrArg (fun a=>a.2.val) (X.clock.injective e); change B.marked.val+k=0 at hu; have ht:0<B.marked.val:= B.marked.property; omega
 refine disjoint_left.mpr fun x h v=>?_; obtain ⟨k,h,e⟩:= (X.ditch i).internal x|>.mp h; obtain ⟨l,v,f⟩:= (X.ditch j).internal x|>.mp v; change k ≤ B.D at h; change l ≤ B.D at v; rcases lt_or_eq_of_le h with u|rfl -- tune
 · exact he _ _ p u v (e.symm.trans f)
 rcases lt_or_eq_of_le v with u|w; exact he _ _ p.symm u le_rfl (f.symm.trans e); have ht:X.start (i+1)=X.start (j+1):= (X.ditch_last i|>.symm).trans ((e.symm.trans f).trans (w ▸ X.ditch_last j)); apply p; apply add_right_cancel; apply congrArg Prod.fst (X.clock.injective (a₁:=(i+1,⟨0,B.full.property⟩)) (a₂:=(j+1,⟨0,B.full.property⟩)) ?_); simpa [clock_eq,ht]
lemma at_overlap {i j : X.Index}{x : Site s} (p : x∈ X.gap i): x∈ X.band j ↔ (i=j ∧ x 0=X.stop i) ∨ (j=i+1∧ x 0=X.start (i+1)) := by
 obtain ⟨k,h,f⟩:= (X.ditch i).internal x|>.mp p; rw [←mark_mem,(X.mark j).internal,f]; change k ≤ B.D at h
 constructor
 · rintro ⟨l,g,Q⟩; change l ≤ B.marked.val at g; rcases lt_or_eq_of_le h with h|t; rw [X.ditch_clock i h, X.mark_clock j (lt_of_le_of_lt g B.marked_lt)] at Q; obtain ⟨u,A⟩:= Prod.mk.inj (X.clock.injective Q); have v:= congrArg Fin.val A; change B.marked.val+k=l at v; exact Or.inl ⟨u,by rw [show k=0 by omega,Tunnel.rise_zero,X.ditch_o]⟩
   have ht : (X.ditch i).rise k=(X.mark (i+1)).rise 0:= by rw [t,rise_zero,X.mark_o]; exact X.ditch_last i
   apply Or.inr; rw [ht]; rw [ht, X.mark_clock (i+1) B.full.property,X.mark_clock j (lt_of_le_of_lt g B.marked_lt)] at Q; exact ⟨(congrArg Prod.fst (X.clock.injective Q)).symm,by simp⟩
 rintro (⟨rfl,k⟩|⟨rfl,k⟩); exact ⟨B.marked.val,le_rfl,k⟩; exact ⟨0,Nat.zero_le _,by rw [k]; simp⟩
lemma size (i : X.Index)(k:Fin B.full.val) : (X.mark i).rise k.val=X.clock (i,k):= X.mark_clock i k.isLt

-- all links contained in some mark or gap. Either horizontal (obvious) or vertical (include from last of previous, but not last before next).
lemma links_cover (k : Link s) : ∃ i : X.Index, k∈inside (X.band i) ∨ k∈inside (X.gap i):=by
 obtain ⟨⟨i,a,h⟩,e⟩:=X.clock.surjective (k.1 0); change X.clock (i,⟨a,h⟩)=_ at e; have he:=X.mark_clock i h; have hp:=B.full_eq; have hx (p:B.marked.val ≤ a) : k.1 0=(X.ditch i).rise (a-B.marked.val):= by rw [←e,X.ditch_clock i (by omega : a-B.marked.val<B.D)]; congr; exact Nat.add_sub_of_le p|>.symm -- tune
 refine ⟨i,?_⟩; rcases link_cases k with ⟨v,f⟩|f
 · rw [f]; rcases le_or_gt a B.marked.val with v'|v'; exact Or.inl ((X.mark i).tang_in _|>.mpr ⟨a,v',e.symm.trans he.symm⟩); exact Or.inr ((X.ditch i).tang_in _|>.mpr ⟨_, X.ditch_n i|>.symm ▸ (show a-B.marked.val≤ B.D by omega),hx v'.le⟩)
 rw [f]; rcases lt_or_ge a B.marked.val with v|v; exact Or.inl ((X.mark i).normal_in _|>.mpr ⟨a,v,e.symm.trans he.symm⟩); exact Or.inr ((X.ditch i).normal_in _|>.mpr ⟨_, X.ditch_n i|>.symm ▸ (show a-B.marked.val<B.D by omega),hx v⟩)
lemma link_overlap {i j : X.Index}{k : Link s} (p:k∈inside (X.gap i))(h:k∈inside (X.band j)): ∃ x, (i=j∧ k=fl (X.stop i) x) ∨ (j=i+1∧ k=fl (X.start (i+1)) x):=by
 have v(x)(g:x∈X.gap i)(w:x∈X.band j):=(X.at_overlap g).mp w; obtain ⟨a,b⟩:= inside_iff ..|>.mp p; obtain ⟨c,d⟩:= inside_iff ..|>.mp h; have he:= v _ a c; rcases link_cases k with ⟨x,h⟩|h; exact ⟨x,he.imp (fun e=>⟨e.1,h.trans (by rw [e.2])⟩) fun e=>⟨e.1,h.trans (by rw [e.2])⟩⟩
 exfalso; have hf:= v _ b d; rw [show k.2=0 from congrArg Prod.snd h] at hf; simp only [Pi.add_apply,step_apply, ite_true] at hf; have hs : k.1 0+1≠ k.1 0:= by
   intro e; have he : (1: Per s)=0:= add_eq_left.mp e; have hs:= (X.ditch i).room; have hx:1 < s.val:=by omega
   have he':=(ZMod.val_natCast_of_lt hx); simp only [Nat.cast_one] at he'; rw [he] at he'; simp at he'
 have hx:= X.next_ne i; rcases he with ⟨e,v⟩|⟨e,v⟩ <;> rcases hf with ⟨g,p⟩|⟨g,p⟩
 exact hs (p.trans v.symm); exact hx (g.symm.trans e.symm); exact hx (e.symm.trans g.symm); exact hs (p.trans v.symm)

/-- Actual chronology-independent D-face N-face of gap (dclas orientation bool could Nat Bool; use if Dmark). -/
def dirichlet (i:X.Index):=if X.Dmark i then i else i+1
def neumann (i:X.Index):= if X.Dmark i then i+1 else i
def depth (i:X.Index)(k:ℕ):=if X.Dmark i then (X.ditch i).rise k else (X.ditch i).fall k
lemma b_zero (i:X.Index): X.Dmark (X.dirichlet i)∧ ¬ X.Dmark (X.neumann i):=by by_cases h:X.Dmark i <;>simp [dirichlet,neumann,h,X.prev_next]
lemma depth_flip (i:X.Index){k:ℕ}(p:k ≤ B.D): ∃ a≤ B.D,(X.ditch i).rise k=X.depth i a :=by unfold depth; split; exact ⟨k,p,rfl⟩; refine ⟨B.D-k,Nat.sub_le ..,?_⟩; rw [Tunnel.fall,X.ditch_n,Nat.sub_sub_self p]
lemma depth_gap (i:X.Index){k:ℕ}(p:k ≤ B.D) (x:Tri s) : event (X.depth i k) x∈ X.gap i:=by rw [← X.ditch_mem]; unfold depth; split; exact (X.ditch _).rise_mem (X.ditch_n _|>.symm ▸ p) _; exact (X.ditch _).rise_mem (Nat.sub_le ..) _
lemma depth_zero (i:X.Index) : X.depth i 0=if X.Dmark i then X.stop i else X.start (i+1) := by split_ifs with h <;> simp [depth,h]
lemma depth_D (i:X.Index) : X.depth i B.D= if X.Dmark i then X.start (i+1) else X.stop i:=by unfold depth; split; exact X.ditch_last i; rw [Tunnel.fall,X.ditch_n,Nat.sub_self,rise_zero,ditch_o]
lemma depth_inj {i : X.Index}{a b:ℕ}(h:a≤ B.D)(v:b≤ B.D) (p:X.depth i a=X.depth i b): a=b:=by
 unfold depth at p; split at p; exact (X.ditch i).rise_inj (by rw [X.ditch_n]; omega) (by rw [X.ditch_n]; omega) p
 · have he (k) : (X.ditch i).n.val-k≤ (X.ditch i).n.val+1:=by omega
   have ht:=(X.ditch i).rise_inj (he a) (he b)  p; rw [X.ditch_n] at ht; omega
lemma guardD (i:X.Index) (x:Tri s) : event (X.depth i 0) x∈ X.band (X.dirichlet i):=by
 unfold dirichlet; rw [X.depth_zero]; split; exact (X.mark i).late x; exact (X.mark _).early x
lemma guardN (i:X.Index) (x:Tri s) : event (X.depth i B.D) x∈ X.band (X.neumann i):=by
 unfold neumann; rw [X.depth_D]; split; exact (X.mark _).early x; exact (X.mark _).late x

-- both arise in crown of adjoining band too
lemma crownD (i:X.Index)(x:FlatLink s): fl (X.depth i 0) x ∈ (X.mark (X.dirichlet i)).crown := (Tunnel.crown_mem ..).mpr ⟨x,by by_cases h:X.Dmark i<;> simp [X.depth_zero,h,Bands.dirichlet]⟩ -- def typo simp
lemma crownN (i:X.Index)(x:FlatLink s): fl (X.depth i B.D) x∈ (X.mark (X.neumann i)).crown := (Tunnel.crown_mem ..).mpr ⟨x,by by_cases h:X.Dmark i <;> simp [X.depth_D,h,Bands.neumann]⟩
end Bands
end YM.CF.BPress
