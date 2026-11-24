import YM.CF.BPress.Wealth.Canon
import YM.CF.BPress.Wealth.Festival
/-! Mixed radix temporal & tangent. Positive half ties to *earlier gap*. Memory coordinate on Lambda. Head geometry independent priors. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth
open scoped Topology BigOperators Classical Matrix
variable {s L Q : Side}
-- primitive steps both ways around peculiar origin. Even at radius equal stride.
section radial
open Radix
variable (X:s.val=L.val*Q.val)(o:Per s)
-- Calendar port separate proof-irrelevance of clocks
abbrev idx (x:Per s) := ((clock s L Q X o).symm x).1
abbrev innerV (x:Per s) := ((clock s L Q X o).symm x).2
@[simp] lemma idx_at (i:Per Q)(k:Fin L.val) : idx X o (clock s L Q X o (i,k))=i:= congrArg Prod.fst (Equiv.symm_apply_apply ..)
lemma dial_length (i:Per Q)(j k:ℕ) : dial s L Q o i (j+k) = dial s L Q o i j + k:=by unfold dial; push_cast; abel
include X in
lemma dial_reel (i:Per Q)(k:ℕ) : dial s L Q o (i+1) k=dial s L Q o i (L.val+k):=by rw [dial_length,dial_edge s L Q X]; unfold dial; push_cast; abel -- tune include X
lemma rad_ft (i:Per Q)(p:ℕ)(h:p<L.val) : idx X o (dial s L Q o i p)=i:= idx_at X o i ⟨p,h⟩
lemma rad_reel (i:Per Q)(k:ℕ)(h:k<L.val): idx X o (dial s L Q o i (L.val+k))=i+1:= by rw [←dial_reel X, rad_ft X o _ k h]
lemma rad_tail (x:Per s)(k:ℕ)(p:k ≤ L.val): idx X o (x+k)=idx X o x ∨ idx X o (x+k)= idx X o x+1:=by
 obtain ⟨⟨i,a⟩,rfl⟩:= (clock s L Q X o).surjective x; rw [idx_at]; change idx X o (dial s L Q o i a.val + _) = _ ∨ _; have ht:= dial_length (L:=L) o i a.val k; change _ ∨ idx X o (dial s L Q o i a.val+_) = _; rw [← ht]; by_cases p': a.val+k<L.val; · exact Or.inl (rad_ft _ _ _ _ p')
 right; set Z:= a.val + k; obtain ⟨j,h⟩:=Nat.exists_eq_add_of_le (show L.val≤ Z from Nat.le_of_not_gt p'); have hx:=a.isLt; rw [h]; refine rad_reel X o i j (by unfold Z at h; omega)
lemma rad_dist_of (x y: Per s)(h:delta1 s x y ≤ L.val): (∃ k:ℕ, k ≤ L.val ∧ x=y+ ↑k) ∨ ∃ k:ℕ, k ≤ L.val ∧ y=x+ ↑k:=by
 obtain ⟨a,p,t⟩:= step_exists _ _ _ h; rcases le_or_gt 0 a with v|v; · exact Or.inl ⟨a.toNat,by omega,by rw [t]; congr; exact Eq.symm (by rw [← Int.cast_natCast (R:=Per s) a.toNat,Int.toNat_of_nonneg v])⟩ -- tune
 let k:=(-a).toNat; have he: ↑k=(-a:ℤ):= Int.toNat_of_nonneg (by omega); have hv:(a:Per s)=-k:=by rw [← Int.cast_natCast (R:= Per s) k,he]; push_cast; simp
 refine Or.inr ⟨k,by omega,by rw [t,hv,add_assoc]; simp⟩
lemma radial (x y:Per s)(h:delta1 s x y ≤ L.val): delta1 Q (idx X o x) (idx X o y)≤1:=by
 have he(a b:Per s)(k:ℕ)(h:k≤ L.val)(v:b=a+ ↑k): delta1 Q (idx X o b) (idx X o a)≤1:= by
   rcases rad_tail X o a k h with t|t; · rw [v,t,d_id]; omega
   rw [v,t]; simpa using delta_nat (idx X o a) 1
 rcases rad_dist_of x y h with ⟨k,p,v⟩|⟨k,p,v⟩; exact he y x k p v; exact (d_sym ..).le.trans (he x y k p v)
end radial
variable {b:BandWidth}(X:Bands s b)
-- start after center cut in *band i*. half of band i associated to gap i-1 through cut incl. `morning` starts time cofactor idx i=0.
def daybreak (b:BandWidth):= b.marked.val/2+1
def amark := (b.collar:Per s)+ ↑(daybreak b)
def moment (t:Per s) := idx X.size_eq (amark (b:=b) (s:=s)) t
def panel (p:Site s) : X.Hcols:= (moment X (p 0), Fin.tail p)
open Radix
@[simp] lemma am_event (t:Per s)(x:Tri s): panel X (event t x)=(moment X t,x):=Prod.ext (by simp [panel]) (by simp [panel,event])
lemma at_mark (i:X.Index)(k:ℕ): dial s b.full X.Q (amark (b:=b)) i k=(X.mark i).rise (daybreak b+k):=by unfold dial amark; change _= ((↑(b.full.val*i.val):Per s)+b.collar)+ _; push_cast; abel
lemma dawn_between (i:X.Index)(k:ℕ): (X.mark (i+1)).rise k= (X.mark i).rise (b.full.val+k):=by unfold Tunnel.rise; rw [X.mark_o,X.mark_o,←X.stop_next]; nth_rw 1 [Bands.stop]; rw [b.full_eq]; push_cast; abel
lemma dawn_paid (i:X.Index)(a:ℕ)(p:a<b.full.val): moment X ((X.mark i).rise (daybreak b+a))=i:= by rw [← at_mark]; exact rad_ft X.size_eq _ _ _ p
lemma sunrise (b:BandWidth): daybreak b ≤ b.marked.val:= by have he:0<b.marked.val:=b.marked.property; unfold daybreak; omega
lemma time_ride (i:X.Index)(k:ℕ)(p:k < daybreak b) : moment X ((X.mark i).rise k)= i-1:=by
 have he:= (daybreak b+k-k); -- tune
 let z:= b.full.val+k-daybreak b; have h:= (sunrise b).trans b.marked_lt.le; nth_rw 1 [← sub_add_cancel i 1]; rw [dawn_between]; rw [show b.full.val+k=daybreak b+z by unfold z; omega]; exact dawn_paid X (i-1) z (by unfold z; omega)
lemma time_blk (i:X.Index)(k:ℕ)(p: daybreak b≤ k)(e:k≤b.full.val) : moment X ((X.mark i).rise k)=i:=by nth_rw 1 [show k=daybreak b+(k-daybreak b) by omega]; apply dawn_paid; have he: 0<daybreak b:=Nat.succ_pos _; omega
lemma ditch_ride (i:X.Index)(t:Per s)(v:footTime X t i): moment X t=i:=by
 obtain ⟨k,h,rfl⟩:=v; rw [show (X.ditch i).rise k= (X.mark i).rise (b.marked.val+k) from (by unfold Tunnel.rise; rw [ditch_o,mark_o]; unfold Bands.stop; push_cast; abel)]; apply time_blk; all_goals first|exact (sunrise _).trans (Nat.le_add_right ..)| rw [b.full_eq]; omega
lemma collar_ride {i:X.Index}{k:ℕ}{t:Per s}(p:ZoneNear X i k t)(h:k≤cloak b) : moment X t=i:=by
 have he:= h.trans (by unfold cloak; exact Nat.div_le_self ..); -- tune infer
 have ht:0< b.marked.val:= b.marked.property; have hw:2*k< b.marked.val:=by unfold cloak at h; omega
 rcases photo_collar X i hw p with p|⟨k,q,u,rfl⟩|⟨k,q,u,rfl⟩; · exact ditch_ride X i t p
 · unfold Tunnel.fall; apply time_blk; · change daybreak b ≤ b.marked.val-k; unfold daybreak; unfold cloak at h; omega
   exact (show b.marked.val-k ≤ _ from Nat.sub_le ..).trans b.marked_lt.le
 rw [time_ride]; simp; unfold daybreak; unfold cloak at h; omega
lemma band_time (i:X.Index){k:ℕ}(p:k ≤ (X.mark i).n.val): moment X ((X.mark i).rise k)= if k ≤ (X.mark i).cut then i-1 else i:=by
 split; next h=> exact time_ride X i k (Nat.lt_succ_iff.mpr h )
 next h=> exact time_blk X i k (Nat.gt_of_not_le h) (p.trans b.marked_lt.le)
end YM.CF.BPress.Locale
