import YM.CF.BProof.Charge.Drought

/-! The Heavy supports and gap index. We always charge a vertical plaquette including
boundary data solely at its horizontal column position. Other heavy plaquettes and
kept roots pay 3M_I in tangent columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Form Angular Angular.Yard AnalyticBridge.SectorAffine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side} (Y:Yard s)(M:ℕ)(i:Y.Index)(l:Tile s)

abbrev pilot (l:Tile s):= Sum.elim Prod.fst Lam.center l
abbrev Stove := ¬ coldG Y M l
def touch := Sum.elim RG.touched (fun a=> pulley a M) l
lemma pivot : pilot l∈touch M l:= by cases l; exact four_self _; apply halo_subset _ _ (mem_singleton_self _)
lemma bounded {p:Site s}(h:p∈touch M l): separation (pilot l) p≤ M+2 := by
 cases l; exact le_trans (E01.sep_touched _ _ h) (by omega); rename_i a; simpa [touch,pulley,halo_spec] using h
lemma hotFire (h: Stove Y M l) : ∃ i:Y.Index,Y.Vic i (4*M) (time (pilot l)):=by
 cases l with
 | inl l => obtain ⟨b,p⟩:= unmark_center Y l h; exact ⟨b,Y.outside_gap b _ _ p⟩
 | inr l => change ¬ (∀ i:Y.Index,¬_) at h; simpa using h

def blame := if h: Stove Y M l then (hotFire Y M l h).choose else 0
lemma blamed (h:Stove Y M l): Y.Vic (blame Y M l) (4*M) (time (pilot l)):= by unfold blame; rw [dif_pos h]; exact (hotFire Y M l h).choose_spec
structure Room : Prop where
 range : 4*(5*M+3)+4≤Y.long
 seed : 2≤M
variable {M} -- arguments maybe adjust?
variable (p:Room Y M)(h: Stove Y M l)
include h
lemma warm_touch (x:Site s)(v:x∈touch M l): Y.Vic (blame Y M l) (5*M+2) (time x):=by
 have hh:= bounded M l v; exact (show 4*M+(M+2)=5*M+2 by omega) ▸ Y.vic_halo _ _ (blamed Y _ l h) (halo_spec.mpr ⟨_,mem_singleton_self _,hh⟩)
include p
abbrev close (b d: Y.Col)(k:ℕ):Prop:= b.1=d.1 ∧ Grid.dist b.2 d.2≤k
abbrev Lens := (blame Y M l,space (pilot l))
lemma near_touch (b:Bond s)(t:Form.Wet (touch M l) b)(d:Y.Door)(g:Y.heir b=some d): close Y (Lens Y l (M:=M)) d.1 (3*M):=by -- taylorwet replace
 rcases whichBond b with ⟨x,k,rfl⟩|⟨x,k,j,rfl⟩; · rw [heir_v] at g; contradiction
 rw [heir_h] at g; obtain ⟨hp,hq⟩:=t; change join x k∈touch M l at hp; have he:= warm_touch Y l h (join x k) hp
 rw [time_join] at he; rw [Y.locate (blame Y M l) x k j he (by have :=p.range; omega) g]
 have hi : Grid.dist (space (pilot l)) k ≤ M+2:= by
    rw [← space_join x k]; apply Grid.dist_le.mpr; exact fun i=> le_trans (show Cube.delta1 s _ _≤separation (pilot l) (join x k) from component_le (pilot l-join x k) i.succ) (bounded _ _ hp)
 exact ⟨rfl,hi.trans (by have :=p.seed; omega)⟩
omit p h in
lemma ripe (b:Y.Door): ¬ coldG Y M (.inl (Y.rise b)) := Y.birth b -- include parameters remove (l)
lemma recognize (b:Y.Door) (he:l=.inl (Y.rise b)): Lens Y l (M:=M)=b.1:=by
 subst l; have hg:time (pilot (Sum.inl (Y.rise b)))=Y.dawn b.1.1 b.2.1:=rfl; apply Prod.ext; swap; exact space_join (Y.dawn b.1.1 b.2.1) b.1.2
 apply Y.vic_unique _ _ (time (pilot (.inl (Y.rise b)))) (by have :=p.range; omega) (blamed _ _ _ h) (Y.outside_gap _ _ _ ((Y.dawn_open ..).le))
omit h p
lemma touch_local (A:BudgetPoint)(c:Clip)(T:PathData SU.group)(β:ℝ){w C D:ℝ}(ht:T.Bounds c w C D)(k:ValidR c A M): LocalOn (↑(touch M l)) (fun U=>heavy c A T M β U l) := by cases l; exact direct_here (G:=SU.group) c A β _; exact higher_local c A T M β ht _ k
-- linear touch agrees on physical links in indicated support. proof uses per_fac and slot accesses.
lemma local_curl (σ:Signed)(p:Cell s)(W V:Argument s){S}(h:touched p⊆ S)(g:Agrees (move σ S) W V): curlP σ p W=curlP σ p V:=by
 have e(i):Form.part σ (positions p i) W= Form.part σ (positions p i) V:= congrArg (turn (σ.flip ((positions p i).2))) (g _ (per_fac σ _ _ ⟨h (curl_positions p i).1,h (curl_positions p i).2⟩).1 (per_fac σ _ _ ⟨h (curl_positions p i).1,h (curl_positions p i).2⟩).2) -- tune
 simp only [curl_px,e]
lemma touch_grade (W V:Argument s)(T:PathData SU.group)(g:Agrees (touch M l) W V): linear T M l W=linear T M l V:=by
 cases l with
 | inl l=>
   change curlP 1 l W=curlP 1 l V; apply local_curl 1 l W V (Subset.refl _); convert g using 1; congr; change move 1 (touched l)=touched l; simp only [move]; rw [show (⇑(Micro.equiv (s:=s) 1))=id from funext fun x=> Signed.act_one _]; simp
 | inr a=>
   change ray T M a W=ray T M a V; rw [rays,rays]; refine sum_congr rfl fun i hi=>?_ ; congr 1; let x:=(ref a).1
   change Agrees ↑(pulley a M) W V at g; rw [pulley_ref] at g; exact local_curl a.1 _ _ _ (fun i' h' => halo_spec.mpr ⟨_,mem_singleton_self _,(jogB i x _ h').trans (by have h:= (Stack.short_iff ..).1 hi; omega)⟩) g
end YM.CF.BProof.Charge
