import YM.CF.BPress.Locale.Depth
import YM.CF.BPress.Wealth.March
import YM.CF.BPress.Port.Raw
/-!
`eq:B-mapcard`. Widths before period. Need floor selecting component witnesses only on T. use exact counting. Posed for given h parameters. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth Weave Radix
open scoped Topology BigOperators Classical Matrix
variable {s:Side}{b:BandWidth}(X:Bands s b) (R:Hangar s){T:Sheet.Atlas}{y L C C':ℝ}{a:ℕ}
variable (F:Net s T L y C C' a) (S:Support s)
structure Frame (S L:Seal (Tri s)):Prop where
 fee_g : Grove (Grid.field 3 s) L
 sub : S⊆L
 read (U V : Horiz s)(p q:HFrame s) : equalOn U V L → Set.EqOn p q L→ Set.EqOn (F.frame U p) (F.frame V q) S

def firm (U: Support s): Seal (Tri s):= U.image (fun x=>Fin.tail x)
def cart (i:X.Index)(S:Seal (Tri s)):= (S.image (Prod.mk i)).image (own X R)
structure Floor (Q:Seal (SiteX X R)): Prop where
 base_g : Grove (shape X R) Q
 yard : broad (shape X R) (S.image (plan X R)) 1⊆ Q -- note short map doesn't include this
 knows(p:X.Index × Support s): p∈gaze X S→∃ L:Seal (Tri s), Frame F (firm p.2) L ∧ cart X R (p.1-1) L ∪ cart X R p.1 L⊆ Q
structure Rights (R:Hangar s)(b:BandWidth)(Lf y:ℝ)(r:ℕ): Prop where
 thin : R.L.val≤ umbra b
 near : r < umbra b
 memory : (frameWidth Lf y).val ≤ b.marked.val

abbrev baser:=estate 1*estate 2
abbrev creep (m:ℕ)(Lf y:ℝ):=m *(32+rFrame Lf y+1)
abbrev pacer (a:ℕ)(Lf y:ℝ):=baser + 2*estate 2*(creep a Lf y+1)
-- `Y` price both attaches
variable {X R}{A B : Seal (Tri s)} -- b binder update duplicate check
lemma membership {x:X.Index}{a:Tri s} (h:a∈A): own X R (x,a) ∈ cart X R x A:= mem_image_of_mem _ (mem_image_of_mem _ h)
variable (X R)
lemma docking (Q:Seal (Tri s))(p:Grove (Grid.field 3 s) Q)(x:X.Index) : Grove (shape X R) (cart X R (x-1) Q∪ cart X R x Q):=by
 let F:=shape X R; let A:= cart X R (x-1) Q; let B:=cart X R x Q; obtain ⟨i,v⟩:=Grid.inhabited_grove p; let a:=own X R (x-1,i); let b:= own X R (x,i); have ht:F.span a b≤1:=by have h:= adjacent X R (x-1) (tang R i); rw [sub_add_cancel] at h; exact h
 have ha:a ∈ A:=membership v; have hb:b∈B:= membership v; let f:= (crowd X R _ (fold_g X (x-1) Q p)).join (x:=b) ha ((F.sym _ _).le.trans ht); change Grove F (A∪B); rw [← show insert b A∪B= A∪ B from (by ext i; by_cases v:i=b<;> simp [*,Finset.mem_union])]; exact f.unite (crowd X R _ (fold_g X x Q p)) (mem_insert_self b A) hb
lemma cart_bill (Q:Seal (Tri s))(p:Grove (Grid.field 3 s) Q)(x:X.Index): R.L.val* (cart X R x Q).card ≤ estate 2*(Q.card+R.L.val):= (turf_print X R _ (fold_g X x Q p)).2.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right card_image_le _))
lemma umbra_pay {r:ℕ}(h:r<umbra b): b.marked.val ≤ 32* umbra b:=by unfold umbra at *; omega
variable {r:ℕ} -- order bindings
lemma acquire (p:Grove (Grid.field 4 s) S)(u:Rights R b L y r)(t:meets X r S)(o:X.Index× Support s)(v:o∈gaze X S) : ∃ U:Seal (Tri s), Frame F (firm o.2) U∧ R.L.val*(cart X R (o.1-1) U∪cart X R o.1 U).card ≤ 2*estate 2*(creep a L y+1)*o.2.card:=by
 let V:= firm o.2; obtain ⟨T,b1,h,g,q,c⟩:= F.frame_pays V (proj_g (gaze_cover X S _ v |>.2.1)); let k:= (frameWidth L y).val; let U:= o.2.card; have he: umbra b ≤ U:= by rcases o with ⟨i,Qx⟩; obtain ⟨x,h,h'⟩:= (gaze_mem ..).mp v; change umbra b ≤ Qx.card; simpa only [←h'] using stem_dep p u.near t h -- tune shadow
 have hK:R.L.val ≤ U:=u.thin.trans he; have ht:k ≤ 32*U:=u.memory.trans ((umbra_pay u.near).trans (Nat.mul_le_mul_left _ he)); have hv : T.card ≤ creep a L y*U:=by unfold creep; apply q.trans; rw [mul_assoc]; apply Nat.mul_le_mul_left; have he:V.card≤U:=card_image_le; exact (Nat.add_le_add ht (Nat.mul_le_mul_left _ he)).trans_eq (by ring) -- tune
 refine ⟨T,⟨b1,h,c⟩,?_⟩; let A:=cart X R (o.1-1) T; let B:=cart X R o.1 T; apply le_trans (Nat.mul_le_mul_left _ (card_union_le A B)); rw [Nat.mul_add]; let K(i:X.Index):= (cart_bill X R T b1 i).trans (Nat.mul_le_mul_left _ (Nat.add_le_add hv hK)); exact (Nat.add_le_add (K _) (K _)).trans (Eq.le (by unfold U; ring)) -- tune
lemma floor_pays (p:Grove (Grid.field 4 s) S)(u:Rights R b L y r)(t:meets X r S) : ∃ A, Floor X R F S A∧ R.L.val*A.card ≤ baser*R.L.val + pacer a L y*S.card:=by
 let Y:=gaze X S; let f:=plan X R; let U:=broad (shape X R) (S.image f) 1; have hp:R.L.val≤b.full.val:= by have hx:=b.marked_lt; have hf:=u.thin; unfold umbra at hf; omega
 obtain ⟨hx,lx⟩:= shape_print X R hp S p; obtain ⟨hu,lu⟩:= b_print X R (S.image f) hx 1
 choose! W e k using fun (i : X.Index × Support s)(v:i∈Y)=> acquire X R F S p u t i v
 let B(i:X.Index × Support s):= cart X R (i.1-1) (W i)∪cart X R i.1 (W i); have hb(i)(h:i∈Y) : Grove (shape X R) (B i):= docking X R _ (e i h|>.fee_g) _
 have he (i:X.Index × Support s) (v:i∈Y): ∃ x∈U,x∈B i:=by
   obtain ⟨x,hx⟩:= Grid.inhabited_grove (gaze_cover X S i v|>.2.1); obtain ⟨l,hl,g,f'⟩:= (gaze_cover X S i v).2.2 x hx; let z:=own X R (i.1,Fin.tail x); let y':=event (x 0) (Fin.tail x); have hv:y'∈ S:= by rw [show y'=x from event_eta x]; exact (gaze_cover X S i v).1 hx
   refine ⟨z, (frame_bridge X R S (Fin.tail x) i.1 (Nat.le_trans (Nat.le_add_right ..) g) f' hv).2, mem_union_right _ (show z∈cart X R i.1 (W i) from membership (A:=W i) ((e i v).sub ?_))⟩; exact mem_image.mpr ⟨x,hx,rfl⟩
 obtain ⟨h,w⟩:= Grid.many (shape X R) U hu Y B hb he -- tune `choose!`
 · refine ⟨U ∪ Y.biUnion B,⟨h,subset_union_left,fun i v=>⟨W i,e i v, Subset.trans (show B i ⊆ Y.biUnion B from subset_biUnion_of_mem _ v) subset_union_right⟩⟩,?_ ⟩
   have hv:S.card≥ ∑ i∈Y,i.2.card:= by rw [← card_biUnion (gaze_disjoint X S)]; exact card_le_card (show Y.biUnion Prod.snd ⊆ S from (by intro i v; obtain ⟨j,v,g⟩:=mem_biUnion.mp v; exact (gaze_cover X S _ v).1 g))
   apply (Nat.mul_le_mul_left _ w).trans; rw [mul_add]; let i:=b.marked.val; let P:= 2*estate 2*(creep a L y+1); have hm:R.L.val*(∑ i∈Y,#(B i)) ≤ P*S.card:=by rw [mul_sum]; apply (sum_le_sum k).trans; rw [← mul_sum]; exact Nat.mul_le_mul_left P hv
   have ht:R.L.val*U.card ≤ baser*(S.card+R.L.val):=calc
     _ ≤ R.L.val*(estate 1* #(S.image f)) := Nat.mul_le_mul_left _ lu
     _ = estate 1* (R.L.val* #(S.image f)):=mul_left_comm ..
     _ ≤ estate 1*(estate 2*(S.card+R.L.val)):= Nat.mul_le_mul_left _ lx
     _ = _ :=(mul_assoc ..).symm
   exact (Nat.add_le_add ht hm).trans (Eq.le (by unfold pacer P; ring))
end YM.CF.BPress.Locale
