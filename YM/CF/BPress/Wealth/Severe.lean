import YM.CF.BPress.Wealth.Higher
/-! Mark-perturbation decomposition with heavy roots assigned to severe columns. Scores include K+L compensation on *all* roots. Keeping logs additive for exact `eq:B-Heavy`. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(M:ℕ) (R:PathData group)(d:Clip)(p:BudgetPoint) (β y:ℝ)(S:Finset X.Hcols) (w: Directions group s)
-- heavy input orientation v controls. `K_h` whole.
def due (i : Root s):= heavy R d p β M i (background y)
def outer := univ.filter (retained X M)
def debtH := ∑ i∈outer X M,due M R d p β y i
-- assign by first choice. depends only on eligible set.
def take1 {X:Type*}(S:Finset X):Option X := if p:S.Nonempty then some p.choose else none
def beginA (S:Finset X.Hcols)(i:Root s):= take1 (S∩ danger X M i)
def bookS (x:X.Hcols):= (outer X M).filter fun i=> beginA X M S i=some x
def error (U:Micro s)(i:Root s):= heavy R d p β M i U-(due M R d p β y i+first R d M β y i w+second R d M β i w)
def spent (U:Micro s)(i:Root s) := (due M R d p β y i + first R d M β y i w)-heavy R d p β M i U

def pays (U:Micro s)(x:X.Hcols) := ∑ i∈ bookS X M S x,spent M R d p β y w U i

variable {X M}
lemma book_t {x : X.Hcols}{i: Root s} (t:i∈bookS X M S x) : x∈ S∩ danger X M i:= by
 obtain ⟨u,p⟩:=mem_filter.mp t; unfold beginA take1 at p; split at p; next h=> exact Option.some.inj p ▸ h.choose_spec -- tune
 contradiction
lemma start_eq (i:Root s) : beginA X M S i=none ↔ regular (X:=X) (M:=M) S i:=by
 unfold beginA take1 regular; rw [disjoint_iff_inter_eq_empty]; split; next t=> simp [t.ne_empty]
 next t=> simp [Finset.not_nonempty_iff_eq_empty.mp t]
lemma assigned {i:Root s} (p: ¬regular (X:=X) (M:=M) S i)(r:retained X M i): ∃ x∈ S, i∈ bookS X M S x:=by
 cases h:beginA X M S i with|none=> exact (p (start_eq ..|>.1 h)).elim|some x=> have ht : i∈bookS X M S x:=mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,r⟩,h⟩; exact ⟨x,(mem_inter.mp (book_t S ht)).1,ht⟩ -- tune formatting
lemma pays_V (u:High B M)(i:X.Air)(p : i.1∈ S): Sum.inl (vert X i)∈ bookS X M S i.1:=by
 obtain ⟨x,g,t⟩:=assigned (X:=X) (M:=M) S (mt (use_vert u S i).mp (not_not_intro p)) (vert_ret X M i); have h:= (mem_inter.mp (book_t S t)).2; rw [danger,if_pos (show steep (.inl (vert X i)) from vert_l X i), vert_block X M u.spans i, mem_singleton] at h; rwa [←h]
lemma begin_g (i:Root s){T: Finset X.Hcols} (p:∀ j∈ rangeTh X M i, j∈ S ↔ j∈ T): beginA X M S i= beginA X M T i:=by
 unfold beginA; apply congrArg take1; ext j; simp only [mem_inter]; exact and_congr_left fun t=> p j (danger_sub i X M t)
lemma book_cost (p:High B M)(x:X.Hcols): (bookS X M S x).card ≤ counted M B.D:= by
 apply (LE.le.trans (b:=#(univ.filter (fun i:Root s=> retained X M i ∧ x∈ rangeTh X M i))) ?_ (ticket_copies p x)); apply card_le_card; intro i v; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ((mem_filter.mp v).1)).2, danger_sub i X M ((mem_inter.mp (book_t S v)).2)⟩
lemma book_local (x:X.Hcols) {T:Finset X.Hcols} (p:∀ j∈columnBall X x (6*M),j∈S↔j∈T): bookS X M S x=bookS X M T x:=by
 ext i; by_cases v:x∈rangeTh X M i; swap; · simp only [iff_false_intro (show i∉bookS X M T x from fun t=> v (danger_sub i X M ((mem_inter.mp (book_t T t)).2))),iff_false]; exact fun t=> v (danger_sub i X M ((mem_inter.mp (book_t S t)).2)) -- tune simp
 unfold bookS; simp only [mem_filter]; rw [begin_g S i (T:=T) (fun j t=> p j (by rw [show 6*M=3*M+3*M by omega]; exact reach_add X (column_sym.mpr v) t))]
variable (X M)
variable {C Λ σ:ℝ}(H:R.Bounds d σ C Λ)
include H
lemma debit (U:Micro s): ∑ i∈outer X M,- heavy R d p β M i U= -debtH X M R d p β y -(∑ i ∈ Θ X M S,(second R d M β i w+error M R d p β y w U i)) +∑ x∈S,pays X M R d p β y S w U x := by
 let g:=spent M R d p β y w U; let f:=Θ X M S; let V:=outer X M; let t:=S.biUnion (bookS X M S); have h: t=V \ f:= by
    ext i; rw [mem_biUnion]; constructor
    · rintro ⟨x,h,v⟩; have he:beginA X M S i=some x:=(mem_filter.mp v).2; exact mem_sdiff.mpr ⟨(mem_filter.mp v).1, fun k=> by have hu:= ((start_eq ..).2 ((mem_filter.mp k).2).2); rw [he] at hu; contradiction⟩
    intro p; obtain ⟨t,v⟩:= mem_sdiff.mp p; have he:= (mem_filter.mp t).2; apply assigned S _ he; exact fun x=> v (mem_filter.mpr ⟨mem_univ _, he,x⟩)
 have ht:(∑ i∈f,g i)+(∑ x∈ S, pays X M R d p β y S w U x)= ∑ i∈V, g i:=by
    unfold pays; rw [← sum_biUnion]; swap; · intro i w j k r; exact disjoint_left.mpr fun a p t=> r (Option.some.inj ((mem_filter.mp p|>.2.symm).trans ((mem_filter.mp t).2))) -- tune
    unfold t at h; rw [h]; exact (add_comm ..).trans (sum_sdiff (fun i (v:i∈f)=> mem_filter.mpr ⟨mem_univ _, (mem_filter.mp v).2.1⟩))
 have he(i:Root s): second R d M β i w+ error M R d p β y w U i= - g i:= by unfold error g spent; abel
 have F: (∑ i∈V,g i)=debtH X M R d p β y-∑ i∈V, heavy R d p β M i U:=by unfold g spent V outer; rw [sum_sub_distrib,sum_add_distrib,show _=_ from magcancel w M R H X β y, add_zero]; rfl
 simp_rw [he,sum_neg_distrib]; change _= -_ - -(∑ i∈ f,g i)+_; rw [sub_neg_eq_add,add_assoc, ht, F]; abel

omit H
-- detection & price of at least ONE vertical root per severe
variable {X} {κ:ℝ}{U V:Micro s} {K:Bills X E}
private lemma start_D (x:X.Index)(g:Mission X y K V U)(h:ToneNoise y V)(p:FlatLink s): chord (horizontal (X.depth x 0) U p) (magnetH y p.2) ≤ xi y:=by
 let t:= X.depth x 0; let i:= fl t p; have hx : i ∈ inside (halo (cloak B) (X.gap x)):= by refine inside_le (halo_subset (cloak B) (X.gap x)) ?_; apply ((X.ditch x).tang_in p).2 ?_; exact depth_time X x (Nat.zero_le B.D)
 have u:= costBeg y g h hx; unfold i angleBeg t at u; rw [key_o,Option.elim_none,horizontal_background] at u; exact u
lemma billing_vert (t:Mission X y K V U)(h:ToneNoise y V)(g : κ > 0)(v: 0 < y)(e:xi y≤ κ*temp y/2)(x:X.Hcols)(p:severe X κ y K x): ∃ (k:X.Air), k.1=x ∧ (κ/(2*B.D))*temp y ≤ group.chord (faceValue U (vert X k)):=by
 obtain ⟨⟨i,j⟩,p⟩:= p; let b:ℝ:= κ/(2*B.D); let a(l:ℕ):= horizontal (X.depth x.1 l) U (x.2,j); let C:= magnetH y j; have hg: κ*temp y < chord (a (i.val+1)) C:= by
    have hx:= t.lens (x,i,j); change a _=K _ at hx; rw [hx]; exact p
 by_contra q; let A:=b*temp y; have hb: (0:ℝ) < B.D:= by exact_mod_cast B.D_pos
 have ha:0< A:= by unfold A b; positivity [temp_pos v]; -- tune spacing
 have he (l:ℕ)(p:l ≤ B.D) : chord (a l) C ≤ xi y+l*A:=by
    induction l with
    | zero=> simpa using start_D (X:=X) y x.1 t h (x.2,j)
    | succ l ih=>
       let P:X.Air:= (x,⟨l,p⟩,j); refine (chord.triangle _ (a l) C).trans ((add_le_add (b:= A) ?_ (ih (by omega))).trans_eq ?_); rw [←show group.chord _= _ from vert_cliff X P U t.park]; apply le_of_not_ge; exact fun k=> q ⟨P,rfl,k⟩ -- uses < (le_of_not_ge)? not_ge means B ≱ A; here goal not≥? a≤A, not ≥?? lean le_of_not_ge: ¬ A≥? check
       push_cast; ring
 apply not_lt_of_ge ?_ hg; apply le_trans (he (i.val+1) i.isLt); apply le_trans (add_le_add e (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show i.val+1≤B.D from i.isLt)) ha.le)); unfold A b; field_simp; exact le_of_eq (by ring)

def loss (d:Clip)(r:ℝ) := min (d.direct*r^2/2) d.linear
lemma loss_pos {r:ℝ}(u:0<r): 0<loss d r:= by unfold loss; positivity [d.quadratic_pos,d.tail_pos]
lemma losses (V:ℝ)(h:0< V)(w:0<y)(r:ℝ)(v:0<r)(q:r*temp y ≤ V) : loss d r*temp y^2 ≤ PathData.clipped d (temp y) V:= by
 let P:=temp y; have ht:0<P:=temp_pos w; have h':= d.quadratic_pos; have he:=d.tail_pos; unfold loss PathData.clipped; split; next t=>
    apply le_trans (mul_le_mul_of_nonneg_right (min_le_left ..) (sq_nonneg _)); calc
     _ = d.direct*(r*P)^2/2:= by unfold P; ring
     _ ≤ d.direct*V^2/2:= by gcongr
 next t=> apply le_trans (mul_le_mul_of_nonneg_right (min_le_right ..) (sq_nonneg (temp y))); rw [sq,←mul_assoc]; gcongr; exact le_of_lt (lt_of_not_ge t) -- tune
-- assign rarity absolute eps. pointwise exact prices; gate integration uses every such charge assigned.
end YM.CF.BPress.Wealth
