import YM.SU5.Registration.Postcards.EnterSort

/-!
 # Euclidean crossing (116) by finite averages escaping to infinity.
 
 Enough in this version to run many usual *Eu boost-plane* tests. No full-cone estimate
 used in the cluster pricing, in E or in M! (Need equality of unconditioned point-moment at the indicated
 tests as structural angular estimate.) Our method uses real-angle co-rotation even
 in the payments evaluating (116). Works with REAL displacements large even in every axis,
 need not supply time-ground projector equality to joint projection of unconditioned.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Passage
open Boundary Mink Analysis Function Set Filter OS.Semigroup
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
open CF.Buffered.Afterglow.Tower.VacuumSelection
open CF.Buffered.Afterglow.Hierarchy.Seld
open CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Carton
variable {H : Hilbert} (S : OS.Semigroup H timeAxis)
open ContinuousLinearMap MeasureTheory Small
variable {S} {V : Type*}[AddCommGroup V][Module ℂ V] (B:Carton S V){n m:ℕ}
-- use Postcards/ bridge with temporal fare subtracting before pricing
local notation "T" => TrainJ V
set_option linter.unusedSectionVars false
-- seam words and labels. minimum shared time gap 4 (can take 4*h later). positions shifted.
def Solemn (u:E4): Prop:=∀ j:Axis,0≤u j
def SweepAhead (l t:List T)(u:E4) : Prop:= ∀ i ∈ l, ∀ j∈ t,∀ k:Axis,4+i.2 k < j.2 k + u k
lemma solemn_zero : Solemn 0:=fun _=> le_rfl
lemma Solemn.mixes {u v}(p:Solemn u)(q:Solemn v): Solemn (u+v):=fun i=> add_nonneg (p i) (q i)
lemma ample_sick (u:E4)(p:ampleStep u): Solemn u:=fun i=>(p i).le
lemma SweepAhead.more {u d:E4}{l t:List T}(h:SweepAhead l t u)(p:Solemn d): SweepAhead l t (u+d):=fun i t j v b=>by refine (h i t j v b).trans_le (?_); simp only [← add_assoc, PiLp.add_apply]; linarith [p b]
lemma SweepAhead.perm {t t' l l':List T}{u:E4}(h:SweepAhead l t u) (p:l.Perm l')(q:t.Perm t'):SweepAhead l' t' u:= fun i hi j hj k=> h i (p.mem_iff.mpr hi) j (q.mem_iff.mpr hj) k
lemma SweepAhead.auction {t l:List T}{u:E4} (p:SweepAhead l t u)(h:Auction l)(k:Auction t) : Auction (l++moveCaps t u):=by
 intro i; rw [List.map_append, List.nodup_append]; -- disjoint
 refine ⟨h i,auction_move k u i,?_⟩
 intro a ha b hb; obtain ⟨x,hx,rfl⟩:= List.mem_map.mp ha; obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hb; obtain ⟨w,hw,rfl⟩:= List.mem_map.mp hy
 change x.2 i≠w.2 i + u i; exact ((lt_add_of_pos_left _ (by norm_num:(0:ℝ)<4)).trans (p x hx w hw i)).ne
lemma waltz_shift (t:ℝ≥0)(l:List T)(p:waltz t l)(v:E4): waltz t (moveCaps l v):=by
 refine ⟨p.hp,p.lt,List.pairwise_map.mpr (p.clear.imp ?_)⟩; intro i j h; change 4*(t:ℝ)<YM.time (j.2+v)- YM.time (i.2+v); rw [add_time,add_time,add_sub_add_right_eq_sub]; exact h
lemma SweepAhead.cash {t l:List T}{u:E4} (p:SweepAhead l t u) {q:ℝ≥0} (v:q<1) (i:T)(j:T)(G:i∈l)(H:j∈t):4*(q:ℝ)< YM.time (j.2+u)- YM.time i.2:=by
 have he:= p i G j H timeAxis; rw [add_time]; change 4*(q:ℝ)< j.2 timeAxis+u timeAxis- i.2 timeAxis; linarith [show (q:ℝ)<(1:ℝ) from v]
lemma SweepAhead.charge {t l:List T}{u:E4} (p:SweepAhead l t u)(q:ℝ≥0)(k:waltz q l)(h:waltz q t): waltz q (l++moveCaps t u):= by
 refine ⟨k.hp,h.lt,List.pairwise_append.mpr ⟨k.clear,(waltz_shift q t h u).clear,?_⟩⟩; rintro i x j b; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp b; exact p.cash k.lt i v x hv
lemma spending_ahead (l t:List T) : ∀ᶠ K:ℝ in atTop, ∀ x:E4, (∀ i:Axis,K<x i)→ SweepAhead l t x:= by
 classical
 let p(i j:T)(k:Axis):ℝ:= 4+i.2 k -j.2 k
 filter_upwards [(eventually_all_finset l.toFinset).mpr (fun i _=> (eventually_all_finset t.toFinset).mpr (fun j _=>eventually_all.mpr fun k=> eventually_ge_atTop (p i j k)))] with g h x P i d j b k
 specialize h i (List.mem_toFinset.mpr d) j (List.mem_toFinset.mpr b) k; have hu:=h.trans_lt (P k); unfold p at hu; linarith
lemma moves_price {l t:List T}(g:List.Perm l t)(u:E4): List.Perm (moveCaps l u) (moveCaps t u):=g.map _
lemma cost_extension {l t:List T} {d u:E4} (r:Solemn u) (h:SweepAhead l t d) (a:Auction l)(b:Auction t) : Auction (l++moveCaps t (d+u)):= (h.more r).auction a b
-- expansion. use append averages in either frame; can include empty contributions.
variable {B} {F:InkWaves V} (P:B.Defined F)
include P
lemma at_ticket_empty : Figures F []=1:=by
 have h: (1:ℝ≥0)/2 < 1:=by norm_num
 let p: waltz ((1:ℝ≥0)/2) ([]:List T):=⟨half_pos zero_lt_one,h,List.Pairwise.nil⟩; rw [small_moment P _ _ p]; simp [caps, B.size, inner_self_eq_norm_sq_to_K]
lemma companion_cost (p:ℝ≥0)(l t:List T)(k:waltz p l)(h:waltz p t)(a:T)(b:T)(v t':List T)(hv:l=v++[a])(r:t=b::t')(d:E4)(g:SweepAhead l t d)(u:E4)(w:Solemn u) : Figures F (l++moveCaps t (d+u)) =
 inner ℂ B.omega ((caps B p l * pitStop S p a.2 (b.2+d) * postcard S u* caps B p t) B.omega):=by
 rw [small_moment P _ _ ((g.more w).charge _ k h)]; congr 3
 let δ:=d+u; rw [←cap_stationary B p t δ, r, hv]; unfold moveCaps; simp only [List.map_cons]; rw [cap_append,show b.2+(d+u)=(b.2+d)+u from (add_assoc ..).symm, pit_add p a.2 (b.2+d) (g.cash h.lt a b (by simp [hv]) (by simp [r])) u (w timeAxis), ← mul_assoc (caps B p (v++[a]))] -- tune with let δ
lemma either_moving (p:ℝ≥0)(l t:List T)(k:waltz p l)(h:waltz p t)(d:E4)(g:SweepAhead l t d): ∃ J:H.Op, ‖J‖≤1 ∧ J B.omega=B.omega ∧ ∀ (u:E4),Solemn u→
 Figures F (l++moveCaps t (d+u)) = inner ℂ B.omega ((caps B p l * J* postcard S u * caps B p t) B.omega):=by
 have hold (u:E4) (x:H): inner ℂ B.omega (postcard S u x)= inner ℂ B.omega x:=by
    let y := (SEP timeAxis u).val; change inner ℂ _ (M S y (S.E _ x))=_; rw [tboth,show M S (-y) B.omega= B.omega from B.stay _, ← S.swing,B.hot]
 have stay (u:E4):postcard S u B.omega=B.omega:=by change M S _ (S.E _ _)=_; rw [B.hot]; exact B.stay _
 rcases List.eq_nil_or_concat' l with e|⟨a,b,e⟩; -- check
 · subst l; refine ⟨postcard S 0,card_norm ..,stay _,fun u _=>?_⟩; rw [card_zero,List.nil_append, small_moment P _ _ (waltz_shift p t h _),cap_stationary]; change inner ℂ _ _=inner ℂ _ (postcard S u _); rw [hold]; rfl
 cases t with
 | nil=> refine ⟨postcard S 0,card_norm ..,stay _,fun u _=>?_⟩; rw [card_zero,moveCaps,List.map_nil,List.append_nil, small_moment P p l k]; change inner ℂ _ _=inner ℂ _ (caps B p l (postcard S u B.omega)); rw [stay]
 | cons i t=> refine ⟨pitStop S p b.2 (i.2+d),card_norm ..,pit_hot ..,?_⟩; exact companion_cost P p l (i::t) k h b i a t e rfl d g
end YM.SatinWFixed.Passage
open YM.SatinWFixed.Passage
#print axioms either_moving
