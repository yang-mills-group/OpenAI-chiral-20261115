import YM.SU5.Registration.Postcards.Enclose
import YM.SU5.Registration.Postcards.Astrolabe

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
-- orders & frames. Some poses unique time but not generic (for neighbor use), ink & φ still price. Never posing raw Mark unless generic.
local notation "T" => TrainJ V
abbrev pointsOf (l: List T) :Points l.length:=points (Prod.snd ∘ l.get)
abbrev idsOf (l:List T) : Fin l.length→V:= Prod.fst ∘ l.get
def Auction (l:List T): Prop:= ∀ i:Axis, (l.map (fun x=> x.2 i)).Nodup
def Salient (l:List T): Prop:= (l.map fun x=> YM.time x.2).Nodup
def chron (l:List T) : Prop:= l.Pairwise (fun x y=> YM.time x.2 < YM.time y.2)
lemma Auction.sal {l:List T}(h:Auction l) : Salient l:= h _
lemma auction_iff (l:List T) : Auction l↔ pointsOf l ∈ generic _:=by
 unfold Auction; have he(i:Axis): l.map (fun x=>x.2 i)= List.ofFn fun j=> (l.get j).2 i:=by
   nth_rw 1 [← List.ofFn_get l] -- no dep
   rw [List.map_ofFn]; rfl
 simp_rw[he,List.nodup_ofFn]; rfl
lemma sal_iff (l:List T) : Salient l ↔ Injective (lineK (pointsOf l)) := by
 unfold Salient; let f (x:T):= YM.time x.2; have he:l.map f=List.ofFn (f ∘ l.get):=by rw [← List.map_ofFn,List.ofFn_get]
 rw [he,List.nodup_ofFn]; rfl
lemma chrono_iff (l:List T): chron l ↔ pointsOf l∈Wheeled _:=by rw [chron,List.pairwise_iff_get]; exact ⟨fun p {a b} h=>p a b h,fun p i j h=> p h⟩ -- reducible?
lemma auction_slots (v:Fin n→V)(q:Points n):Auction (slots q v)↔ q∈generic n:=by unfold Auction slots; simp_rw[List.map_ofFn,List.nodup_ofFn]; rfl
lemma sal_slots (v:Fin n→V)(q:Points n):Salient (slots q v)↔ Injective (lineK q):= by rw [Salient, slots,List.map_ofFn,List.nodup_ofFn]; rfl
lemma chron_slots (v:Fin n→V)(q:Points n):chron (slots q v)↔q∈Wheeled n:=by rw [chron,slots,List.pairwise_ofFn]; exact ⟨fun p {a b} h=> p h, fun p {i j} k =>p k⟩
lemma perm_sal {t l:List T} (e:t.Perm l) (h:Salient l) : Salient t:= ((e.map _).nodup_iff).2 h
lemma perm_auction {t l:List T} (e:t.Perm l) (h:Auction l) : Auction t:= fun i=> ((e.map _).nodup_iff).2 (h i)
lemma chrono_sal (t:List T)(p:chron t) : Salient t:= (sal_iff t).2 ((show StrictMono (lineK (pointsOf t)) from ((chrono_iff t).1 p)).injective)
set_option linter.unusedSectionVars false
set_option quotPrecheck false
local notation "R" => fun x y : TrainJ V => YM.time x.2 ≤ YM.time y.2
noncomputable def ordered (l:List T) : List T:= List.insertionSort (R) l
lemma order_cost (l:List T): (ordered l).Perm l:=List.perm_insertionSort ..
lemma order_sal {l:List T}(p:Salient l): chron (ordered l):=by
 letI :IsTrans T (R):= ⟨fun _ _ _ => le_trans⟩; letI : Std.Total (R):= ⟨fun _ _=> le_total ..⟩; let S:= ordered l; have he: S.Pairwise (R):= List.pairwise_insertionSort ..; have ht:= (sal_iff S).1 (perm_sal (order_cost l) p); refine List.pairwise_iff_get.mpr (fun i j h=> lt_of_le_of_ne (List.pairwise_iff_get.mp he i j h) (ht.ne h.ne))
lemma order_match {l t: List T}(h:l.Perm t)(p:chron l)(q:chron t): l=t:=List.Perm.eq_of_pairwise (fun a b ha hb (h:YM.time a.2 < YM.time b.2) t=> False.elim (asymm h t)) p q h -- order tune
lemma order_on_sal (l:List T)(h:chron l): ordered l=l:= order_match (order_cost _) (order_sal (chrono_sal l h)) h
lemma perm_schedule (q:Points n)(v:Fin n→V)(r:Equiv.Perm (Fin n)): List.Perm (slots (Points.rearrange r q) (v∘r)) (slots q v):= by
 let f(i:Fin n):T:=(v i,q i)
 change List.Perm (List.ofFn (f∘r)) (List.ofFn f)
 exact r.ofFn_comp_perm ..
lemma all_scheduled (q:Points n)(u:Injective (lineK q)) (t:Equiv.Perm (Fin n)) (h:Points.rearrange t q∈Wheeled n)(v:Fin n→V) : ordered (slots q v)= slots (Points.rearrange t q) (v ∘ t):= order_match ((order_cost _).trans (perm_schedule q v t).symm) (order_sal ((sal_slots v q).2 u)) ((chron_slots ..).2 h)
lemma auction_move {t:List T}(p:Auction t)(d:E4) : Auction (moveCaps t d):=fun i => by
 have he : ((moveCaps t d).map (fun x=>x.2 i))=(t.map (fun x=>x.2 i)).map (· +d i):=by rw [moveCaps,List.map_map,List.map_map]; rfl
 rw [he]; exact (p i).map (fun x y=> add_right_cancel)
lemma chrono_moves (t:List T)(p:chron t)(d:E4):chron (moveCaps t d):= List.pairwise_map.mpr (p.imp (fun h=> add_lt_add_left h (YM.time d))) -- lemma obsolete?
lemma salient_mirror (l:List T)(p:Auction l)(J:JMap V):Auction (turnSpec J l):= fun i=> by
 unfold turnSpec; let h:= l.map (fun p=> p.2 i); rw [List.map_map, List.map_reverse, List.nodup_reverse]; by_cases z:i=timeAxis
 · rw [show (_ ∘ halfShot J)=(fun x:ℝ=> -x) ∘ fun x:T=> x.2 i from (by funext x; dsimp only [Function.comp_apply,halfShot]; subst i; exact mirror_time _),←List.map_map]; exact (p i).map neg_injective
 rw [show (_ ∘ halfShot J)=(fun x=> x.2 i) from (by funext x; dsimp only [Function.comp_apply,halfShot]; rw [mirror,Signed.mirrored]; exact if_neg z)]; exact p i
lemma chrono_turn (l:List T)(p:chron l)(J:JMap V): chron (turnSpec J l):=by apply List.pairwise_map.mpr; apply List.pairwise_reverse.mpr; refine p.imp ?_; intro i j h; change YM.time (mirror j.2)< YM.time (mirror i.2); rw [mirror_time,mirror_time]; exact neg_lt_neg h
def AdmitMom (F:InkWaves V)(l: List T): ℂ:= F.entrance (pointsOf l) (idsOf l)
def Figures (F:InkWaves V)(l:List T):ℂ := AdmitMom F (ordered l)
lemma read_cast (F:InkWaves V)(l:List T){p:Points n}{v:Fin n→V}(h:n=l.length)(e:∀ i,l.get (Fin.cast h i)=(v i,p i)): AdmitMom F l=F.entrance p v:=by
 subst n; unfold AdmitMom; rw [show pointsOf l=p from PiLp.ext fun j=>congrArg Prod.snd (e j), show idsOf l=v from funext fun j=> congrArg Prod.fst (e j)]
lemma slots_read (F:InkWaves V)(v:Fin n→V)(p:Points n): AdmitMom F (slots p v)=F.entrance p v:=by refine read_cast F _ (by simp [slots]) ?_; intro i; simp [slots]
lemma slots_pts (l:List T): slots (pointsOf l) (idsOf l)=l:= by
 unfold slots; simpa only [Function.comp_apply,points_apply] using List.ofFn_get l
lemma figures_here (F:InkWaves V)(l:List T)(h:chron l) : Figures F l=AdmitMom F l:=by unfold Figures; rw [order_on_sal l h]
lemma figures_perm (F:InkWaves V){l t:List T}(p:Salient l)(t':List.Perm l t): Figures F l= Figures F t:= congrArg (AdmitMom F) (order_match (((order_cost _).trans t').trans (order_cost _).symm) (order_sal p) (order_sal (perm_sal t'.symm p)))
-- needed p width qualifications. works for ANY $p$ sufficient (then quantities unique). rule also for ties? no. 
structure waltz (t:ℝ≥0)(l:List T):Prop where
 hp: 0<t
 lt: t<1
 clear : l.Pairwise (fun x y=> 4*(t:ℝ)<YM.time y.2-YM.time x.2)
lemma waltz_eq (t:ℝ≥0)(l:List T) : waltz t l ↔ enough (lineK (pointsOf l)) t:=by
 constructor; · exact fun x=> ⟨x.hp,x.lt,List.pairwise_iff_get.mp x.clear⟩
 intro x; exact ⟨x.1,x.2.1,List.pairwise_iff_get.mpr x.2.2⟩
lemma waltz_slow {t:ℝ≥0}{l:List T}(h:waltz t l){p:ℝ≥0}(hp:0<p)(e:p≤ t): waltz p l:= ⟨hp,e.trans_lt h.lt,h.clear.imp fun g=> lt_of_le_of_lt (mul_le_mul_of_nonneg_left (show (p:ℝ)≤(t:ℝ) from e) zero_le_four) g⟩
lemma waltz_exists {l:List T}(h:chron l) : ∃ t:ℝ≥0,waltz t l:=by
 let z(i:Fin l.length):ℂ:= lineK (pointsOf l) i; -- im* I
 have hp:= Work.C03.exists_lit (show (fun i=>z i *Complex.I)∈ strict _ from (fun i j q=>by simpa [z] using (show StrictMono (lineK (pointsOf l)) from (chrono_iff l).1 h) q))
 obtain ⟨v,x⟩:= hp; refine ⟨v,(waltz_eq ..).2 ?_⟩; unfold lit at x; simpa only [z,Complex.mul_I_im, Complex.ofReal_re] using x
lemma waltz_chron {t:ℝ≥0}{l:List T}(h:waltz t l): chron l:= h.clear.imp fun i=> sub_pos.mp ((mul_pos (by norm_num) (show 0<(t:ℝ) from h.hp)).trans i)
lemma waltz_turn {t:ℝ≥0}{l:List T}(p:waltz t l)(J:JMap V): waltz t (turnSpec J l):=by
 refine ⟨p.hp,p.lt,List.pairwise_map.mpr (List.pairwise_reverse.mpr ?_)⟩; refine p.clear.imp ?_; intro i j h; change 4*(t:ℝ)< YM.time (mirror i.2)- YM.time (mirror j.2); rw [mirror_time,mirror_time,neg_sub_neg]; exact h
variable {B}
lemma small_moment {F:InkWaves V}(p:B.Defined F)(t:ℝ≥0)(l:List T)(h:waltz t l): Figures F l= inner ℂ B.omega (caps B t l B.omega):=by
 rw [figures_here F l (waltz_chron h),AdmitMom,cap_matrix t p _ _ ((waltz_eq ..).1 h),slots_pts]
lemma figure_turn {F:InkWaves V}(P:B.Defined F)(l:List T)(p:Salient l)(J:JMap V)(g:Remembers B J): star (Figures F l)=Figures F (turnSpec J l):=by
 let u:=order_sal p; obtain ⟨k,w⟩:= waltz_exists u; rw [show Figures F l=Figures F (ordered l) from figures_perm F p (order_cost _).symm,small_moment P _ _ w];
 have t:List.Perm (turnSpec J (ordered l)) (turnSpec J l):=(List.Perm.trans (List.reverse_perm (ordered l)) ((order_cost l).trans (List.reverse_perm l).symm)).map _; rw [← figures_perm F (chrono_sal _ (chrono_turn _ u J)) t, small_moment P _ _ (waltz_turn w J),←cap_mirror k J g]
 exact (inner_conj_symm ..).trans (ContinuousLinearMap.adjoint_inner_right ..).symm
end YM.SatinWFixed.Passage
open YM.SatinWFixed.Passage
#print axioms figures_perm
#print axioms figure_turn
#print axioms perm_schedule
