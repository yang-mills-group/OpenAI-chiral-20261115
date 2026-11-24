import YM.SU5.Registration.Postcards.Road

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
variable {X:Type*} [TopologicalSpace X][MeasurableSpace X][OpensMeasurableSpace X][CompactSpace X] (μ:Measure X)[IsFiniteMeasure μ]
variable {H₀:X→Hilbert}{S₀:∀ x,OS.Semigroup (H₀ x) timeAxis}
-- API consumes charter families and Passport over at axis 3 only. Does not require a Mink or Eu rotation estimate in this structure.
structure Album (F:X→InkWaves V) (U:∀ x,Carton (S₀ x) V) (J:JMap V): Prop where
  accounts : ∀ x,(U x).Defined (F x)
  keep (x) : Remembers (U x) J
  rate (v:V)(s:ℝ≥0)(p:0<s): ∃ y≥ (0:ℝ),∀ x:X, ‖(U x).bar s v‖≤ y
  ticket (l:List (TrainJ V))(p:Auction l): Continuous (fun x=> Figures (F x) l)
  moors : ∀ᵐ x∂ μ, Moors (U x)
section cluster
variable (F:X→InkWaves V)
def meanFig (l:List (TrainJ V)) :ℂ:=∫ x, Figures (F x) l ∂μ
-- joint in two registers courtesy. no stars here, later USE θ3 to buy it anti at any eligible slot.
def fullFig (l t:List (TrainJ V)):ℂ:=∫ x, Figures (F x) l * Figures (F x) t ∂μ
variable {μ F} {U:∀ x,Carton (S₀ x) V} {J:JMap V} {l t:List (TrainJ V)}(p:Album μ F U J)
variable {I:Type}[Fintype I][Nonempty I] (f:I→E4)(g:∀ i,ampleStep (f i))(h:Auction l)(r:Auction t)
local notation "W!" x:max L:max=> Figures (F x) L
local notation "K!" x:max t:max s:max d:max=> Figures (F x) (t++moveCaps s d)
local notation "Θ" => fullFig μ F
include h r g p
lemma Album.shippable {d:E4}(q:SweepAhead l t d) (n:ℕ) : Continuous (fun x=> shipping f n (fun a=> K! x l t a) d):=by
 induction n generalizing d with
 | zero=> exact p.ticket _ (q.auction h r)
 | succ n ih=> change Continuous (fun x=> ((Fintype.card I:ℂ)⁻¹)*_); exact continuous_const.mul (continuous_finsetSum _ fun i _=> ih (q.more (ample_sick _ (g i))))
lemma Album.collected {d:E4}(q:SweepAhead l t d) (n:ℕ): Continuous (fun x=> postmark f n (fun a=> K! x l t a) d):= continuous_const.mul (continuous_finsetSum _ (fun i _=>p.shippable f g h r q i))
lemma Album.forges {d:E4}(q:SweepAhead l t d)(n:ℕ):(∫ x, shipping f n (fun a=> K! x l t a) d ∂μ) = shipping f n (fun u=> meanFig μ F (l++moveCaps t u)) d:=by
 induction n generalizing d with
 | zero=> rfl
 | succ n ih=>
                unfold shipping; rw [integral_const_mul, integral_finsetSum _ (fun i (_:i∈Finset.univ)=>?_)] -- with excess!
                · congr 1; exact Finset.sum_congr rfl fun i _=> ih (q.more (ample_sick _ (g i)))
                exact (p.shippable f g h r (q.more (ample_sick _ (g i))) n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) -- if budget
lemma Album.reels {d:E4}(q:SweepAhead l t d)(n:ℕ):(∫ x, postmark f n (fun a=> K! x l t a) d ∂μ)= postmark f n (fun a=>meanFig μ F (l++moveCaps t a)) d:=by
 unfold postmark; rw [integral_const_mul,integral_finsetSum _ (fun i _=> (p.shippable f g h r q i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]; simp_rw [p.forges f g h r q]
omit h r g
lemma Album.cap_cost (t:List (TrainJ V))(s:ℝ≥0)(g:0<s) : ∃ c≥(0:ℝ),∀ x, ‖caps (U x) s t‖≤ c := by
 induction t with
 | nil=> refine ⟨1,zero_le_one,fun x=>?_⟩; let B:= S₀ x; change ‖(1:(H₀ x).Op)‖≤1; rw [← card_zero B]; exact card_norm ..
 | cons i l ih=>
   obtain ⟨y,u,v⟩:= ih; obtain ⟨r,h,k⟩:= p.rate i.1 s g; refine ⟨r*y,mul_nonneg h u,fun x=>?_⟩
   have hp:‖clip (fun i j:T => pitStop (S₀ x) s i.2 j.2) i l‖≤1:=by cases l with
                                                                          | nil=> let B:= S₀ x; change ‖(1:(H₀ x).Op)‖≤1; rw [←card_zero B]; exact card_norm ..
                                                                          | cons j l=> exact card_norm ..
   refine (norm_mul_le ..).trans (?_); refine mul_le_mul (k x) ((norm_mul_le ..).trans ?_) (norm_nonneg _) h; exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans (v x)
def touringCosts (μ:Measure X)(F:X→InkWaves V) (l t:List (TrainJ V))(d:E4)(f:I→E4)(n:ℕ):ℂ:= postmark f n (fun u=> meanFig μ F (l++moveCaps t u)) d
include h r g
lemma Album.clusters (v:Priced f) {d:E4}(q:SweepAhead l t d) (c:chron l)(w:chron t): Tendsto (touringCosts μ F l t d f) atTop (𝓝 (fullFig μ F l t)):=by
 obtain ⟨s',a⟩:= waltz_exists c; obtain ⟨t',b⟩:=waltz_exists w; let s:=min s' t'; have hp:0<s:=lt_min a.hp b.hp; let hp':=waltz_slow a hp (min_le_left ..); let ht':=waltz_slow b hp (min_le_right ..)
 obtain ⟨Cx,u,hu⟩:= p.cap_cost l s hp; obtain ⟨Cy,v₀,hv⟩:=p.cap_cost t s hp
 let Q(x:X)(n:ℕ):=concertedMoments l t f (F x) n d; have he:Tendsto (fun n=>∫ x,Q x n ∂μ) atTop (𝓝 (fullFig μ F l t)):=by
    refine tendsto_integral_filter_of_dominated_convergence (μ:=μ) (fun _=>Cx*Cy) (?_) ?_ (integrable_const _) ?_
    · exact Eventually.of_forall fun n=> (p.collected f g h r q n).aestronglyMeasurable
    · exact Eventually.of_forall fun n=> Eventually.of_forall fun x=> (moment_bound s l t f g (F x) (p.accounts x) hp' ht' q n).trans (mul_le_mul (hu x) (hv x) (norm_nonneg _) u)
    exact p.moors.mono (fun x e=> concert_cluster s l t f g (F x) (p.accounts x) hp' ht' q v e)
 exact he.congr fun i=> p.reels f g h r q i
omit g p h r
lemma mean_perm {a b:List (TrainJ V)}(h:a.Perm b)(q:Salient a): meanFig μ F a=meanFig μ F b:= integral_congr_ae (Eventually.of_forall fun _=> figures_perm _ q h)
lemma Album.clusters_any (p:Album μ F U J)(g:∀ i,ampleStep (f i))(v:Priced f) (h:Auction l)(r:Auction t){d:E4}(q:SweepAhead l t d) : Tendsto (touringCosts μ F l t d f) atTop (𝓝 (fullFig μ F l t)):=by
 let oL:=(order_cost l).symm; let oT:=(order_cost t).symm
 rw [show fullFig μ F l t= fullFig μ F (ordered l) (ordered t) from integral_congr_ae (Eventually.of_forall fun i=> congrArg₂ (· * ·) (figures_perm _ h.sal oL) (figures_perm _ r.sal oT))]
 refine (p.clusters f g (perm_auction oL.symm h) (perm_auction oT.symm r) v (q.perm oL oT) (order_sal h.sal) (order_sal r.sal)).congr fun n=> (?_)
 unfold touringCosts postmark; let t' := ordered t; let l':= ordered l
 have hx(n:ℕ)(d:E4)(q:SweepAhead l t d):shipping f n (fun u=>meanFig μ F (l++moveCaps t u)) d=shipping f n (fun u=>meanFig μ F (l'++moveCaps t' u)) d:=by
    induction n generalizing d with
    | zero=> exact mean_perm (oL.append (oT.map _)) ((q.auction h r).sal)
    | succ n ih=> unfold shipping; congr 1; exact Finset.sum_congr rfl fun i _=> ih _ (q.more (ample_sick _ (g i)))
 congr 1; exact Finset.sum_congr rfl fun i _ => (hx i d q).symm
end cluster
end YM.SatinWFixed.Passage
open YM.SatinWFixed.Passage
#print axioms Album.clusters
#print axioms Album.clusters_any
#print axioms Album.ticket
