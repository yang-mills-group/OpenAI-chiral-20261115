import YM.SU5.Reconstruction.Anvil.Merge
/-! # Embed the Anvil disc as a true lens for spatial slits. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace OS Semigroup Finset ConePrice
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
namespace Price
abbrev extend (P: Price)(T:ℝ) :Price:={P with margin:=T}
def compares (P:Price)(v:Bool) (x:ℝ): ℝ := if v then x+P.second-(P.first+ P.firstWidth) else P.first - (P.second+P.secondWidth)-x
lemma window_syntax (a:Axis)(P:Price)(z:Wage):
 (P.permeates a true z ↔ 0 < P.first+ P.margin ∧ ‖rimPay a (Deeper z)‖ < P.compares true (z a).re ∧ ‖rimPay a (Deeper z)‖ < P.margin-(P.second+P.secondWidth)-(z a).re)∧
 (P.permeates a false z ↔ ‖rimPay a (Deeper z)‖ < (z a).re+(P.second+ P.margin) ∧ ‖rimPay a (Deeper z)‖ < P.compares false (z a).re ∧ 0 < P.margin-(P.first+P.firstWidth)):=by simp only [permeates]; rw [P.commuter a true,P.commuter a false]; simp only [entry,leaves,compares, if_true,reduceCtorEq,if_false,← facet_t, Tunnel, mem_setOf_eq, deeper_sub,deeper_add,rimPay_sub,rimPay_add,grace,rimPay_zero]; simp [onlyTime, sub_eq_add_neg, add_assoc]
lemma charge_upwards (a:Axis)(Q:Price)(x y:ℝ)(p:x≤y)(w:Bool)(z:Wage)(q:(Q.extend x).permeates a w z) : (Q.extend y).permeates a w z := by
 cases w
 · rw [(window_syntax a _ z).2] at q ⊢; obtain ⟨a,b,c⟩:=q; exact ⟨by dsimp [extend] at a ⊢; linarith [a],b,by dsimp [extend] at c ⊢; linarith [c]⟩
 rw [(window_syntax a _ z).1] at q ⊢; obtain ⟨a,b,c⟩:=q; exact ⟨by dsimp [extend] at a ⊢; linarith [a],b,by dsimp [extend] at c ⊢; linarith [c]⟩
lemma entry_cost (a:Axis)(Q:Price)(w:Bool)(z:Wage)(q:‖rimPay a (Deeper z)‖ < Q.compares w (z a).re): ∀ᶠ T:ℝ in atTop,(Q.extend T).permeates a w z:= by
 filter_upwards [eventually_gt_atTop (-Q.first), eventually_gt_atTop (‖rimPay a (Deeper z)‖ + Q.second+ Q.secondWidth+(z a).re), eventually_gt_atTop (Q.first+ Q.firstWidth),eventually_gt_atTop (‖rimPay a (Deeper z)‖-Q.second-(z a).re)] with t hf h1 h2 h3
 cases w
 · exact (window_syntax a _ z).2.mpr ⟨by dsimp only [extend]; linarith,q,h2|> sub_pos.mpr⟩ -- tune
 exact (window_syntax a _ z).1.mpr ⟨by dsimp only [extend]; linarith,q,by dsimp only [extend]; linarith⟩
end Price
abbrev LedgerRide (a:Axis)(z:Wage) (t:ℂ): Wage := z+ onlyTime a t
@[simp] lemma rides_repeat (a:Axis)(z:Wage)(s t:ℂ): LedgerRide a (LedgerRide a z s) t= LedgerRide a z (s+t):=by unfold LedgerRide; rw [single_compensate,add_assoc]
lemma ride_h (a:Axis)(z:Wage)(D:Set ℂ)(i:Axis) : DifferentiableOn ℂ (fun t=> LedgerRide a z t i) D:= by by_cases p:i=a<;> simp [LedgerRide,onlyTime,p]<;> fun_prop
-- time orientation here negative i is always posed with same meaning. Support
variable (a : Axis)(x:Meter)(b:ℝ)
abbrev aim := facet x+onlyTime a (sideways b)
structure Outlook where
 X : ℂ→Wage
 atSpot : X 0=aim a x b
 life (i:ℂ)(h:i∈Pane): ContinuousAt X i
 pulse (i:Axis)(z:ℂ)(h:z∈Well): DifferentiableAt ℂ (fun p=> X p i) z
-- rest of story: use only K positively compared, may mix order k.
variable {K: Finset Axis}
-- tests use orientations Price including real widths rented (no real of mark stamp dependency). target comm at spatial shift x (with x a=0). lens from ISSUANCE across all compare-containing.
structure Terrain (a:Axis)(K:Finset Axis) where
 P : K→Price
 first : K→ Bool -- True starts A order (A before B)
 enough (k:↥K) : k.val≠a
namespace Terrain
variable {a} (P:Terrain a K)
abbrev gap (k: K):= (P.P k).compares (P.first k) (x k.val)
variable (V : Festum (P.gap x) b)
local notation "A"=> P.gap x
local notation "I" => Complex.I
def raiseLens (z:ℂ): Wage:= fun i=> if h : i ∈ K then let k:↥K:=⟨i,h⟩; if P.first k then (x i:ℂ)+(V.g k z - (A k:ℂ)) else (x i:ℂ) + ((A k:ℂ) - V.g k z) else if i = a then V.φ z else x i
local notation "F"=> raiseLens x b P V
lemma centerLens (z:ℂ): F z a= V.φ z:= by simp [raiseLens,show a ∉ K from fun h=> P.enough ⟨a,h⟩ rfl]
lemma compareLens (z:ℂ)(k:K): F z k.val=(if P.first k then (x k.val:ℂ)+(V.g k z-(A k:ℂ)) else (x k.val:ℂ)+((A k:ℂ)-V.g k z)) := by simp [raiseLens,k.property]
lemma expense (i:Axis)(z:ℂ)(h:z∈Pane): ContinuousAt (fun z=>F z i) z:= by
 by_cases p:i∈K; · let k:↥K:=⟨i,p⟩; change ContinuousAt (fun z=> F z k.val) z; simp_rw [compareLens x b P V]; cases P.first k; exact continuousAt_const.add (continuousAt_const.sub ((V.enters h).2 _)); exact continuousAt_const.add (((V.enters h).2 _).sub continuousAt_const)
 by_cases u:i=a; · subst i; simp_rw [centerLens]; exact (V.enters h).1
 have t: (fun z=> F z i) = fun _=> (x i:ℂ):= funext fun _=>by simp [raiseLens,p,u]
 rw [t]; exact continuousAt_const
lemma totals (i:Axis)(z:ℂ)(h:z∈Well): DifferentiableAt ℂ (fun z=>F z i) z:= by
 by_cases p:i∈K; · let k:↥K:=⟨i,p⟩; change DifferentiableAt ℂ (fun z=> F z k.val) z; simp_rw [compareLens x b P V]; cases P.first k; exact (differentiableAt_const _).add ((differentiableAt_const _).sub ((V.hol h).2 _)); exact (differentiableAt_const _).add (((V.hol h).2 _).sub (differentiableAt_const _))
 by_cases u:i=a; · subst i; simp_rw [centerLens]; exact (V.hol h).1
 have t: (fun z=> F z i) = fun _=> (x i:ℂ):= funext fun _=>by simp [raiseLens,p,u]
 rw [t]; exact (differentiableAt_const _)
lemma makesLens (hx:x a=0) : F 0= aim a x b:= by
 ext i : 1; by_cases p:i∈K; · let k:↥K:=⟨i,p⟩; change F 0 k.val= aim a x b k.val; simp [compareLens x b P V,V.at_place,aim,P.enough k,onlyTime]
 by_cases z:i=a; · subst i; simp [aim, centerLens,V.atBase,hx,sideways,onlyTime]
 simp [aim,z,p,raiseLens,onlyTime]
private lemma imagCost (i:K)(z:ℂ) : (F z i.val).im^2=(V.g i z).im^2:=by rw [compareLens]; cases P.first i <;> simp
private lemma totalIm (i:K)(z:ℂ): ‖rimPay i.val (Deeper (F z))‖^2=(V.φ z).im^2+∑ j∈ Finset.univ.erase i,(V.g j z).im^2:= by
 let f(k:Axis):= (F z k).im^2
 rw [rimPay_norm]; have h: a ∉ K:= fun h=> P.enough ⟨a,h⟩ rfl
 have e:f a=(V.φ z).im^2:= congrArg (fun z:ℂ=>z.im^2) (centerLens ..)
 change ∑ k∈ Finset.univ.erase i.val,f k=_
 let p(k:Axis):ℝ:=if k=i.val then 0 else f k
 have W:∑ k:↥K,p k.val=∑ j∈ Finset.univ.erase i,(V.g j z).im^2:= by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),show p i.val=0 from if_pos rfl, add_zero]; refine Finset.sum_congr rfl fun j hj=>?_ ; exact (if_neg (fun b=> ne_of_mem_erase hj (Subtype.ext b))).trans (P.imagCost x b V j z) -- notation shadow
 have Y:∑ k∈ K,p k=∑ k:↥K,p k.val:= by symm; exact K.sum_attach p
 rw [←W,←Y,←e]; trans ∑ k∈ (Finset.univ:Finset Axis),p k
 · rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i.val), show p i.val= 0 from if_pos rfl, add_zero]; exact Finset.sum_congr rfl (fun k hk=> Eq.symm (if_neg (ne_of_mem_erase hk)))
 rw [← show p a= f a from if_neg (P.enough i).symm, ← Finset.sum_insert h]; symm; refine Finset.sum_subset (Finset.subset_univ _) fun b t u=>?_ -- shadows b
 have hb:= mem_insert.not.mp u; simp [p]; have H: f b=0:=by obtain ⟨r,s⟩:= not_or.mp hb; simp [f,raiseLens,s,r]
 simp [p,H]
lemma arcScan (z:ℂ)(v:z∈Rim) : ∃ i:K, ‖rimPay i.val (Deeper (F z))‖ < (P.P i).compares (P.first i) (F z i.val).re:= by
 obtain ⟨k,h,r⟩:=V.relies z v; refine ⟨k,?_⟩
 rw [← totalIm x b P V k z] at r; rw [show (P.P k).compares (P.first k) (F z k.val).re= (V.g k z).re from ?_]; exact lt_of_pow_lt_pow_left₀ 2 h.le r
 rw [compareLens]; simp only [gap, Price.compares]; cases P.first k <;> simp <;> ring
end Terrain
end YM.Anvil
