import YM.CF.DPress.FD.Tile.Warm
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Metric Filter SU MeasureTheory Ramp Row Frame
open scoped Topology BigOperators NNReal ENNReal Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {I K:Type*}[Fintype I][Fintype K]{m:ℕ}
namespace Warm
abbrev Assembly (S:Finset I)(F G:Ramp I m→ArrayF K)(r:ℕ)(b:ℝ):Prop:=∀ v⊂ S, v.card≤r → Seam (facet v) F G b
variable {S:Finset I}{F G H:Ramp I m→ArrayF K}{x y:Ramp I m}{a b:ℝ}{r:ℕ} (p:0<m)
include p
private lemma no_empty (u: x∈ facet S): 0<S.card:=by obtain ⟨i,v,h⟩:= exists_right p u; exact Finset.card_pos.mpr ⟨i,v⟩
lemma vacant (S:Finset I)(F G:Ramp I m→ ArrayF K) (a:ℝ):Assembly S F G 0 a:=by
 intro v _ t; have e(i:Ramp I m): i∉ facet v:= fun h=> not_lt_of_ge t (no_empty p h); exact ⟨fun _ v=>False.elim (e _ v),fun i v=>False.elim (e i v), fun x p=>False.elim (e _ p)⟩
lemma limUnit (x:Ramp I m)(t:x∈boundary S): x∈facet (supportT x):=⟨t.1,Finset.Subset.refl _⟩
lemma tap_core0 (b:ℝ)(u:0≤b)(t:∀ v⊂S,Seam (facet v) F G b):Seam (boundary S) F G (2*b+2*Row.rad):=by
 refine ⟨fun i v=> (t _ v.2).legal (limUnit p _ v),fun i v=> (t _ v.2).pay i (limUnit p _ v),?_⟩; have h:=Row.alive; exact Ramp.join_cost S p (show 0≤2*Row.rad from by positivity) u (C:=Frame K) (fun _ x _ y=> Frame.uniform x y) (fun i v=> (t _ v.2).shape (limUnit p _ v)) (fun u v=> (t _ v).e)
-- arbitrary U extends its Seam with common choice over U RHS.Speed from SU.
omit p
lemma edgeK (a b:ℝ)(p:0≤a)(q:0≤b): ∃ c:ℝ, b≤c∧∀ {I K:Type*} [Fintype I][Fintype K] (S:Finset I) (v: S.card ≤4) (m:ℕ)(h:0<m)(F G:Ramp I m→ArrayF K), (∃ G, Seam (facet S) F G a) → (∀ u⊂ S,Seam (facet u) F G b) → ∃ U, Seam (facet S) F U c∧EqOn U G (boundary S):=by
 obtain ⟨c,t,h⟩:=Ramp.budgetL (a+(2*b+2*Row.rad)); refine ⟨a+c+b,le_add_of_nonneg_left (by linarith),?_⟩; intro I K H H' S v m he F G Hp pT; obtain ⟨A,p'⟩:= Hp; let x:= facet (m:=m) S; let y:=boundary (m:=m) S; obtain ⟨f,i,j⟩:= Seam.lift (p'.more (show y⊆x from fun _=> border) a le_rfl) (tap_core0 he b q pT)
 obtain ⟨D,U,P⟩:= h S v m he f i; let g(i:Ramp I m):= sail (A i) (D i); refine ⟨g, ⟨p'.legal,fun i p=>?_ , fun i s j w=>?_⟩,?_⟩ -- charge uses a and c.
 · obtain ⟨u,v⟩:=p'.pay i p; exact ⟨u*D i,by rw [←sail_mul,dist_le_zero.mp v]; exact dist_self (g i) |>.le⟩
 · refine (move_cost (A:=A i) (p'.shape w) (D i) (D j)).trans ((add_le_add (p'.e i s j w) (U i s j w)).trans ?_); rw [←add_mul]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right q) δp
 intro i v; unfold g; rw [← P v]; exact j v
-- update G simultaneously for every U with |U|=r+1 . ∈ max.P. need Hull r-dimensional. value at x via own support.
lemma acclimate(S:Finset I)(F G:Ramp I m→ArrayF K)(r:ℕ)(a b:ℝ)(fa:Assembly S F G r a)(v:a≤b)(p:∀ U⊂ S,U.card=r+1→∃ G',Seam (facet U) F G' b ∧ EqOn G' G (boundary U)) : ∃ T, Assembly S F T (r+1) b:=by
 choose g u v' using p; let H(x):= supportT (m:=m) (I:=I) x; let Y(x):Prop:= H x ⊂ S ∧ (H x).card=r+1; let T(x):= if p:Y x then g (H x) p.1 p.2 x else G x
 refine ⟨T,?_⟩; intro V x y; rcases y.eq_or_lt with hp|hp
 · apply (u V x hp).congr; intro i v; change i∈facet V at v; by_cases w:H i=V; swap; · have hx: i∈boundary V:=⟨v.1, Finset.ssubset_iff_subset_ne.mpr ⟨v.2,w⟩⟩; have he:= Finset.card_lt_card hx.2; have h:¬Y i:=fun t=>Nat.ne_of_lt he (t.2.trans hp.symm); unfold T; rw [dif_neg h]; exact v' V x hp hx
   let μ : Y i:=by unfold Y; rw [w]; exact ⟨x,hp⟩
   unfold T; rw [dif_pos μ]; have hh(U V:Finset I)(e:U=V)(u:U⊂S)(v:U.card=r+1)(k:V⊂S)(p:V.card=r+1) :g V k p i=g U u v i:=by subst V; rfl
   exact hh (H i) V w μ.1 μ.2 x hp
 refine ((fa V x (by omega)).more (Set.Subset.refl _) b v).congr ?_; intro i t; unfold T; have hv:(H i).card ≤ V.card:= Finset.card_le_card (show H i⊆ V from t.2); rw [dif_neg]; exact fun p=> (Nat.ne_of_lt (hv.trans_lt hp)) p.2
private lemma step (n:ℕ)(h:n≤4)(a:ℝ)(p:0≤a):∃ b:ℝ, 0≤b∧∀ {I K:Type*}[Fintype I][Fintype K](S:Finset I)(m:ℕ),0 < m →∀ f:Ramp I m→ArrayF K,(∀ v⊂ S,v.card≤n →∃ g,Seam (facet v) f g a) →∃ g, Assembly S f g n b:=by
 induction n with
 |zero=> exact ⟨0,le_rfl,fun S m p f h=> ⟨f,vacant p S f f 0⟩⟩
 |succ n ih=>
    obtain ⟨b,h,V⟩:= ih (by omega); obtain ⟨c,q,Y⟩:=edgeK a b p h; refine ⟨c,h.trans q,?_⟩; intro I K i k S m p f t; obtain ⟨g,p'⟩:= V S m p f (fun u v t'=> t u v (by omega)); refine acclimate S f g n b c p' q (fun U v l=>Y U (by omega) m p f g (t U v l.le) (fun i w=> p' i (show i< S from lt_trans w v) (by have h:= Finset.card_lt_card w; omega))) -- tune Finset lt.
lemma boundary_ride (a:ℝ)(p:0≤a):∃ b:ℝ,0 ≤ b∧∀ {I K:Type*}[Fintype I][Fintype K](S:Finset I),S.card≤5→∀ (m:ℕ),0 < m →∀ f:Ramp I m→ArrayF K,(∀ v⊂ S,∃ g,Seam (facet v) f g a) →∃ g, Seam (boundary S) f g b:=by
 obtain ⟨b,h,g⟩:= step 4 le_rfl a p; refine ⟨2*b+2*Row.rad,(by have he:=Row.alive; positivity),?_⟩; intro I K i k S p m t f v; obtain ⟨T,w⟩:=g S m t f (fun j x _=>v j x); exact ⟨T,tap_core0 t b h (fun i v=> w i v (by have he:= Finset.card_lt_card v; omega))⟩

end Warm
end YM.CF.DPress.FD
