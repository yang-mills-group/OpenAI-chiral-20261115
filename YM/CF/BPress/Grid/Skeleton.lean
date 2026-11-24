import YM.CF.BPress.Grid.Fiber
/-!
Dimension induction on the periodic r*b cell skeleton. Step for eq:B-start.
Works also on subcomplexes for lem:B-moX.
-/
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.CF.BPress.Grid
open Function Finset Lattice MeasureTheory Filter
open scoped BigOperators Topology NNReal Classical
variable {G:Gauge} {d : ℕ} {s : Side} {k:Tiling s}
variable {F : Type} [MetricSpace F] [Nonempty F][CompactSpace F] [MeasurableSpace F][BorelSpace F]
namespace Entity
def inner (J:Entity k d) (x:Space d s) := ∃ a, J.Valid a ∧ ¬J.Boundary a ∧ J.heart a=x
lemma inner_rank (J:Entity k d) {x:Space d s}(p:J.inner x) : rankSet k x=J.axes:= by obtain ⟨a,t,v,rfl⟩:=p; exact (rank_eq k J t).2 v -- tune
lemma inner_only {J J' : Entity k d}{x:Space d s}(p:J.inner x)(h:J'.inner x): J=J':=by obtain ⟨a,x,v,rfl⟩:=p; obtain ⟨b,t,u,g⟩:=h; exact interior_unique _ _ _ x t v u g.symm
lemma rank_boundary (J:Entity k d){a:Coord d}(p:J.Valid a)(h:J.Boundary a): (rankSet k (J.heart a)).card < J.axes.card:= Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨rank_le k J p, fun e=> (rank_eq k J p).mp e h⟩)
end Entity

def Graded (X:Finset (Entity k d)):Prop:=∀ i∈ X,∀ j∈i.axes,∀ t,i.wall j t∈X
lemma Graded.fixed {X:Finset (Entity k d)} (H: Graded X) (J:Entity k d) (e:J∈X) (x:Space d s) (p:J.contains x): ∃ i ∈ X,i.inner x:=by
 suffices ∀ n:ℕ, ∀ i∈ X, i.contains x → i.axes.card ≤ n → ∃ i∈ X,i.inner x from this _ J e p le_rfl; intro n; induction n using Nat.strong_induction_on with| h n ih=>
   intro i h y w; obtain ⟨a,p,g⟩:=y; by_cases z:i.Boundary a; swap; · exact ⟨i,h,a,p,z,g⟩
   obtain ⟨j,t,d⟩:=z; have he:= i.wall_coord d p; have hz:= i.wall_mo d.1 t; exact ih _ (show (i.wall j t).axes.card<n by omega) _ (H i h j d.1 t) ⟨_,he.1,he.2.trans g⟩ le_rfl

namespace Delivery
open Entity
variable (D : Delivery G d F)
-- issue all steps except on fixed entities. W read at r-grid sites.
variable (J:Entity k d)
-- Selector over entity inputs; explicitly truncate to hull sites, whether or NOT following the hypotheses.
private def overwrite (g : Fabric d s F)(x:Space d s) : F:= if J.contains x then g x else Classical.arbitrary F
private def slice (W : GaugeField G d s)(x:WalkEdge d s) : G.El := if J.contains x.1 then W x else 1
structure Sizer (K:ℝ) where
  updateF : Finset (Entity k d) → Finset (Entity k d) → GaugeField G d s → Fabric d s F → Fabric d s F
-- probably unused
private lemma selected (K:ℝ) : ∃ T : GaugeField G d s × Fabric d s F → Fabric d s F,
    Measurable T ∧ (∀ W f, (∃ z, keep J f z ∧ D.Speed J W z K) → keep J f (T (W,f)) ∧ D.Speed J W (T (W,f)) K) ∧ ∀ x y, (∀ p,J.contains p.1→x.1 p=y.1 p) → (∀ p,J.contains p→ x.2 p=y.2 p) → T x=T y := by
  let P:= {(x:(GaugeField G d s × Fabric d s F) × Fabric d s F)| keep J x.1.2 x.2 ∧ D.Speed J x.1.1 x.2 K}
  have h:IsClosed P:=by
    unfold P Speed keep; simp_rw [Set.setOf_and,Set.setOf_forall]; apply IsClosed.inter
    · exact isClosed_iInter (fun i=> isClosed_iInter fun _=> isClosed_iInter fun _=> isClosed_eq (by fun_prop) (by fun_prop))
    refine isClosed_iInter fun i=> isClosed_iInter fun j=> isClosed_iInter fun _=>?_ ; unfold speed along; refine isClosed_le (Continuous.dist ?_ (by fun_prop)) continuous_const; exact D.cont.comp (Continuous.prodMk (by fun_prop) (by fun_prop)) -- tune
  obtain ⟨T,t,u⟩:=choose_if_closed P h
  let Q(x:(GaugeField G d s × Fabric d s F)):(GaugeField G d s × Fabric d s F):= (slice J x.1,overwrite J x.2)
  have he(x:(GaugeField G d s × Fabric d s F))(y) : (Q x,y)∈ P ↔ (x,y)∈P:= by
    change (_ ∧ _)↔(_ ∧ _); unfold Speed keep Q; dsimp only; unfold speed along slice overwrite; congr! 5 with i p b <;> try rfl -- tune
    · rw [if_pos (show J.contains (J.heart i) from ⟨_,p,rfl⟩)]
    rename_i a i p; rw [if_pos (show J.contains (J.heart a) from ⟨_,J.valid_tick p,rfl⟩)]
  refine ⟨T ∘ Q, t.comp (Measurable.prodMk ?_ ?_),fun W f g=>?_,fun x y p g=>congrArg T ?_⟩
  · apply measurable_pi_lambda; intro i; unfold slice; split; exact (measurable_pi_apply i).comp measurable_fst; exact measurable_const
  · apply measurable_pi_lambda; intro i; unfold overwrite; split; exact (measurable_pi_apply i).comp measurable_snd; exact measurable_const
  · exact (he (W,f) _).mp (u _ (g.imp fun i p=>(he (W,f) i).mpr p))
  apply Prod.ext
  · ext1 i; change slice J x.1 i=slice J y.1 i; unfold slice; split; exact p _ ‹_›; rfl
  ext1 i; change overwrite J x.2 i=overwrite J y.2 i; unfold overwrite; split; exact g _ ‹_›; rfl

-- masked read from entities at prescribed dim; no summing exponential gauge weights.
abbrev FabrReq(G:Gauge)(d:ℕ)(s:Side)(F:Type):= GaugeField G d s × Fabric d s F
private def changeS (v:Entity k d → FabrReq G d s F → Fabric d s F) (n:ℕ) (A X : Finset (Entity k d)) (w:FabrReq G d s F) (x : Space d s):F :=
  if h:∃ i∈A,i∉ X∧i.axes.card=n ∧ i.inner x then v h.choose w x else w.2 x
private lemma changeS_apply (v: Entity k d → FabrReq G d s F → Fabric d s F) (n:ℕ) (A X : Finset (Entity k d))(w : FabrReq G d s F)(x:Space d s) (a:J∈A)(h:J∉X)(e:J.axes.card=n)(p:J.inner x) :
    changeS v n A X w x=v J w x:=by
  unfold changeS; split; next g => rw [inner_only g.choose_spec.2.2.2 p]
  next g=> exact (g ⟨_,a,h,e,p⟩).elim

-- collect touches: queries at mesh x are local in coarse distance GR! Need for actual dependency budgets.
def Knows (k:Tiling s) (d:ℕ) {G:Gauge}{F:Type} (a:Finset (Entity k d)→ Finset (Entity k d)→ FabrReq G d s F→ Fabric d s F) (r:ℕ) : Prop:= ∀ A X B Y W V x,
   x∈mesh k.r.val → (∀ (i:Entity k d), delta x i.origin≤ r → ((i∈A ↔ i∈B) ∧ (i∈X↔ i∈Y))) →
   (∀ i, i.1∈mesh k.r.val → delta x i.1≤ r→ W.1 i=V.1 i) →
   (∀ i, i∈mesh k.r.val → delta x i≤ r → W.2 i=V.2 i) →
   a A X W x=a B Y V x

private lemma change_recognizes
    (v: Entity k d → FabrReq G d s F → Fabric d s F)
    (h:∀ (J:Entity k d) x y, (∀ p,J.contains p.1→x.1 p=y.1 p) → (∀ p,J.contains p→ x.2 p=y.2 p) → v J x=v J y) (n:ℕ): Knows k d (changeS v n) (2*k.R) := by
  intro A X B Y W V x e p l L
  have hx (i:Entity k d)(g:i.inner x): delta x i.origin ≤ k.R:= by obtain ⟨a,u,t,e⟩:=g; rw [←e,delta_comm]; exact i.span u
  have he(y) (J:Entity k d)(g:J.inner x)(h:J.contains y): y∈mesh k.r.val ∧ delta x y≤2*k.R:=by obtain ⟨a,u,rfl⟩:=h; exact ⟨J.on_grid _,(delta_triangle _ J.origin _).trans ((add_le_add (hx J g) (J.span u)).trans_eq (two_mul ..|>.symm))⟩
  have hz:∀ i:Entity k d, i∈ A∧i∉X∧i.axes.card=n∧i.inner x ↔ i∈B∧i∉Y∧i.axes.card=n∧i.inner x:=by
    intro i; by_cases g:i.inner x; have hi:=hx i g; obtain ⟨u,t⟩:=p i (by omega); tauto; tauto
  by_cases q: ∃ i∈A,i∉X∧ i.axes.card=n∧i.inner x
  · obtain ⟨i,m,p,P'⟩ := q; have k:= P'.2; obtain ⟨M,a,g,h'⟩ := (hz i).mp ⟨m,p,P'⟩; rw [changeS_apply i v n _ _ W x m p g k,changeS_apply i v n _ _ V x M a g k,h i W V (fun p v=> l _ (he _ _ k v).1 (he _ _ k v).2) (fun p v=> L _ (he _ _ k v).1 (he _ _ k v).2)]
  have z:= exists_congr hz; unfold changeS; rw [dif_neg q,dif_neg (mt z.mpr q)]; exact L _ e (by simp)

lemma Knows.comp {u v:ℕ}{a b : Finset (Entity k d)→ Finset (Entity k d)→ FabrReq G d s F→ Fabric d s F} (p : Knows k d a u)(q : Knows k d b v): Knows k d (fun A X (W:FabrReq G d s F)=> b A X (W.1,a A X W)) (v+u):=by
  intro A X B Y W V x e k l h; refine q _ _ _ _ _ _ _ e (fun i p=> k i (by omega)) (fun i t p=> l i t (by omega)) (fun i t p'=> p _ _ _ _ _ _ _ t (fun j r=> k _ ((delta_triangle _ i _).trans (add_le_add p' r))) (fun i' s u=> l i' s ((delta_triangle _ i _).trans (add_le_add p' u))) (fun j t' r=> h _ t' ((delta_triangle _ i _).trans (add_le_add p' r))))
-- keep rank across all smaller accepted steps, regardless of whether boundary labels match from neighbor
private lemma change_small (v: Entity k d → FabrReq G d s F → Fabric d s F) (n:ℕ) (A X : Finset (Entity k d))(w : FabrReq G d s F)(x:Space d s) (g:(rankSet k x).card < n) : changeS v n A X w x=w.2 x:= by
  unfold changeS; rw [dif_neg]; rintro ⟨i,_,_,p,e⟩; rw [i.inner_rank e,p] at g; omega
private lemma change_fixed (v: Entity k d → FabrReq G d s F → Fabric d s F) (n:ℕ) (A X : Finset (Entity k d)) (h:Graded X)(w : FabrReq G d s F)(x:Space d s)(i:Entity k d)(p:i∈X)(e:i.contains x): changeS v n A X w x=w.2 x:= by
 unfold changeS; rw [dif_neg]; obtain ⟨j,r,t⟩:= h.fixed i p x e; rintro ⟨l,_,g,u,v⟩; rw [inner_only v t] at g; exact g r

-- simp time later. transfer speed from wall
private lemma Speed.relax (K L:ℝ)(t:K≤L)(W:GaugeField G d s)(f g:Fabric d s F)(x : D.Speed J W f K) (v:∀ a,J.Valid a→ f (J.heart a)=g (J.heart a)): D.Speed J W g L:=by
 intro a i p; apply (div_le_div_of_nonneg_right t (by positivity : (0:ℝ) ≤ k.b.val)).trans'; unfold speed; rw [← v a (J.valid_tick p),← v _ p]; exact x a i p
lemma prior (W : GaugeField G d s) (f:Fabric d s F) (L:ℝ) (h:∀ i∈J.axes,∀ t, D.Speed (J.wall i t) W f L): D.Before J W f L:=by
 intro a i p j t x y; have a1:= J.wall_coord x (J.valid_tick p); have a2:= J.wall_coord y p; have he:i≠j:=fun g=> by
    have e := x.2.trans y.2.symm; rw [←g,tick_self] at e; omega
 have ht:= (show Function.update (tick a i) j 0= tick (Function.update a j 0) i from by ext l; by_cases u:l=i <;> by_cases v:l=j <;> simp_all); rw [ht] at a2; have ht:= h j x.1 t _ i a2.1; unfold speed along at *; rwa [a2.2,a1.2] at ht

def Reach (n:ℕ) (k:Tiling s) (L Z:ℝ) (T:Finset (Entity k d)→ Finset (Entity k d)→ FabrReq G d s F → Fabric d s F): Prop :=
 ∀ (A X : Finset (Entity k d)), Graded X → Graded A → X ⊆ A→ ∀ W f,
 (∀ i∈A,i.flat W ((k.b.val:ℝ)^2)⁻¹) → (∀ i∈X, D.Speed i W f L) →
 (∀ i∈A,i.axes.card ≤ n → D.Speed i W (T A X (W,f)) Z) ∧
 (∀ i∈X,∀ a,i.Valid a→ (T A X (W,f)) (i.heart a)= f (i.heart a)) ∧ ∀ i, i∈mesh k.R → (T A X (W,f)) i=f i

private lemma step_B (L:ℝ)(p:0≤L)(n:ℕ) : ∃ Z:ℝ,L≤Z ∧ ∀ s:Side,∀ k:Tiling s,∃ T, D.Reach n k L Z T ∧ (∀ A X, Measurable (T A X)) ∧ Knows k d T (n*(2*k.R)):= by
 induction n with
 | zero =>
    refine ⟨_,le_refl L,fun s k=>⟨fun _ _ x=>x.2,?_, fun _ _=>measurable_snd,?_⟩⟩ -- tune
    · intro A X _ _ _ W f _ _; refine ⟨fun i _ t a j u=>?_,fun _ _ _ _=>rfl,fun _ _=>rfl⟩; exfalso; have hh:=i.dim_off u (i:=j) (by rw [card_eq_zero.mp (Nat.eq_zero_of_le_zero t)]; simp); rw [tick_self] at hh; omega
    intro A X B Y W V x e _ _ h; exact h x e (by simp)
 | succ n ih=>
    obtain ⟨v,w,H⟩:= ih; obtain ⟨Z,g,Y⟩:= D.grant_entity v (p.trans w); refine ⟨Z,w.trans g,fun s k=>?_⟩
    obtain ⟨T,r,hT,Lq⟩:= H s k; choose F' hf Fq using fun J:Entity k d=> selected D J Z
    let u:= changeS F' (n+1); refine ⟨fun A X (x:FabrReq G d s F)=> u A X (x.1,T A X x),?_,?_,?_⟩
    · intro A X h k' z W f e b
      obtain ⟨y,tU,bU⟩:= r A X h k' z W f e b; let o:= T A X (W,f); let g':= u A X (W,o)
      refine ⟨?_,fun i l t m=> (change_fixed _ _ _ _ h (W,o) _ _ l ⟨_,m,rfl⟩).trans (tU i l t m),?_⟩
      · intro i t l; change D.Speed i W g' Z; rcases lt_or_eq_of_le l with a|a
        · apply Speed.relax D i v Z g W o _ (y _ t (by omega)); intro w q; exact (change_small _ _ _ _ (W,o) _ (lt_of_le_of_lt (card_le_card (rank_le k i q)) a)).symm
        by_cases c:i ∈ X
        · apply Speed.relax D i L Z (le_trans w g) W _ _ (b i c); intro w q; exact ((change_fixed _ _ _ _ h (W,o) _ _ c ⟨_,q,rfl⟩).trans (tU i c w q)).symm
        obtain ⟨P,Q⟩:= (Fq i).1 W o (Y s k i W (e _ t) o (D.prior i W o v (fun j p x=> y _ (k' _ t _ p x) (by have ht:=i.wall_mo p x; omega))))
        apply Speed.relax D i Z Z le_rfl W _ _ Q; intro v l; by_cases u:i.Boundary v; rw [P v l u]; exact (change_small _ _ _ _ (W,o) _ ((i.rank_boundary l u).trans_le (le_of_eq a))).symm; exact (changeS_apply i _ _ _ _ (W,o) _ t c a ⟨_,l,u,rfl⟩).symm
      intro i p; have e: rankSet k i=∅:= by ext x; simpa [rankSet] using p x
      exact (change_small _ _ _ _ (W,o) i (by rw [e,card_empty]; omega)).trans (bU i p)
    · intro A X; apply Measurable.comp (g:=fun w=> u A X w) (f:=fun w=> (w.1,T A X w)) _ (measurable_fst.prodMk (hT A X)); apply measurable_pi_lambda; intro x; unfold u changeS; split; next h=> exact (measurable_pi_apply x).comp (hf _)
      next h=> exact (measurable_pi_apply x).comp measurable_snd
    rw [add_mul,one_mul,add_comm (n*_)]; exact Lq.comp (change_recognizes _ (fun i=> (Fq i).2) _)

theorem build (L:ℝ)(t:0≤L): ∃ Z:ℝ,L≤Z ∧ ∀ s:Side,∀ k:Tiling s,∃ T, D.Reach d k L Z T ∧ (∀ A X,Measurable (T A X)) ∧ Knows k d T (d*(2*k.R)):= step_B D L t d
end Delivery
end YM.CF.BPress.Grid
