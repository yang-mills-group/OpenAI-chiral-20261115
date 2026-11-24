import YM.CF.BPress.Smooth.Extend
import YM.CF.Mesa.Gerund

/-!
Lipschitz SU fillings, as used for the B-gate frame construction. Using FiniteGaugeData's Mesa
implementation of the column bundle (in particular the punctured-sphere section `atlas`).
We prove the uniform Lipschitz conclusion already for **partial** boundary data
with the stated pairwise-Lipschitz hypothesis; this way the cube procedure needn't first
continuously interpolate between the discrete boundary values. Same ordering: costs independent
of the step reduction b and of the curvature.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Smooth
open Function Metric Filter Set Module MeasureTheory Mesa
open scoped Topology NNReal ENNReal ContDiff InnerProductSpace Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {Z : Type} [MetricSpace Z]
variable {n : ℕ}

def special (n:ℕ) := {A:Keys n| trueS A}
lemma special_compact (n:ℕ) : IsCompact (special n):=by
  rcases n with _|n; · exact Set.Subsingleton.isCompact (Set.subsingleton_of_subsingleton)
  refine IsCompact.inter_right ?_ (isClosed_eq (f:=Matrix.det) continuous_id.matrix_det continuous_const)
  apply isCompact_iff_compactSpace.mpr (Gauge.compactGaugeU n)
lemma dist_keys (u v w x:Keys n) (h:v∈special n) (g:w∈special n) :
    dist (u*w) (v*x) ≤ dist u v+dist w x := by
  rw [dist_eq_norm,dist_eq_norm,dist_eq_norm, show u*w-v*x=(u-v)*w+v*(w-x) by noncomm_ring]; apply (norm_add_le ..).trans_eq; rw [Gauge.frob_mul_eq _ _ (show w*star w=1 from (show trueS w from g).1.2), Gauge.mul_frob_eq _ _ (show _ from (show trueS v from h).1.1)]
lemma mul_cost {f g : Z→ Keys n} {S : Set Z} {K L:ℝ≥0} (h: MapsTo f S (special n)) (t : MapsTo g S (special n))
    (p : LipschitzOnWith K f S)(q : LipschitzOnWith L g S) : LipschitzOnWith (K+L) (fun x=>f x*g x) S := by
  apply LipschitzOnWith.of_dist_le_mul; intro a ha b hb; rw [NNReal.coe_add, add_mul]; exact (dist_keys _ _ _ _ (h hb) (t ha)).trans (add_le_add (p.dist_le_mul a ha b hb) (q.dist_le_mul a ha b hb))
lemma star_cost {f : Z → Keys n} {S : Set Z} {K:ℝ≥0} (h:LipschitzOnWith K f S) : LipschitzOnWith K (fun x=>star (f x)) S := by
  apply LipschitzOnWith.of_dist_le_mul; intro a ha b hb; rw [dist_eq_norm,← star_sub,norm_star, ← dist_eq_norm]; exact h.dist_le_mul a ha b hb

-- quantitative single column: if inputs avoid v by ε, can first fill sphere then compensate
-- entire extension stays in the punctured patch. Constant cost can here depend on v.
private lemma column_tool {T S : Set Z} (p : IsCompact T) (L:ℝ≥0)(s:S⊆T)
    (v : Ket (Fin (n+2))) (h:‖v‖=1) (ε : ℝ) (l : 0 < ε) :
    ∃ C : ℝ≥0, ∀ D⊆ S, D.Nonempty → ∀ f : Z → Ket (Fin (n+2)), LipschitzOnWith L f D →
    (∀ x∈ D, ‖f x‖=1 ∧ ε ≤ dist (f x) v) → ∃ F : Z → Keys (n+2),
    LipschitzOnWith C F T ∧ MapsTo F T (special _) ∧ EqOn f (shaft 0 ∘ F) D := by
  let i : Fin (n+2) := 0; obtain ⟨W,w,G,H⟩:= clear_extend v h T p L ε l; obtain ⟨ρ,R⟩:=Mesa.atlas i 1 (Ne.symm (Fin.succ_ne_zero (0:Fin (n+1)))) _ h
  let A:= sphere (0 : Ket (Fin (n+2))) 1 \ ball v w
  have V(u)(t:u∈A) : trueS (ρ u)∧ shaft i (ρ u)=u ∧ ContDiffAt ℝ 1 ρ u:=
      R u (by simpa using (show u∈sphere 0 1 from t.1)) (fun x=> t.2 (x ▸ mem_ball_self G))
  obtain ⟨K,h⟩:= lip_near (s:= A) ((isCompact_sphere ..).diff isOpen_ball) (fun x p=> (V _ p).2.2)
  refine ⟨K*W, fun Z l ne F L G=>?_ ⟩; obtain ⟨f,t,W,v⟩:= H Z (l.trans s) ne F L G; have he : MapsTo f T A:= fun i p=>⟨by simpa using (v i p).1, fun g=> not_lt.mpr (v i p).2 (mem_ball.mp g)⟩
  exact ⟨ρ ∘ f,h.comp t he,fun x p=>(V _ (he p)).1,fun x p=> (W p).trans (V _ (he (s (l p)))).2.1.symm⟩

theorem su_extension {T S : Set Z} (p : IsCompact T) (q : IsCompact S) (s:S⊆T) (h : dimH S <3) (n:ℕ)(L:ℝ≥0) :
    ∃ K:ℝ≥0, ∀ D ⊆ S, ∀ f: Z→ Keys (n+1), LipschitzOnWith L f D→MapsTo f D (special _)→
      ∃ F: Z→ Keys (n+1), LipschitzOnWith K F T ∧ MapsTo F T (special _) ∧ EqOn f F D := by
  induction n generalizing L with
  | zero=>
    refine ⟨0,fun D H f _ w=> ⟨fun _=>1,(LipschitzWith.const _).lipschitzOnWith,fun _ _=>suit_one,?_⟩⟩; intro i t; have ht: (f i).det=1:=(show trueS _ from w t).2; ext j k; fin_cases j; fin_cases k; simpa using ht
  | succ n ih=>
    let N:=n+1+1; let TT:=Ket (Fin N); let c : Fin N:=0; obtain ⟨C,X⟩:=lip_near (special_compact N) (f:=shaft c) (fun i _=> shaft_smooth c i)
    let v:=shaft c (1 : Keys N); have hu:‖v‖=1:=shaft_norm _ suit_one _
    obtain ⟨δ,u,x,V⟩:= avoidance v hu S q (C*L) (n:=2*n+3) (by
      rw [← Module.finrank_mul_finrank ℝ ℂ,finrank_euclideanSpace,Fintype.card_fin,Complex.finrank_real_complex]; unfold N; ring) (h.trans_le (by exact_mod_cast (show 3≤2*n+3 by omega)))
    choose c' T' using fun w : sphere (0:TT) 1 => column_tool p (C*L) s w.val (by simpa using w.property) δ x
    let P:=u.sup c'; obtain ⟨S₁,H₁⟩:=lip_near (special_compact N) (f:=aside) (fun _ _=> aside_cont _); obtain ⟨S₂,H₂⟩:=lip_near (special_compact (n+1)) (f:=layer) (fun _ _=> layer_cont _)
    obtain ⟨A,Y⟩:= ih (S₁*(P+L)); refine ⟨P+ S₂*A,?_⟩; intro D H f E G; rcases D.eq_empty_or_nonempty with d|d; · subst D; exact ⟨fun _=>1,(LipschitzWith.const' _).lipschitzOnWith,fun _ _=> suit_one,Set.eqOn_empty ..⟩
    let a:=shaft c ∘ f; have ht : LipschitzOnWith (C*L) a D:= X.comp E G; have hr(i)(p:i∈D):‖a i‖=1:=shaft_norm _ (G p) _
    obtain ⟨i,k,w⟩:=V D H d a ht hr; obtain ⟨B,t,hB,Tb⟩:= T' i D H d _ ht (fun x v=>⟨hr _ v,w _ v⟩); have hp:= t.weaken (show c' i ≤ P from Finset.le_sup (f:=c') k)
    let F x:= star (B x)*f x; have he (i)(p:i∈D) : F i∈special N ∧ F i=layer (aside (F i)):= by
      have hz : trueS (B i) := hB (s (H p)); have ht:trueS (F i):= suit_mul (suit_star hz) (G p); refine ⟨ht, layer_flat ht ?_⟩
      unfold F; rw [shaft_back, show shaft 0 (f i)=shaft 0 (B i) from Tb p,←shaft_back, show star (B i)*B i=1 from hz.1.1]
    obtain ⟨F',R,U,T⟩:= Y D H (aside ∘ F) (H₁.comp (mul_cost (g:=f) (fun i p=> (suit_star (hB (s (H p))))) G (star_cost (hp.mono (H.trans s))) E) (fun i p=>(he i p).1)) (fun i p=> (suit_layer _).mp ((he i p).2 ▸ (he i p).1)) -- substitution tune
    let L' := layer ∘ F'
    have hu : MapsTo L' _ (special N):= fun i p=>(suit_layer _).mpr (U p)
    exact ⟨fun x=> (B x)*L' x,mul_cost hB hu hp (H₂.comp R U),fun i p=> suit_mul (hB p) (hu p),fun i p=> by dsimp only; rw [show L' i= F i from (congrArg layer (T p).symm).trans (he i p).2.symm]; unfold F; rw [← mul_assoc, show B i *star (B i)=1 from (show trueS _ from hB (s (H p))).1.2,one_mul]⟩
end YM.CF.BPress.Smooth
