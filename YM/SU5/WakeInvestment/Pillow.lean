import YM.SU5.WakeInvestment.Penny
import YM.SU5.WakeInvestment.Layout
import YM.SU5.WakeInvestment.Gate

/-!
Cost ledger of any $z_i(F_i-g_i)$, actual after shear, local polynomial after taking a root.
At this test never estimate tilt energy by the norm of the whole one-particle shift (growing as
period is removed). Combine `Contracts` etc Hilbert pricing through those layouts and degrees.
Keep the estimates even for using *any* scalar later in the exponential query (under the
modulus constraint at every Saber).
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.WakeInvestment
open Function Set Filter Fock Lattice Finset NormedSpace
open Papyrus Papyrus.Franc Lat Fir Ember Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N:Side} {M:Tulip.Male} {j n:ℕ} {I:Type*} [LinearOrder I] [Fintype I] [Nonempty I]
variable {S T:Shaft I} {Q:Op I} (P: Op I) {t z u ε L :ℝ}

private lemma pad_wing (p:IsStarProjection Q)(x : |t| ≤ 1) (A B:Op I) (c:ColumnDeal (A-B) ε) : ColumnDeal (oneTilt Q t * A-oneTilt Q t*B) (tiltBound*ε):=by
  rw [←mul_sub]; constructor; intro i; rw [act_mul]; apply (Flare.opy ..).trans; exact mul_le_mul ((oneTilt_cap p t).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone x) zero_le_two)) (c.all i) (norm_nonneg _) tiltBound_pos.le

omit [Nonempty I] in
private lemma pillow_fold (p:IsStarProjection Q)(x : |t| ≤ 1) (A : Op I)(c: ‖A‖ ≤ L): ‖oneTilt Q t*A‖ ≤ tiltBound*L :=
 (norm_mul_le ..).trans (mul_le_mul ((oneTilt_cap p t).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone x) zero_le_two)) c (norm_nonneg _) tiltBound_pos.le)

local notation "ΩK" => spar j M (1 : Pane N)
def billWhole (L:ℝ) := tiltBound*(1+L)
lemma pillow_high (p:IsStarProjection Q)(e:Pillow S T L ε) (ht: |t| ≤ 1) : Pillow (weighted Q t S) (weighted Q t T) (tiltBound*L) (tiltBound*ε):=by
  constructor
  · intro i; cases i; · exact pad_wing p ht _ _ (e.flare false)
    unfold weighted mount; simp only [↓reduceIte,Shaft.foldC,star_mul]; unfold tiltShaft; rw [(oneTilt_self p _).star_eq]
    exact pad_wing p ((abs_neg t) ▸ ht) _ _ (e.flare true)
  intro i; cases i; · exact pillow_fold p ht _ (e.pose false)
  unfold weighted mount; simp only [↓reduceIte,Shaft.foldC,star_mul]; unfold tiltShaft; rw [(oneTilt_self p _).star_eq]; exact pillow_fold p ((abs_neg t) ▸ ht) _ (e.pose true)

lemma pillow_schedule (j:ℕ)(h:1≤j) : ∃ C:ℝ, 0<C∧ ∀ (ε:ℝ) (k:ℕ),0<ε → 1 ≤ (k:ℝ)*(ε^2/C)^2 →
    ∀ (N:Side) (M:Tulip.Male) (p:IsStarProjection (spar j M (1:Pane N))), Pillow (shear h p) (Saber (B:=tickA N) p k) (1+(k:ℝ)) ε:= by
  obtain ⟨C,p,a⟩:= approximate_saber j h; refine ⟨C,p,fun ε k q w N M t=>?_⟩
  obtain ⟨f,g⟩:= a ε k q w N M t; obtain ⟨u,hv⟩:=counting_Saber t (Cascade.plus_P N) k
  constructor
  · intro b; cases b; exact f; exact g
  intro b; cases b; exact u
  exact (norm_star ..).trans_le hv

def fee (K:ℝ)(m:ℕ)(L k ε σ:ℝ):= ((tiltBound*L)^2+(tiltBound*L)^2)*(K*wordToll k m)^2 + tiltBound*ε*K*wordToll k m+2*σ^2
omit [Nonempty I] in
lemma flat_part (p:IsStarProjection P)(S:Shaft I)(y:Wave I)(h:Sea P y)(F:FC I) (u:ℝ) :
  grain y ((weighted P u S).glow F)= grain y (S.glow F):=by
  rw [←whole_glow p]; change inner ℂ y (acts _ y)=inner ℂ y (acts _ y)
  rw [act_mul, wholeTilt_stays p y h, act_mul, ← act_inner (wholeTilt P u), (wholeTilt_self p u).star_eq,wholeTilt_stays p y h]

/-- Combine with one signed bill for *all* these stencils; isolated purely
analytic result. (k will be small at our application because we're using
$κ_s^{sample}$ parameter on polynomial readings too.) -/
theorem leaf_pose (p:IsStarProjection P)(S T:Shaft I)(F G:Fin n→ FC I)
    (σ: Fin n→Finset I) (o: Set.PairwiseDisjoint Set.univ σ)
    (k m ε L B:ℝ)(M:ℕ) (δ:Fin n→ℝ) (a:0≤k)
    (h: Pillow S T L ε)(he:0≤ ε)(t:∀ u:ℝ, |u|≤1→ Quotes (weighted P u S) m)
    (w:m≥1)(K:∀ i,Lyrics (σ i) M k (G i))
    (A:∀ i, ∀ s:ℝ, |s|≤1→ 0≤ s → ‖(weighted P s S).glow (F i)-(weighted P s S).glow (G i)‖ ≤ δ i)
    (C:∀ i, ∀ s:ℝ, |s|≤1 → 0 ≤ s → ‖(weighted P s S).glow (F i)‖ ≤ B) (b:0≤B) (c:B ≤ 1/2)
    (O:∀ i j, Commute (F i) (F j)) (x y: Wave I)(h0:Sea P y) :
    ‖acts (stripTil (S.glow ∘ F) 1) x‖ ≤ Real.exp ((∑ i, ((grain y (S.glow (G i))).re+δ i)) + n*fee k M L m ε B) * ‖acts (wholeTilt P 1) x‖:= by
  let H:= fun i=> S.glow (F i); let V:= fee k M L m ε B- 2*B^2; let T':= ∑ i, ((grain y (S.glow (G i))).re+δ i)
  have heq: ∀ i j, Commute (H i) (H j):= fun i j=> (O i j).map S.glowHom
  have h' : ∀ i s, |s| ≤ 1→ reopen P s (H i) = (weighted P s S).glow (F i):=fun i s _=> whole_glow p S _ _
  refine (engross P B (T'+n*V) b c x H heq (fun i t v p=> (h' i t v).symm ▸ (C i t v p)) ?_).trans_eq ?_
  · intro u s v r
    simp_rw [fun i=> h' i s v]; let W:= weighted P s S; let X:=‖u‖^2; let d:= heatCost u P
    let price(i:Fin n):=(grain y (S.glow (G i))).re; let discV(i:Fin n):= discrepancy u y (W.glow (G i));
    have hv(i:Fin n): (grain u (W.glow (F i))).re ≤ (price i+δ i)*X+‖discV i‖:=by
      let Y':= grain u (W.glow (F i)); let f':=grain u (W.glow (G i)); let U:=grain y (S.glow (G i)); let p':= price i; let r':=δ i
      have heq: Y'.re-f'.re ≤ X*r':= (Complex.sub_re ..).symm.trans_le ((Complex.re_le_norm _).trans (le_trans (b:=X*‖W.glow (F i)- W.glow (G i)‖) (by unfold Y' f'; rw [←map_sub]; exact grain_cap ..) (mul_le_mul_of_nonneg_left (A i s v r) (sq_nonneg ‖u‖))))
      have hg: discV i=f'-(X:ℂ)*U:=by unfold discV; rw [discrepancy_type,flat_part P p S y h0]
      have hm := Complex.re_le_norm (discV i); rw [show (discV i).re=f'.re-X*p' from ?_] at hm; swap; · rw [hg,Complex.sub_re, Complex.re_ofReal_mul]; -- tune
      change Y'.re ≤ _; linarith only [heq,hm]
    have hu:= entire_lyrics u y W (weighted P s T) σ o p h0 G a K (pillow_high p h v) (mul_nonneg tiltBound_pos.le he) (t s v) w
    have hp : ∑ i, ‖discV i‖ ≤ d + n*V*X:=by apply le_trans hu; rw [Fintype.card_fin]; unfold V fee; rw [add_sub_cancel_right] -- tune
    let f₂(i:Fin n):=(grain u (W.glow (F i))).re
    have ht: ∑ i, f₂ i ≤ T'*X +∑ i, ‖discV i‖:=by apply (sum_le_sum (fun i _=> hv i)).trans_eq; rw [sum_add_distrib,←sum_mul]
    change ∑ i, f₂ i ≤ _; linarith only [ht,hp]
  unfold V T'; congr 2; ring

#print axioms leaf_pose
end YM.CF.WakeInvestment
