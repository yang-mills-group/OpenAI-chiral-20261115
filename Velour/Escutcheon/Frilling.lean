import Velour.Escutcheon.Torte
import YM.CF.BProof.Floral.Hol
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

open Metric
-- Cauchy, as in YM.SU5.Same.TemperPrism
lemma density_cost (z:ℂ) (w:0<z.re) : ‖deriv S.F z‖ ≤ 1 / (z.re/2):=by
 apply CF.Floral.c_deriv (AnalyticOnNhd.differentiableOn S.localHeat) (half_pos w) _ (fun z h=> S.norm_row h); intro x p
 apply (half_pos w).trans_le (?_ : z.re/2≤x.re); have he: _≤ z.re/2:= mem_closedBall.mp p; rw [dist_eq_norm] at he; have hx:= (abs_le.mp ( (Complex.abs_re_le_norm (x-z)).trans he)).1; rw [Complex.sub_re] at hx; linarith

lemma parc_bound (m:ℕ)(d:ℝ)(e:0<d):
 ∃ c:ℝ, 0<c ∧ ∀ R:ℝ, 1≤R → ∀ z:ℂ,d≤R*z.re→
 ‖parabola S m z‖≤ c * R^m:= by
 have t {d R:ℝ}{z:ℂ}(e:0<d)(r:1≤R)(p:d≤R*z.re): 0<z.re:=
    pos_of_mul_pos_left ((e.trans_le p).trans_eq (mul_comm R z.re)) (zero_le_one.trans r)


 induction m generalizing d with
 | zero=>
   refine ⟨1,zero_lt_one,fun R p z q=> (S.norm_row (t e p q)).trans ?_⟩
   simp
 | succ m ih=>
   obtain ⟨c,L,w⟩:=ih (d/2) (half_pos e)
   refine ⟨(1+4/d)*c, by positivity, fun r y z v=> ?_⟩
   let u:= z/2
   have V:d/2≤r*u.re:=by change d/2≤r*(_/2:ℂ).re; rw [div_ofNat_re]; linarith
   have g:=t (half_pos e) y V
   have l:‖looper S u‖ ≤ (1+4/d)*r:=by
      refine (norm_sub_le ..).trans ((add_le_add (S.norm_row g)
              (S.density_cost u g)).trans ?_)
      rw [add_mul]
      exact add_le_add (by rwa [one_mul]) (by
          rw [div_mul_eq_mul_div]
          apply (div_le_div_iff₀ (half_pos g) e).2
          nlinarith only [V])
   rw [parabola]
   exact (norm_mul_le ..).trans ((mul_le_mul l (w r y _ V) (norm_nonneg _)
     ((norm_nonneg _).trans l)).trans (by rw [pow_succ];ring_nf;exact le_rfl))


open _root_.YM.CF.Buffered.Afterglow.Hierarchy
variable (b:Cross a)(A:Shelf S b)
lemma trim_bound (m:ℕ)(d:ℝ)(e:0<d) :
 ∃c:ℝ, 0<c ∧ ∀R:ℝ, 1≤R → ∀z w:ℂ, d≤R*(z.re-|w.im|)→
  ‖Seld.Poin.foil S b A m z w‖ ≤ c*R^m:=by
 obtain ⟨c,p,r⟩:=S.parc_bound m _ (half_pos e)
 refine ⟨4*c,by positivity,fun R L z w g=>?_⟩
 have i:= pos_of_mul_pos_right (e.trans_le g) (zero_le_one.trans L)
 have k: Wheel z w:=sub_pos.mp i
 have h:0<z.re:=wheel_pos _ _ k
 let t:=wageX z w
 have v:=A.norm t w (cups_own z w k).2
 have y:d/2≤R*(z-duration t).re:=by
    dsimp only [duration,t,wageX]
    rw [sub_re,ofReal_re,Real.coe_toNNReal _ (by positivity)]
    linarith only [g]
 have u:=r R L _ y
 exact (norm_mul_le ..).trans ((mul_le_mul u v (norm_nonneg _) ((norm_nonneg _).trans u)).trans_eq (by ring))

def Flourish {n:ℕ}(d R:ℝ) (z w:Fin n→ℂ):Prop:=
 ∀i j:Fin n,i<j→ d≤R*((z j-z i).re - |(w j - w i).im|)

lemma mill_bound_aux (n:ℕ)(d:ℝ)(e:0<d)(m:Fin (n+1)→ℕ)(G:Fin (n+1)→ H.Op):
 ∃c:ℝ,0<c∧∀R:ℝ, 1≤R → ∀ z w:Fin (n+1)→ℂ,Flourish d R z w→∀Y,
  R ^ (m 0) * ‖Rail G (Draw S b A z w Y m)‖ ≤ c * R ^ (∑ i, (m i + m i)):=by
 induction n with
 | zero=>
   refine ⟨‖G 0‖+1,by positivity,fun R t z w _ Y=>?_⟩
   have L:=zero_le_one.trans t
   have g:Rail G (Draw S b A z w Y m) = G 0:= by exact solitary ..
   rw [g,Fin.sum_univ_succ,Fintype.sum_empty,add_zero,mul_comm]
   gcongr
   · exact le_add_of_nonneg_right zero_le_one
   · exact Nat.le_add_right ..


 | succ n ih=>
   obtain ⟨c,p,t⟩:=ih (Fin.tail m) (Fin.tail G)
   let l:Fin (n+2):=(0:Fin (n+1)).succ
   obtain ⟨a',g,r⟩:=S.trim_bound b A (m 0+m l) d e
   refine ⟨(‖G 0‖+1)*a'*c,by positivity,fun R q z w L Y=>?_⟩
   let J:=Draw S b A z w Y m
   have h: R^m l * ‖Rail (Fin.tail G) (rump J)‖≤ c * R^(∑ i:Fin (n+1), (m i.succ+m i.succ)):=
     t R q (Fin.tail z) (Fin.tail w)
       (fun i j x=>L _ _ (Fin.succ_lt_succ_iff.mpr x)) (Fin.tail Y)
   have y:‖S.U (Y l-Y 0)‖ ≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      fun x=>(S.unitary _ _).le.trans_eq (one_mul _).symm
   have iPos:=zero_le_one.trans q
   have k:‖J 0 l‖ ≤a'*R^m 0*R^(m l):=
     (norm_mul_le ..).trans ((mul_le_mul
      (r R q _ _ (L _ l (Fin.succ_pos _))) y (norm_nonneg _) (by positivity)).trans_eq (by rw [pow_add,mul_one, mul_assoc]))
   rw [Fin.sum_univ_succ, Rail_step,s1S]


   let D:=∑ i:Fin (n+1), (m i.succ+m i.succ)
   let V:= Rail (Fin.tail G) (rump J)
   have u: ‖G 0 * J 0 l * V‖ ≤
       (‖G 0‖+1)*(a'*R^m 0*R^(m l))*‖V‖:=
      (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right
       ((norm_mul_le ..).trans
        (mul_le_mul (show ‖G 0‖≤‖G 0‖+1 by linarith) k (norm_nonneg _) (by positivity))) (norm_nonneg _))
   let w₀ := ‖G 0‖+1
   let D' := w₀*a'*(R^m 0)^2
   have t:=mul_le_mul_of_nonneg_left h (show 0≤D' from by dsimp [D',w₀]; positivity)
   refine (mul_le_mul_of_nonneg_left u (pow_nonneg iPos (m 0))).trans ?_
   calc
    _ = D' * (R^m l* ‖V‖):=by dsimp [D',w₀];ring
    _ ≤ D'*(c*R^D):= t
    _ = _ :=by rw [pow_add,pow_add]; dsimp [D',D,w₀];ring


lemma rail_bound {n:ℕ}(d:ℝ)(e:0<d)(m:Fin n→ℕ)(G:Fin n→ H.Op):
 ∃c:ℝ,0<c∧∀R:ℝ, 1≤R → ∀ z w:Fin n→ℂ,Flourish d R z w→∀Y,
  ‖Rail G (Draw S b A z w Y m)‖ ≤ c * R ^ (∑ i, (m i + m i)):=by
 cases n with
 | zero=>
   refine ⟨‖(1:H.Op)‖+1,by positivity,fun R p z w _ Y=>?_⟩
   rw [Fintype.sum_empty,pow_zero,mul_one]
   exact le_add_of_nonneg_right zero_le_one
 | succ n=>
   obtain ⟨c,p,t⟩:=S.mill_bound_aux b A n d e m G
   exact ⟨c,p,fun R q z w v y=>
    (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ q)).trans
     (t _ q _ _ v y)⟩


variable {S}{κ:Type} (L:S.Livery κ){n:ℕ}(u:Fin n→κ)
namespace Livery

-- remain b,A explicit before L; reorder L first for projection?
def modes :ℕ:= ∑ i, (L.m (u i)+L.m (u i))
lemma modes_order (g:Equiv.Perm (Fin n)):
 L.modes (u ∘ g)=L.modes u:=Equiv.sum_comp g (fun i=> L.m (u i) + L.m (u i))
abbrev bay (z w:Fin n→ℂ)(Y:Fin n→Cross a):ℂ:=
 Mell S L.Ω.val b A z w Y (L.G ∘ u) (L.m ∘ u)


local notation "Ω"=> L.Ω.val
lemma marge (d:ℝ)(e:0<d):
 ∃c:ℝ,0<c∧∀R:ℝ,1≤R → ∀z w:Fin n→ℂ,Flourish d R z w→∀Y,
 ‖L.bay b A u z w Y‖ ≤ c * R ^ L.modes u:=by
 obtain ⟨c,p,t⟩:= S.rail_bound b A d e (L.m ∘ u) (L.G ∘ u)
 refine ⟨(‖Ω‖*‖Ω‖+1)*c,by positivity, fun R q z w h Y=>?_⟩
 have r:= t R q _ _ h Y
 let B:= Rail (L.G ∘ u) (Draw S b A z w Y (L.m ∘ u))
 have e:=q.trans' (show (0:ℝ)≤1 from zero_le_one)
 calc
  _ ≤ ‖Ω‖* (‖B‖*‖Ω‖) := (norm_inner_le_norm (𝕜:=ℂ) Ω _).trans
         (mul_le_mul_of_nonneg_left (B.le_opNorm Ω) (norm_nonneg _))
  _ = ‖Ω‖*‖Ω‖*‖B‖:=by ring
  _ ≤ (‖Ω‖*‖Ω‖+1)*(c*R^L.modes u):=
         mul_le_mul (le_add_of_nonneg_right zero_le_one) r (norm_nonneg _) (by positivity)
  _ = _:=by rw [mul_assoc]
#print axioms marge

