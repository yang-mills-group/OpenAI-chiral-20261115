import Velour.Organza.Larva
import Velour.Organza.Sprinkles
namespace YM.Velour
open Filter Metric
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false
variable {H:Hilbert}

private lemma glow_tan {f:ℕ→ℕ→H.Op} {g:ℕ→H.Op}
    {F:ℕ→H.Op}{G:H.Op} {b:ℕ→ℝ}
    (e:∀k, ∀ v:H, Tendsto (fun i=> f k i v) atTop (𝓝 (g k v)))
    (c:∀ k, ‖g k-G‖≤b k)
    (d:∀ k i, ‖f k i-F i‖≤ b k)
    (z:Tendsto b atTop (𝓝 0)):
    ∀ v:H,Tendsto (fun i=> F i v) atTop (𝓝 (G v)):=by
 intro v
 refine Metric.tendsto_nhds.mpr fun ε u=>?_
 let h:=z.mul_const ‖v‖
 rw [zero_mul] at h
 obtain ⟨k,y⟩:= (h.eventually_lt_const (show 0<ε/3 by positivity)).exists


 filter_upwards [Metric.tendsto_nhds.mp (e k v) (ε/3) (by positivity)] with i w
 have p(A B:H.Op)(r:‖A-B‖≤b k): dist (A v) (B v)< ε/3:=by
     rw [dist_eq_norm,←sub_apply]
     exact ((ContinuousLinearMap.le_opNorm ..).trans
       (mul_le_mul_of_nonneg_right r (norm_nonneg _))).trans_lt y
 linarith only [w,p _ _ (c k),p _ _ (d k i),
        dist_triangle (F i v) (f k i v) (G v),dist_triangle (f k i v) (g k v) (G v),
        dist_comm (F i v) (f k i v)]

lemma Gleams.uniform_joints {f:ℕ→ℕ→H.Op} {g:ℕ→H.Op}
    {F:ℕ→H.Op}{G:H.Op} {b:ℕ→ℝ}
    (e:∀k,Gleams H (f k) (g k))
    (c:∀ k, dist (g k) G≤b k)
    (d:∀ k i, dist (f k i) (F i)≤ b k)
    (z:Tendsto b atTop (𝓝 0)):
    Gleams H F G:=by
 simp only [dist_eq_norm] at c d
 obtain ⟨B,h⟩:=(e 0).bought
 refine ⟨⟨b 0+B,h.mono fun i w=>?_⟩,glow_tan (fun k=>(e k).gaze) c d z,?_⟩
 · exact (norm_le_norm_sub_add _ (f 0 i)).trans
    (add_le_add ((norm_sub_rev ..).le.trans (d 0 i)) w)


 exact glow_tan (H:=H) (f:=fun k i=>star (f k i)) (g:=fun k=>star (g k))
       (fun k=>(e k).turn)
       (fun k=>by rw [←star_sub,norm_star]; exact c k)
       (fun k i=>by rw [←star_sub,norm_star]; exact d k i) z
end YM.Velour
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Velour Boundary Probe
local notation "R"=> S.gauze
local notation "E"=> S.E

def tucked (A:H.Op)(d:ℝ≥0):H.Op := E d * A * E d
lemma tuck_reels (A:H.Op):S.Covetails (S.tucked A):=by
 intro d _ t
 change _ = E t * (_*A*_) * _
 have p(x y:ℝ≥0):E (x+y)=E x*E y:= S.time x y
 nth_rw 1 [tucked]
 change E (d+t)*A*E (d+t)= E t * (E d*A*E d)* E t
 nth_rw 1 [add_comm d t]
 rw [p,p]
 simp only [mul_assoc]

lemma tucked_winding (A:H.Op)(m:ℕ){τ:ℕ→ℝ≥0}(p:Tendsto τ atTop (𝓝 0))(r:m≠0):
   Tendsto (fun i=> S.winding_pick (S.tucked A) m (τ i)) atTop
             (𝓝 (R^m * A * R^m)):=by
 let q:=S.winding_approaches p r
 refine ((q.mul_const A).mul q).congr fun i=>?_
 rw [winding_pick,tucked,←mul_assoc,←mul_assoc,←mul_assoc,←(S.winding_symm m (τ i) (τ i)).eq] 


variable {τ:ℕ→ℝ≥0}{C D:ℝ}

def full_bill (τ:ℕ→ℝ≥0)(C D:ℝ)(m:ℕ) :=
     wind_charge τ C D m / (1-D/2^m) +
       (m * (2:ℝ)^m) * C * (m * (2:ℝ)^m)

lemma total_price {Q:ℝ≥0→H.Op}{X:H.Op}
     (h:Installments Q τ C D) (m:ℕ)
     (e: dist (S.winding_pick Q m (τ 0)) X ≤
        wind_charge τ C D m * (D/2^m)^0 / (1-D/2^m)):
     ‖X‖≤full_bill τ C D m:=by
 rw [pow_zero,mul_one,dist_comm,dist_eq_norm] at e
 refine (norm_le_norm_sub_add _ (S.winding_pick Q m (τ 0))).trans
           (add_le_add e ?_)
 let a:=S.winding_bound m (τ 0)
 have p:=h.pay 0; rw [pow_zero,mul_one] at p
 exact (norm_mul_le ..).trans (mul_le_mul
    ((norm_mul_le ..).trans (mul_le_mul a p (norm_nonneg _) ((norm_nonneg _).trans a)))
    a (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans a) ((norm_nonneg _).trans p)))

variable {Y:ℕ→H.Op}{Q:ℝ≥0→H.Op}

structure Ribs (Y:ℕ→H.Op)(Q:ℝ≥0→H.Op)(m:ℕ)(A:ℝ)(X:H.Op):Prop where
  prepaid : S.Prepaid Q m X
  spent : ∀i, ‖S.gauze^m * Y i * S.gauze^m‖≤A
  rattle : Gleams H (fun i=> S.gauze^m * Y i * S.gauze^m) X

lemma Ribs.limit {Y:ℕ→H.Op}{Q:ℝ≥0→H.Op}{m:ℕ}{X:H.Op}{A:ℝ}
    (h:S.Ribs Y Q m A X) : ‖X‖≤A:= h.rattle.norm_paid (Eventually.of_forall h.spent)


variable {m:ℕ}
theorem wind_all (h:S.Covetails Q)
   (p:∀ i, Installments (S.tucked (Y i)) τ C D)
   (g:∀ k, Gleams H (fun i=> S.tucked (Y i) (τ k)) (Q (τ k)))
   (m:ℕ)(r:D<2^m):
   ∃ X, S.Ribs Y Q m (full_bill τ C D m) X:=by
 have a:=p 0
 have y: Installments Q τ C D:=
   ⟨a.minC,a.minD,a.pos,a.falls, fun k=> (g k).norm_paid (Eventually.of_forall fun i=>(p i).pay k)⟩
 obtain ⟨X,e,t,u⟩:= S.winding_price h y m r
 have q:m≠0:=by rintro rfl;rw [pow_zero] at r; exact not_le.mpr r y.minD
 let b(k:ℕ):=wind_charge τ C D m * (D/2^m)^k / (1-D/2^m)
 have ub(i k:ℕ): dist (S.winding_pick (S.tucked (Y i)) m (τ k))
      (R^m * Y i * R^m) ≤ b k:=by
   obtain ⟨Z,_,j,u⟩:=S.winding_price (S.tuck_reels (Y i)) (p i) m r
   rw [←tendsto_nhds_unique j (S.tucked_winding _ _ a.dies q)]
   exact u k


 have n: Tendsto b atTop (𝓝 0):=by
    have q:= tendsto_pow_atTop_nhds_zero_of_lt_one
         (show (0:ℝ)≤D/2^m from div_nonneg (zero_le_one.trans y.minD) (by positivity))
         ((div_lt_one (by positivity)).mpr r)
    simpa using (q.const_mul (wind_charge τ C D m)).div_const (1-D/2^m)
 refine ⟨X,e,fun i=>S.total_price (p i) m (ub i 0),?_⟩
 exact Gleams.uniform_joints (f:=fun k i=> S.winding_pick (S.tucked (Y i)) m (τ k))
       (fun k=>
          let a:= Gleams.const (H:=H) (S.winding m (τ k))
          (a.mul (g k)).mul a)
       u (fun k i=>ub i k) n
#print axioms wind_all

