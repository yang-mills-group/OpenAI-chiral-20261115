import YM.SU5.Reconstruction.Anvil.Era
import YM.SU5.Reconstruction.Seams.Hole
/-! # Momentum travel throughout all full Tunnels. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric MeasureTheory InnerProductSpace Spectral OS Semigroup ConePrice Analysis
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
variable {H: Hilbert} (a: Axis)
local notation "I"=> Complex.I
abbrev pilot(z: Wage) (p:E4):ℂ:= ∑ i∈ Finset.univ.erase a,z i*(p i:ℂ)
def rankQ (z: Wage)(p:E4) :ℂ:= -z a*(p a:ℂ)+pilot a z p*I
def sailQ (z:Wage) (p:E4) :ℂ:= if p∈ ConePrice.front a then Complex.exp (rankQ a z p) else 1
lemma subtractSc (z w: Wage)(p:E4):rankQ a (z+w) p=rankQ a z p+rankQ a w p:=by unfold rankQ pilot; simp only [Pi.add_apply,neg_add',add_mul,Finset.sum_add_distrib]; ring
lemma rankP (z:Wage)(p:E4) : (rankQ a z p).re= -(z a).re * p a- inner ℝ p (rimPay a (Deeper z)).val:=by unfold rankQ pilot; rw [parcel]; simp [Deeper, sub_eq_add_neg] -- need Complex.re_sum
lemma rank_facet (x:Meter)(p:E4) :pilot a (facet x) p= ↑(inner ℝ p (rimPay a x).val):= by rw [pilot,parcel]; push_cast; rfl
lemma sail_exp (x : Wage)(u : Loan a x) (p:E4): ‖sailQ a x p‖ ≤1 := by
 unfold sailQ; split_ifs with y; swap; · simp
 rw [Complex.norm_exp,Real.exp_le_one_iff, rankP, cone_mean]; let W:= rimPay a (Deeper x); have ht:0≤p a:= (norm_nonneg _).trans y; have he : |inner ℝ (SEP a p) W| ≤ p a *(x a).re:= (abs_real_inner_le_norm _ _).trans (mul_le_mul y u (norm_nonneg _) ht); linarith [(abs_le.mp he).1]
@[fun_prop] lemma rank_cont (z:Wage) :Continuous (rankQ a z) := by unfold rankQ pilot; fun_prop
@[fun_prop] lemma sailM (x:Wage) : Measurable (sailQ a x):= Measurable.piecewise (closed_front a).measurableSet (by unfold rankQ pilot; fun_prop) measurable_const
lemma rankD (x:E4) (z:ℂ→Wage){t:ℂ}(e: ∀ i,DifferentiableAt ℂ (fun t=> z t i) t) : DifferentiableAt ℂ (fun t=> rankQ a (z t) x) t:= (((e a).neg).mul_const _).add ((DifferentiableAt.fun_sum fun i _=> (e i).mul_const _).mul_const _)
lemma sail_cost (x:E4) : Continuous (fun z=> sailQ a z x):= by by_cases p:x∈ConePrice.front a<;>simp only [sailQ,p,ite_true,ite_false,rankQ,pilot]<;>fun_prop -- tune
open YM.Multiplier Boundary Probe
variable {a}(S:OS.Semigroup H a)(v:ConePrice.Forward S)
local notation "P"=> S.ℚmeasure
local notation "𝔪" x:max => S.ℚmeasure.diagonal x
def PaysOn (x:Wage): H.Op:= order P (sailQ a x)
local notation "r"=> PaysOn S
lemma signs (x:Wage)(u:Loan a x): Registers S.ℚmeasure (sailQ a x) (PaysOn S x):= order_reads _ ⟨sailM a x,1,zero_le_one,sail_exp a x u⟩
lemma francs (x: Wage)(u:Loan a x) : ‖PaysOn S x‖ ≤1:= (signs S x u).fare zero_le_one (sail_exp a x u)
lemma marchHol {z:ℂ→Wage}{D:Set ℂ}(h:IsOpen D)(u:∀ x∈D,Loan a (z x))(p:∀ i,DifferentiableOn ℂ (fun x=> z x i) D) : DifferentiableOn ℂ (fun x : ℂ=> r (z x)) D := by
 apply AnalyticOnNhd.differentiableOn; refine full_roofs P h (fun x y=> sailQ a (z x) y) 1 _ (fun x v=> signs S _ (u x v)) (fun x=> ?_) (fun x v=> sail_exp a _ (u x v)) (fun x=> sailM a (z x));
 by_cases b:x∈front a; swap; · simp only [sailQ,b,if_false]; fun_prop
 simp only [sailQ,b,if_true]
 exact DifferentiableOn.cexp (fun w t=> (rankD a x z (fun i=> (p i).differentiableAt (h.mem_nhds t))).differentiableWithinAt)
-- local variant sufficient where derivatives hold neighborhoodwise
-- strong-op continuity and simple convergence of perturbed data
variable {ι:Type*}(l:Filter ι)[l.IsCountablyGenerated]{x:Wage}(u:Loan a x) (V:ι→Wage)(hh:∀ᶠ i in l,Loan a (V i)) (e:Tendsto V l (𝓝 x))
include hh e u
lemma on_approach (y:H): Tendsto (fun i=>r (V i) y) l (𝓝 (r x y)):= by
 classical
 let f (i:ι) := if Loan a (V i) then V i else x; have p (i):Loan a (f i):= by unfold f; split_ifs with h <;> assumption
 have E:f =ᶠ[l] V:= hh.mono fun _ v=> if_pos v
 refine Tendsto.congr' (f₁:=fun i=>r (f i) y) (E.mono fun i h=>congrArg (fun x=>r x y) h) (order_tends P _ _ ((signs S x u).price) (fun i=> (signs S _ (p i)).price) (fun i=> ((sail_cost _ i).tendsto _).comp (e.congr' E.symm)) 1 (Eventually.of_forall (fun x=> sail_exp _ _ (p x))) _) -- tune
lemma adj_approach (y:H): Tendsto (fun i=> (ContinuousLinearMap.adjoint (r (V i))) y) l (𝓝 (ContinuousLinearMap.adjoint (r x) y)):= by
 classical
 let f (i:ι) := if Loan a (V i) then V i else x; have p (i):Loan a (f i):= by unfold f; split_ifs with h <;> assumption
 have E:f =ᶠ[l] V:= hh.mono fun _ v=> if_pos v
 refine Tendsto.congr' (f₁:=fun i=>(ContinuousLinearMap.adjoint (r (f i))) y) (E.mono (fun i h=>congrArg (fun x=>(ContinuousLinearMap.adjoint (r x)) y) h)) (Registers.tends l _ _ (signs S x u).adjoint (fun i=>(signs S _ (p i)).adjoint) y 1 (Eventually.of_forall (fun i=> Eventually.of_forall (fun y=>by change ‖star _‖≤1; rw [norm_star]; exact sail_exp a _ (p i) y))) (Eventually.of_forall fun y=> (((sail_cost _ y).tendsto _).comp (e.congr' E.symm)).star)) -- star notation
lemma keepRight (g:ι→H)(y:H)(f:Tendsto g l (𝓝 y)): Tendsto (fun i=> r (V i) (g i)) l (𝓝 (r x y)):= by
 apply Metric.tendsto_nhds.mpr; intro ε p
 filter_upwards [hh,Metric.tendsto_nhds.mp f (ε/2) (by positivity), Metric.tendsto_nhds.mp (on_approach S l u V hh e y) (ε/2) (by positivity)] with i v a b
 refine lt_of_le_of_lt (dist_triangle _ (r (V i) y) _) (lt_of_lt_of_le (add_lt_add (lt_of_le_of_lt ?_ a) b) (add_halves ε).le)
 rw [dist_eq_norm,← map_sub,dist_eq_norm]; exact ((r (V i)).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (francs S _ v) (norm_nonneg _)).trans_eq (one_mul _))
lemma keepLeft (g:ι→H)(y:H)(f:Tendsto g l (𝓝 y)): Tendsto (fun i=> (ContinuousLinearMap.adjoint (r (V i))) (g i)) l (𝓝 (ContinuousLinearMap.adjoint (r x) y)):= by
 apply Metric.tendsto_nhds.mpr; intro ε p
 filter_upwards [hh,Metric.tendsto_nhds.mp f (ε/2) (by positivity), Metric.tendsto_nhds.mp (adj_approach S l u V hh e y) (ε/2) (by positivity)] with i v a b
 refine lt_of_le_of_lt (dist_triangle _ (ContinuousLinearMap.adjoint (r (V i)) y) _) (lt_of_lt_of_le (add_lt_add (lt_of_le_of_lt ?_ a) b) (add_halves ε).le)
 rw [dist_eq_norm,← map_sub,dist_eq_norm]; exact ((ContinuousLinearMap.adjoint (r (V i))).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (by simpa using francs S _ v) (norm_nonneg _)).trans_eq (one_mul _))
omit e hh u
include v
lemma realRent (x:Meter)(u:0≤x a) : PaysOn S (facet x)= S.E (Real.toNNReal (x a)) * S.U (rimPay a x):= by
 let e:= signs S (facet x) ((loan_initial _ _).2 u); apply e.single; let A:=Real.toNNReal (x a)
 refine ⟨e.price,fun z=> ?_⟩; change inner ℂ z (S.E A (S.U (rimPay a x) z))= _; rw [← ContinuousLinearMap.comp_apply, S.independent,ContinuousLinearMap.comp_apply,ConePrice.damped]; apply integral_congr_ae
 filter_upwards [forward_ae S z v] with p h
 rw [sailQ,if_pos h,rankQ,rank_facet]; unfold plane; rw [show (A:ℝ)=x a from Real.coe_toNNReal _ u, ← Complex.exp_add]; congr 1; simp only [facet_apply]; ring_nf; simp; ring
omit v in
lemma combine (x y:Wage)(u:Loan a x)(v0:Loan a y)(t:Loan a (x+y)) : PaysOn S (x+y)= r x*r y:= by
 apply (signs S _ t).single; convert (signs S _ u).times (signs S _ v0) using 1; funext i; by_cases h:i∈front a <;> simp only [Pi.mul_apply,sailQ,h,if_true,if_false,Complex.exp_add,subtractSc,one_mul]
lemma edgeJoin (t:ℝ) : r (onlyTime a (sideways t))= S.edge t:= by
 let x:=onlyTime a (sideways t); have e:Loan a x:= by unfold Loan x; rw [only_agree]; simp [only_pay,sideways,onlyTime]
 let p:= signs S x e
 apply p.single; rw [← Picket.trans_time t S]; apply (Picket.story ..).agrees p.price
 intro y; filter_upwards [forward_ae S y v] with z h; unfold sailQ rankQ; rw [if_pos h, plane]; 
 rw [real_inner_smul_right, Picket.innerB,pilot, Finset.sum_eq_zero (fun i v=>by simp [x,onlyTime,Finset.ne_of_mem_erase v])]; simp only [x,onlyTime,Pi.single_eq_same,sideways]; congr 1; push_cast; ring
end YM.Anvil
