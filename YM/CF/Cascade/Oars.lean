import YM.Next.FREE_KERNELS.Primal
import YM.CF.Pec.Ora
import YM.CF.Aroma.Parlour
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
lemma blade0 (p:Momentum) (i:Axis): symbol 0 p (coord i) vac=Exterior.q p i:=by
  unfold symbol wedge
  rw [Matrix.sum_apply,sum_eq_single i]; · simp [Exterior.left,coord,vac_only,parity,pre, Finset.filter_singleton]
  · intro j _ hj; simp [Exterior.left,coord,hj]
  simp
open Flight
local notation "Z" => coord (1:Axis)
def angel (k:ℝ)(P:Flight j t)(p:Momentum)(l: Site P.L):= toll P.L 1 * (pilot k P p l Z Z)
lemma aheadP (P:Flight j t)(p:Momentum)(x:p 1=0)(l: Site P.L)(i:TypeFace 1):pilot k P p l i Z = ahead k P p l i Z:=by
 have h(u:TypeFace 0): sluice k P p u Z=0:=by
    unfold sluice; rw [Matrix.smul_apply,Matrix.mul_apply]; unfold priorG; rw [sum_eq_single Z]
    · have hu:u=vac:=vac_only ..
      rw [mirage,Matrix.transpose_apply,hu,signal_unit,blade0]; simp [Exterior.q,x]
    · intro j _ v; simp [mask_value,v]
    simp
 rw [pilot, Matrix.add_apply, Matrix.mul_apply]; simp_rw [h]; simp
lemma aheadQ (P:Flight j t)(p:Momentum)(x:p 1=0)(l:Site P.L)(i: TypeFace 1)(e:i≠Z):pilot k P p l i Z=0:=by
 rw [aheadP P p x]; unfold ahead flux priorG hinges; split <;> simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul,Matrix.smul_apply,mask_trans,mask_mul]; all_goals simp [mask_value,e]
lemma angel_p (P:Flight j t): angel k P 0 0=(P.L.val:ℂ)⁻¹:=by simp [angel,toll]
lemma lowC (p:0<k)(x:4≤j)(y:4≤t): Moderate (fun _:Flight j t=>1) (fun P q=> pilot k P q 0 Z Z):=by
 exact (((pilot_cost k p x y (id:Flight j t→Flight j t) (fun i=>0)).tap Z Z).raise_price (u:=fun _=> 1) fun _=> decay_le_one _ _)
abbrev Legends(j t:ℕ):= Σ i:Flight j t, {l:Site i.L// l≠0}
def tenor(p:ℝ)(q:Legends j t)(x:Momentum):= (mask 1 (portD p q.1 x q.2)*flux q.1 1 (aliasAt x q.2.val)*priorG p q.1 x) Z Z
lemma vcost (p:0<k)(x:4≤j)(y:4≤t):Moderate (fun _:Legends j t=>1) (fun i:Legends j t=> tenor k i):=by
 let F(i:Legends j t):=i.1; let A(i:Legends j t): Site (F i).L:= i.2.val; have he(a: Axis):= portD_budget k x F A (fun i=> i.2.property) fun _=>a
 have ht:= (((Pay.expose_mask 1 he).times (flux_budget F 1 A)).times (prior_cost k p y F)|>.tap Z Z); apply ht.raise_price; intro i; simp only [pow_one,one_mul,mul_one]; exact (mul_le_of_le_one_left (decay_pos ..|>.le) (inv_le_one_of_one_le₀ (one_le_pow₀ (grade_ge _)))).trans (decay_le_one _ _)
lemma closeP {ι:Type}{f:ι→ Momentum→ℂ}(h: Moderate (fun _=>1) f):∃ a C:ℝ,0<a∧0<C∧∀ x:Momentum,‖x‖<a→∀ i,‖f i x-f i 0‖≤ C*‖x‖:=by
 obtain ⟨a,C,ha,hC,P⟩:= h; let r:= a/2; have hp:0<r:=half_pos ha; have hx: ball (0:Momentum) r⊆ cube a:= (ball_subset_ball (show r ≤ a-r by unfold r; linarith)).trans (ball_inside_cube (cube_zero r hp))
 refine ⟨r,2*C/r,hp,(by positivity),fun x g i=>?_⟩
 have hh : Set.MapsTo (f i) (ball (0:Momentum) r) (Metric.closedBall (f i 0) (2*C)):=by intro z t; rw [Metric.mem_closedBall,dist_eq_norm]; exact (norm_sub_le ..).trans ((add_le_add ((P i).bound z (hx t)) ((P i).bound 0 (cube_zero a ha))).trans_eq (by ring))
 have hz:x∈ ball (0:Momentum) r:=by simpa using g
 simpa only [dist_eq_norm,sub_zero] using Complex.dist_le_div_mul_dist_of_mapsTo_ball (fun z v=> ((P i).hol z (hx v)).differentiableWithinAt) hh hz
lemma vexp (p:0<k)(x:4≤j)(y:4≤t):∃ C:ℝ,0<C∧∀ (P:Flight j t) (l:Site P.L),l≠0→ ∀ z:Momentum,z∈baseCube→ z 1=0→ ‖angel k P z l‖≤ C*lengthSq z:=by
 obtain ⟨a,c,h,hc,D⟩:=vcost p x y; refine ⟨meter.high^2*c,mul_pos (pow_pos meter.high_pos _) hc,fun P l ht z he g=>?_⟩
 let V:=P.span z; have hf :‖V‖ ≤ meter.high^2*lengthSq z:=by
    have hp:=divisor_real_bounds P.land.mass (base_subset_realCube zone_pos he); apply le_trans _ hp.2; unfold V span; rw [divisor_normSq _ he.1]; simp only [Complex.norm_real,Complex.ofReal_re]; exact le_of_eq (Real.norm_of_nonneg (Finset.sum_nonneg fun i _=> sq_nonneg _))
 unfold angel; rw [aheadP _ _ g, ahead,if_neg ht,Matrix.smul_apply,norm_mul,norm_smul]; apply le_trans (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_); change ‖V‖ * ‖tenor k ⟨P,l,ht⟩ z‖≤ _; have hv:= D (⟨P,l,ht⟩:Legends j t); have he:= hv.bound z (mem_cube_real (base_subset_realCube h he) h);
 exact (mul_le_mul hf (he.trans_eq (mul_one _)) (norm_nonneg _) ((norm_nonneg _).trans hf)).trans_eq (by ring)
 rw [toll,norm_inv,pow_one]; simp only [Complex.norm_natCast]; exact inv_le_one_of_one_le₀ (by exact_mod_cast P.L.property)
lemma angel_pr (p:0<k)(x:4≤j)(y:4≤t):∃ a C:ℝ,0<a∧0<C ∧∀ P:Flight j t,∀ v: Momentum,‖v‖<a→ ‖angel k P v 0-(P.L.val:ℂ)⁻¹‖ ≤ C*‖v‖:=by
 obtain ⟨s,c,h,t,P⟩:= closeP (lowC p x y); refine ⟨s,c,h,t,fun F v hx=>?_⟩
 rw [←angel_p (k:=k),angel,angel,←mul_sub,norm_mul]; refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (P v hx F); simp only [toll,norm_inv,pow_one,Complex.norm_natCast]; exact inv_le_one_of_one_le₀ (by exact_mod_cast F.L.property)
end YM.CF.Cascade
