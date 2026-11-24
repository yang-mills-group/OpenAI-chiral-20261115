/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Gauge.Size
import YM.Wilson.Symmetry

/-!
# Beyond estimating vacuum by its crude lower and total prior volume upper

Compare different Haar shell factors by LOCAL packing rather than comparing to
total volume. Use the actual motivating HS rather than any norm on the algebra
of states. Constants independent of coupling. This is a step to cancel factors
against normalized Haar shell lower at the same volume. In particular doing
this need *not* require Lie exponential coordinates and fixed smooth
Jacobians, even without choosing `LocalRatio`; helps to eliminate differences
between powers of x.

Packing proof adjusted from `YM/Gauge/Size`. The new part is relative, and the
decay estimate is uniform relative to the same shell measured in the lower.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fixed.Extensive
open Function Filter Set MeasureTheory Gauge Lattice
open scoped Matrix.Norms.Frobenius BigOperators Topology ENNReal InnerProductSpace
attribute [local instance] frobInner
variable {x y:ℝ}
private theorem packing {E: Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
    (p:ℝ)(A: Finset E)(t:ℝ) (g:0<t)(h:0≤p) (X:E)
    (H:(A:Set E).Pairwise (fun i j=>2*t< ‖i-j‖)) (B:∀ i∈A,‖i-X‖≤p*t) : (A.card:ℝ) ≤ (p+1)^Module.finrank ℝ E := by
  letI : MeasurableSpace E:=borel _; letI : BorelSpace E:=⟨rfl⟩; letI : ProperSpace E:=FiniteDimensional.proper ℝ _
  let μ : Measure E:= Measure.addHaar; haveI : Measure.IsAddHaarMeasure μ:=by unfold μ; infer_instance
  let d:= Module.finrank ℝ E; let D:= μ.real (Metric.ball 0 1)
  have fan (i:E)(v:ℝ): μ (Metric.ball i v) <⊤ := measure_ball_lt_top
  have hD:0<D:= ENNReal.toReal_pos (by rw [ne_eq]; exact Measure.IsOpenPosMeasure.open_pos _ Metric.isOpen_ball (Metric.nonempty_ball.mpr zero_lt_one)) (fan _ _).ne
  have he (a : E)(r:ℝ)(hr:0<r): μ.real (Metric.ball a r) = r^d*D := by rw [measureReal_def, Measure.addHaar_ball_of_pos μ _ hr, ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]; rfl
  let K(i:E):= Metric.ball i t
  have hv:(⋃ i∈A, K i) ⊆ Metric.ball X ((p+1)*t):=by
    intro i g; obtain ⟨y,hy,hY⟩:= mem_iUnion₂.mp g; rw [Metric.mem_ball, dist_eq_norm]
    have hp:=norm_sub_le_norm_sub_add_norm_sub i y X; have he: ‖i-y‖ < t := by simpa [K, Metric.mem_ball, dist_eq_norm] using hY
    nlinarith [B y hy]
  have hd:Set.PairwiseDisjoint (A:Set E) K:=by
    intro i hi j hj z; apply Set.disjoint_left.mpr; intro x hx hy; have p:= norm_sub_le_norm_sub_add_norm_sub i x j
    have ht: ‖i-x‖ < t:= by rw [norm_sub_rev]; simpa [K,Metric.mem_ball,dist_eq_norm] using hx
    have hu: ‖x-j‖ < t:= by simpa [K,Metric.mem_ball,dist_eq_norm] using hy
    linarith [H hi hj z]
  have ht:=measureReal_mono (μ:=μ) hv (by exact (fan _ _).ne)
  rw [measureReal_biUnion_finset hd (fun i _=>Metric.isOpen_ball.measurableSet) (fun i _=> (fan _ _).ne), he _ _ (by positivity),mul_pow] at ht
  simp only [K,he _ _ g, Finset.sum_const,nsmul_eq_mul,mul_assoc] at ht
  apply le_of_mul_le_mul_right ht (show 0<t^d*D by positivity)

variable (G:Gauge)
def shellMass (r:ℝ):= G.probHaar.real (G.shell r)
lemma shellMass_le : shellMass G x≤1:= (measureReal_mono (subset_univ (G.shell x))).trans (probReal_univ.le)
lemma shellMass_pos (h:0<x)(e:x≤1): 0 < shellMass G x := (show 0<(x/4)^Module.finrank ℝ G.Mat by positivity).trans_le (G.shell_ge x h e)
lemma shellMass_ratio (h:0<x)(g:0≤y) : shellMass G (y*x) ≤ (2*y+1)^Module.finrank ℝ G.Mat * shellMass G x := by
  classical
  let d:=Module.finrank ℝ G.Mat; let γ:=G.colorScale; have hp:0<γ:=G.colorScale_pos
  let S:=G.shell (y*x); let f(U:G.El)(V:G.El):= ‖G.mat U-G.mat V‖; let T:=x*γ
  let B:= (2*y+1)^d
  have e(a:G.El): a∈S ↔ f a 1≤ (2*y)*(T/2):=by
    change ‖G.mat a-1‖/γ≤_ ↔ _; unfold f; rw [G.mat_one,div_le_iff₀ hp,show 2*y*(T/2)=y*x*γ by unfold T; ring]
  let V(A:Finset G.El):Prop:= (A:Set G.El).Pairwise (fun u v=>T<f u v) ∧ ∀ i∈A,i∈S
  have he(A:Finset G.El)(v:V A): (A.card:ℝ)≤ B:=by
    let P:=A.image G.mat
    have ht:(P:Set G.Mat).Pairwise (fun i j=>2*(T/2) < ‖i-j‖):=by
      rintro i hi j hj t; obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hi; obtain ⟨y,hy,rfl⟩:= Finset.mem_image.mp hj; rw [show 2*(T/2)=T by ring] -- tune; cancel₀ order
      exact v.1 hx hy (fun h=> t (congrArg G.mat h))
    have hs:=packing (2*y) P (T/2) (by unfold T; positivity) (by positivity) (G.mat 1) ht (fun i hi=> by obtain ⟨i,hs,rfl⟩:= Finset.mem_image.mp hi; exact (e _).mp (v.2 _ hs))
    exact_mod_cast le_trans (le_of_eq (congrArg (Nat.cast (R:=ℝ)) ((Finset.card_image_of_injective A G.mat_injective).symm))) hs -- tune
  obtain ⟨A,u,k⟩ : ∃ A:Finset G.El, V A ∧ ∀ U∈ S, ∃ i∈A, f i U≤T:=by
    by_contra hh; push Not at hh
    have H(n:ℕ):∃ v:Finset G.El,v.card=n∧ V v:=by
      induction n with
      | zero=> exact ⟨∅, rfl,by unfold V; simp⟩
      | succ n ih=>
        obtain ⟨s,p,v⟩:=ih; obtain ⟨i,h,q⟩:=hh s v
        have hi:i∉s:=by intro e; have ht:= q i e; unfold f at ht; rw [sub_self,norm_zero] at ht; exact not_lt.mpr (by unfold T; positivity) ht
        refine ⟨insert i s,by rw [Finset.card_insert_of_notMem hi,p],?_ ,?_⟩
        · intro x hx y hy h; simp only [Finset.coe_insert,mem_insert_iff] at hx hy
          rcases hx with a|a<;> rcases hy with b|b
          · exact (h (a.trans b.symm)).elim
          · rw [a]; unfold f; rw [norm_sub_rev]; exact q y b
          · rw [b]; exact q x a
          exact v.1 a b h
        intro j u; rcases Finset.mem_insert.mp u with r|r; rw [r]; exact h; exact v.2 j r
    obtain ⟨n,hn⟩:= exists_nat_gt B; obtain ⟨A,p,v⟩:= H n; exact (he A v).not_gt (by rwa [p])
  let L(a:G.El):=(fun b:G.El=>a⁻¹*b)⁻¹' G.shell x
  have hL(a): G.probHaar.real (L a)=shellMass G x:= by
    unfold L shellMass; rw [measureReal_def,measureReal_def]; exact congrArg ENNReal.toReal ((measurePreserving_mul_left G.probHaar a⁻¹).measure_preimage (G.shell_meas x).nullMeasurableSet)
  have ht:S ⊆ ⋃ i∈A,L i:=by
    intro i hi; obtain ⟨p,e,v⟩:= k i hi; apply mem_iUnion₂.mpr; refine ⟨p,e,?_⟩
    apply (div_le_iff₀ hp).mpr; rw [G.mat_mul, ← G.mat_one,← inv_mul_cancel p, G.mat_mul,← mul_sub, mul_frob_eq _ _ (G.mat_star_mul _),norm_sub_rev]; exact v
  have hu:= (measureReal_mono (μ:=G.probHaar) ht (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le (μ:=G.probHaar) A L)
  simp only [hL,Finset.sum_const,nsmul_eq_mul] at hu; exact hu.trans (mul_le_mul_of_nonneg_right (he _ u) (measureReal_nonneg))

-- βt≥ chosen lower in using, upper integral. Constants not pressure universal; post-L choose.
def saltWeight (p k:ℝ) (x:G.El):= Real.exp (-k*(G.chord x/p))
lemma salt_cont (p k:ℝ): Continuous (saltWeight G p k):=by unfold saltWeight; fun_prop
lemma salt_le_one (x:G.El)(u p:ℝ)(h:0≤p)(f:0≤u): saltWeight G u p x≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (div_nonneg (G.chord_nonneg _) f))
lemma salt_pay (p:ℝ)(h:0<p): ∃ C:ℝ,1 ≤ C ∧ ∀ x:ℝ,0 < x → ∫ y:G.El,saltWeight G x p y ∂G.probHaar ≤ C * shellMass G x:=by
  classical
  let d:=Module.finrank ℝ G.Mat; let A(i:ℕ):= (3*(i+1):ℝ)^d *Real.exp (-p * i)
  have hA : Summable A:=by
    let T(i:ℕ):= ((i:ℝ)^d* Real.exp (-p*i)); have he:Summable T:=Real.summable_pow_mul_exp_neg_nat_mul d h
    have hp: A=(fun i=> (3^d*Real.exp p)*(T (i+1))):=by
      funext i; dsimp only [A,T]; push_cast; rw [mul_pow, show -p*(i+1:ℝ)=-(p*i)-p by ring,Real.exp_sub]; rw [neg_mul p ↑i]; field_simp
    rw [hp]; exact (((summable_nat_add_iff 1).2 he).mul_left _)
  let C:= (∑' i,A i); refine ⟨max 1 C,le_max_left ..,fun x hx=>?_⟩; let B:=shellMass G x; let F(i:ℕ):=Real.exp (-p*i)
  let Z(i:ℕ):= ((i:ℝ)+1)*x; let S(i:ℕ):=G.shell (Z i)
  obtain ⟨D,hD⟩:= exists_nat_gt (2/x); let K:=Finset.range D; let y:= saltWeight G x p
  let g(i:ℕ):=(S i).indicator (fun _:G.El=>F i)
  have hs(U:G.El):y U ≤ ∑ i∈K,g i U:=by
    let t:=G.chord U/x; let a:= ⌊t⌋₊; have ht:0≤t:=div_nonneg (G.chord_nonneg _) hx.le
    have he: (a:ℝ)≤ t:=Nat.floor_le ht; have hu:t < a+1:= Nat.lt_floor_add_one _
    have hv:a∈K:= Finset.mem_range.mpr (Nat.cast_lt.mp (lt_of_le_of_lt (le_trans he (div_le_div_of_nonneg_right (G.chord_le_two _) hx.le)) hD))
    refine (Finset.single_le_sum (f:=fun i=>g i U) (fun i _=> indicator_nonneg (fun x _=>(Real.exp_pos _).le) _) hv).trans' ?_
    rw [show g a U=F a from indicator_of_mem (show U∈ S a from ((div_lt_iff₀ hx).mp hu).le) _]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left he (by linarith))
  refine le_trans (integral_mono (f:=y) (g:=fun u=>∑ i∈K,g i u) ?_ ?_ hs) ?_
  · exact (salt_cont G x p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact integrable_finsetSum _ fun i _=> (integrable_const _).indicator (G.shell_meas _)
  rw [integral_finsetSum _ (fun i _=>(integrable_const _).indicator (G.shell_meas _))]; refine (Finset.sum_le_sum (g:=fun i=> A i *B) (fun i _=>?_)).trans ?_; swap
  · rw [←Finset.sum_mul]; apply mul_le_mul_of_nonneg_right _ measureReal_nonneg; exact le_trans (hA.sum_le_tsum _ fun i _=>by unfold A; positivity) (le_max_right ..)
  unfold g; rw [integral_indicator (G.shell_meas _),setIntegral_const]; unfold A
  calc G.probHaar.real (S i) • F i ≤ ((2*((i:ℝ)+1)+1)^d*B) * F i:= mul_le_mul_of_nonneg_right (shellMass_ratio G hx (by positivity)) ((Real.exp_pos _).le)
       _ ≤ (3*((i:ℝ)+1))^d * Real.exp (-p*i)* B:= ?_
  rw [mul_right_comm _ B]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _) (Real.exp_pos _).le) measureReal_nonneg

end YM.CF.Fixed.Extensive
