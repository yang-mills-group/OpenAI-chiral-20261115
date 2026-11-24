import SatinFixedContrastNovember4
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Convex.Combination

/-!
# mixture step for an actual point OP-limit

We use convex combinations of THIN stencils refined in their communication spatial
and temporal footprint budgets (down to zero radius). They keep support and ruler
qualifications. Though program still uses choice (as for earlier purchases), needn't
depend on any rates through an ultrafilter, nor on normalizing by the read answer.
Here's the Hilbert-norm-distance construction using minimization and tolerance.
It's good even for the full operator price (strong* with warm and cool costs later).
-/

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM
namespace Sifter
open Function Filter Metric Set TopologicalSpace
open scoped lp Topology BigOperators InnerProductSpace NNReal ENNReal Classical
structure Scoop where
  weight : ℕ→ℝ
  take : Finset ℕ
  positive :∀ i∈take,0≤ weight i
  total : take.sum weight=1

def Scoop.recipe {E:Type*}[AddCommMonoid E][SMul ℂ E](u:Scoop)(F:ℕ→E):E:= ∑ i∈u.take,(↑(u.weight i):ℂ) • (F i)

section convex
variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
private lemma clump {F:ℕ→H} (C:ℝ) (p:∀ i,‖F i‖≤C) : ∃ v:ℕ→H, (∀ i, v i∈convexHull ℝ (Set.range fun k=> F (i+k)))∧ CauchySeq v := by
 let Q(i:ℕ):= convexHull ℝ (Set.range fun k=>F (i+k))
 let D(i):=closure (Q i)
 have e(i): F (i+0)∈D i:= subset_closure (subset_convexHull ℝ _ (mem_range_self (f:=fun k=>F (i+k)) 0)) -- implicit?
 have h(i): Convex ℝ (D i):= (convex_convexHull ℝ _).closure
 have he: Antitone D:=by intro i j p; apply closure_mono; apply convexHull_mono; rintro _ ⟨k,rfl⟩; exact ⟨j-i+k,congrArg F (by omega)⟩
 choose v t y using fun i=> exists_norm_eq_iInf_of_complete_convex ⟨_,e i⟩ (isClosed_closure.isComplete) (h i) 0
 have hy(i)(x:H)(u:x∈ D i) : ‖v i‖≤‖x‖:=by
   have hp := (le_of_eq (y i)).trans (ciInf_le ⟨0, Set.forall_mem_range.2 (fun (_:D i)=> norm_nonneg _)⟩ (⟨x,u⟩:D i)); simpa using hp
 let r(i):= ‖v i‖^2
 have hn(i:ℕ):‖v i‖≤C:=(hy i _ (e i)).trans (p _)
 have hq:Monotone r:= fun _ _ u=> pow_le_pow_left₀ (norm_nonneg _) (hy _ _ (he u (t _))) _
 have hB:BddAbove (Set.range r):=⟨C^2,Set.forall_mem_range.mpr fun i=>pow_le_pow_left₀ (norm_nonneg _) (hn i) _⟩
 have hc: CauchySeq r:= (tendsto_atTop_ciSup hq hB).cauchySeq
 have hu {i j:ℕ}(e:i≤j): 4* r i ≤ ‖v i+v j‖^2:= by
    have p:(1/2:ℝ) • (v i+v j)∈D i:= by rw [smul_add]; exact h i (t _) (he e (t _)) (by norm_num) (by norm_num) (by norm_num)
    have h:=pow_le_pow_left₀ (norm_nonneg _) (hy i _ p) 2; rw [norm_smul, Real.norm_of_nonneg (by norm_num: (0:ℝ)≤1/2),mul_pow] at h; dsimp [r]; linarith
 have hv:CauchySeq v:=by
    apply Metric.cauchySeq_iff'.2; intro e p
    obtain ⟨N,t⟩:=Metric.cauchySeq_iff'.1 hc (e^2/2) (by positivity)
    refine ⟨N,fun n v'=>?_⟩; have hp:=t n v'; have hy:= hu v'; have hx:= parallelogram_law_with_norm ℝ (v N) (v n); rw [Real.dist_eq] at hp; have hl:= (abs_lt.mp hp).2; rw [dist_comm,dist_eq_norm]; unfold r at hl hy; exact (sq_lt_sq₀ (norm_nonneg _) p.le).mp (by linarith)
 choose z k h using fun i=> Metric.mem_closure_iff.1 (t i) (1/(i+1:ℝ)) (by positivity)
 refine ⟨z,k,(hv.tendsto_limUnder.congr_dist (squeeze_zero (fun i=> dist_nonneg) (fun i=> (h i).le) tendsto_one_div_add_atTop_nhds_zero_nat)).cauchySeq⟩
private lemma harvest {F:ℕ→H} (C:ℝ) (p:∀ i,‖F i‖≤C) : ∃ S:ℕ→ Scoop,
    CauchySeq (fun i:ℕ=> (∑ k∈(S i).take,(S i).weight k • F (i+k) : H)) := by
  obtain ⟨v,t,h⟩:=clump C p
  simp_rw [convexHull_range_eq_exists_affineCombination, Set.mem_setOf] at t
  choose s w he ht x using t
  let U(i):Scoop:=⟨w i,s i,he i,ht i⟩; refine ⟨U,?_⟩; have hp(i:ℕ): v i=∑ k∈s i,w i k • F (i+k):= by
      rw [←x i,affineCombination_eq_centerMass (ht i)]; exact Finset.centerMass_eq_of_sum_1 _ _ (ht i)
  convert h using 1; exact (funext hp).symm
end convex
variable (X:Hilbert)
namespace Scoop
variable (u:Scoop)(A:ℕ→X.Op)
lemma evaluates (v:X) : (u.recipe A) v=u.recipe (fun i=>A i v) := by
  unfold recipe; simp_rw [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]
lemma reflects : (u.recipe A).adjoint=u.recipe (fun i=>(A i).adjoint):= by
  unfold recipe; simp only [map_sum, map_smulₛₗ, Complex.conj_ofReal]
lemma cap {E: Type*}[SeminormedAddCommGroup E][NormedSpace ℂ E] {F:ℕ→E}{M:ℝ}(p: ∀ i∈u.take,‖F i‖≤ M) : ‖u.recipe F‖≤M := by
  unfold recipe; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun i=>u.weight i*M) (fun i hi=>?_)).trans_eq ?_)
  · rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (u.positive _ hi)]; exact mul_le_mul_of_nonneg_left (p i hi) (u.positive _ hi)
  rw [←Finset.sum_mul,u.total,one_mul]
end Scoop
section converges
private lemma denseCauchy (F:ℕ→X.Op) (M:ℝ)(q:0<M)(p:∀ i,‖F i‖≤M)
    (D:ℕ→ X)(g:DenseRange D)(h:∀ i,CauchySeq (fun n:ℕ=> F n (D i))) : ∀ v:X,CauchySeq (fun n:ℕ=> F n v) := by
  intro v; apply Metric.cauchySeq_iff.mpr; intro ε u; obtain ⟨m,g⟩:= g.exists_dist_lt v (show 0<ε/(4*M) by positivity)
  obtain ⟨N,w⟩:= Metric.cauchySeq_iff.1 (h m) (ε/4) (by positivity)
  have he(i:ℕ): dist (F i v) (F i (D m)) ≤ ε/4 := by
    have h:F i (v-D m)=_:= map_sub (F i) v (D m)
    rw [dist_eq_norm,←h]; rw [dist_eq_norm] at g
    refine ((F i).le_opNorm _).trans ((mul_le_mul (p i) g.le (norm_nonneg _) q.le).trans_eq ?_); field
  refine ⟨N,fun j hj i hi=>?_⟩; have ht:= he i; rw [dist_comm] at ht
  exact lt_of_le_of_lt (dist_triangle4 _ (F j (D m)) (F i (D m)) _) (by linarith only [he j,w j hj i hi,ht,u]) -- name

private lemma closePointwise (F:ℕ→X.Op) (M:ℝ) (p:∀ i,‖F i‖≤M)(h:∀ v:X,CauchySeq (fun i:ℕ=> F i v)) : ∃ L:X.Op,∀ v:X,Tendsto (fun i:ℕ=> F i v) atTop (𝓝 (L v)):= by
  choose L hp using fun v:X=> cauchySeq_tendsto_of_complete (h v)
  let L': (X) →ₗ[ℂ] X:={
    toFun:=L
    map_add':=fun v w=> tendsto_nhds_unique (hp (v+w)) ((hp v|>.add (hp w)).congr fun i=> (map_add (F i) v w).symm)
    map_smul':=fun c v=> tendsto_nhds_unique (hp _) ((hp v |>.const_smul c).congr fun i=> (map_smul (F i) c v).symm) }
  exact ⟨L'.mkContinuous M fun v=> le_of_tendsto (hp v|>.norm) (Eventually.of_forall fun i=> ((F i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (p i) (norm_nonneg _))), hp⟩
end converges

local notation "H'"=> lp (fun _ : ℕ => X.space) 2
/-- A height-mixture messenger. Run this at the very `B` operator costs on the
election. If using `Classical.choose` keep the same mix throughout, also on all
continuing prices. One distinguished orientation plus its genuine adjoint. -/
theorem scoop (v:ℕ→ X.Op)(p:SeparableSpace X.space)(C:ℝ)(q:0<C)(h:∀i,‖v i‖≤C): ∃ B:ℕ→ Scoop,∃ w:X.Op,∀ z:X,
    Tendsto (fun i:ℕ=> (Scoop.recipe (B i) fun k=> v (i+k)) z) atTop (𝓝 (w z))∧
    Tendsto (fun i:ℕ=> (Scoop.recipe (B i) fun k=> v (i+k)).adjoint z) atTop (𝓝 (w.adjoint z)):= by
  let D:= denseSeq X.space; obtain ⟨I,W⟩:=exists_surjective_nat (ℕ × Bool)
  let x(i:ℕ):X:= D (I i).1
  let S(n:ℕ)(i:ℕ) : X.Op:= if (I i).2 then (v n).adjoint else v n
  let r(i:ℕ):ℝ:= (1/2:ℝ)^i/(1+‖x i‖)
  let T (n i:ℕ):= (r i:ℂ) • S n i (x i)
  have p(i:ℕ):0<r i:=by unfold r; positivity
  let L(i:ℕ):=C*(1/2:ℝ)^i; let y(n i:ℕ):H':=lp.single 2 i (T n i)
  have hT(n i:ℕ): ‖y n i‖≤ L i:= by
    have hv(j:ℕ):‖S j i‖ ≤ C:= by unfold S; split_ifs; rw [LinearIsometryEquiv.norm_map]; exact h j; exact h j
    rw [show y n i=lp.single 2 i (T n i) from rfl,lp.norm_single (by norm_num : (0:ℝ≥0∞)<2)]
    unfold T; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (p i).le]; refine (mul_le_mul_of_nonneg_left (((S n i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hv n) (norm_nonneg _))) (p i).le).trans ?_
    have ha:r i≥0:= (p i).le; have he:r i*(1+‖x i‖)=(1/2:ℝ)^i:= div_mul_cancel₀ _ (by positivity)
    unfold L; rw [←he]; nlinarith only [q,ha]
  let Y(n:ℕ):H' := ∑' i,y n i
  have hs:HasSum L (C*2):= hasSum_geometric_two.mul_left C
  have hy(i):Summable (fun k=> ‖y i k‖):= Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (hT i) hs.summable
  have hz(i):Summable (y i):= (hy i).of_norm
  have hh(i:ℕ):‖Y i‖≤C*2:= (norm_tsum_le_tsum_norm (hy i)).trans ((Summable.tsum_le_tsum (hT i) (hy i) hs.summable).trans_eq hs.tsum_eq) -- name
  letI : InnerProductSpace ℝ (H') := InnerProductSpace.complexToReal
  obtain ⟨B,H⟩:= harvest (F:=Y) (C*2) hh
  let g(i:ℕ):= Scoop.recipe (B i) fun k=> v (i+k); let g'(i:ℕ):=(g i).adjoint
  let a(i:ℕ):H':= ∑ j∈(B i).take, (B i).weight j • Y (i+j)
  let F(i:ℕ)(j:ℕ): X.Op:= if (I j).2 then g' i else g i
  have ha(j:ℕ): CauchySeq (fun i:ℕ=> F i j (x j)):= by
    let P':=(lp.evalCLM ℂ _ _ j : H' →L[ℂ] X); let Λ:= limUnder atTop a; have hb:= (lp.evalCLM ℂ _ _ j).continuous.continuousAt.tendsto.comp (show Tendsto a atTop (𝓝 Λ) from H.tendsto_limUnder)
    have hc(i): P' (Y i)= T i j:= by
       unfold Y; rw [P'.map_tsum (hz i),tsum_eq_single j]; swap; · intro b u; exact lp.single_apply_ne (E:=fun _=>X.space) 2 _ (T i b) u.symm
       exact lp.single_apply_self (E:=fun _=>X.space) 2 _ (T i j)
    let w:ℂ:=r j; have hf(i): P' (a i)= w • F i j (x j):= by
      have he(k:ℝ)(x:H'):(k:ℂ) • x=k • x:=Complex.coe_smul _ _
      unfold a F; split_ifs with e 
      · simp_rw [← he,map_sum,map_smul,hc,T,S,if_pos e]; unfold g' g; rw [(B i).reflects X _] -- order X?
        rw [Scoop.evaluates X]; unfold Scoop.recipe; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm _ w _
      simp_rw [← he,map_sum,map_smul,hc,T,S,if_neg e]; unfold g; rw [Scoop.evaluates X]; unfold Scoop.recipe; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm _ w _
    apply ((hb.const_smul w⁻¹).congr fun i=> ?_).cauchySeq -- adjust
    dsimp only [Function.comp_apply]; change w⁻¹ • P' (a i)= _; rw [hf]; exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (p j).ne') _
  have hm(i:ℕ):‖g i‖ ≤ C:= (B i).cap fun i _=>h _
  obtain ⟨L,t⟩:= closePointwise X g C hm (denseCauchy X g C q hm D (denseRange_denseSeq _) (fun i=> by obtain ⟨j,e⟩:= W (i,false); simpa only [x,F,e,Bool.false_eq_true, ↓reduceIte] using ha j))
  have hm'(i:ℕ):‖g' i‖ ≤ C:=(ContinuousLinearMap.adjoint.norm_map _).trans_le (hm i)
  obtain ⟨K,u⟩:= closePointwise X g' C hm' (denseCauchy X g' C q hm' D (denseRange_denseSeq _) (fun i=> by obtain ⟨j,e⟩:= W (i,true); simpa only [x,F,e, ↓reduceIte] using ha j))
  refine ⟨B,L,fun z=>⟨t _,?_⟩⟩
  have ht:K=L.adjoint:= by
    ext1 z; apply ext_inner_left ℂ; intro y
    rw [ContinuousLinearMap.adjoint_inner_right] -- maybe adjoint_inner_left
    exact tendsto_nhds_unique ((tendsto_const_nhds (x:=y)).inner (𝕜:=ℂ) (u z)) (((t y).inner (tendsto_const_nhds (x:=z))).congr fun i=> (ContinuousLinearMap.adjoint_inner_right (g i) y z).symm)
  rw [←ht]; exact u z
#print axioms scoop
end Sifter
end YM
