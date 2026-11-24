import YM.CF.BProof.Extension.Sphere
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
/-! Smooth version for RCLike; permits relative path and square fillings. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Extension.Mar
open Function Filter Metric Set Submodule Module RCLike
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexConjugate Classical ContDiff

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
abbrev Suit (S:Set X)(f:X→Y):Prop:=∀ x∈S,ContDiffAt ℝ ∞ f x
lemma suit_cost (S:Set X)(F:X→Y)(h:IsCompact S)(p:Convex ℝ S)(e:Suit S F) : ∃ C:ℝ,0<C∧ Lip S C F:=by
 have ht:ContinuousOn (fun x=> ‖fderiv ℝ F x‖) S:= fun x hx=> ((e x hx).continuousAt_fderiv (by simp)).norm.continuousWithinAt
 obtain ⟨C,hC⟩:= h.bddAbove_image ht; refine ⟨max C 1, one_pos.trans_le (le_max_right ..),fun x hx y hy=>?_⟩
 rw [dist_eq_norm]; exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f':= fderiv ℝ F) (fun x hx=> ((e x hx).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt) (fun x hx=> (hC ⟨x,hx,rfl⟩).trans (le_max_left ..)) p hy hx
variable [FiniteDimensional ℝ X] {K : Type*} [RCLike K]
-- use compatibility already for Euclidean canonical real operations.
omit [NormedSpace ℝ Y]
-- need Inner overrides existing NormedSpace ℝ Y; section ends instead.
end YM.CF.BProof.Extension.Mar
namespace YM.CF.BProof.Extension.Mar
open Function Filter Metric Set Submodule Module RCLike
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexConjugate Classical ContDiff
set_option linter.unusedSectionVars false
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {𝕂 : Type*}[RCLike 𝕂]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [InnerProductSpace 𝕂 Y] [FiniteDimensional ℝ Y][FiniteDimensional 𝕂 Y][IsScalarTower ℝ 𝕂 Y]
-- compatibility hypothesis
abbrev Realize (𝕂 Y: Type*)[RCLike 𝕂] [Inner ℝ Y][Inner 𝕂 Y]:Prop:=∀ (x y:Y),⟪x,y⟫_ℝ=re ⟪x,y⟫_𝕂
lemma spanO {ι : Type*} {f : ι → Y} {x : Y} : x∈ (span 𝕂 (range f))ᗮ ↔ ∀ i, ⟪f i,x⟫_𝕂=0 := by
 constructor; exact fun h i=> inner_right_of_mem_orthogonal (subset_span (mem_range_self i)) h
 intro h; apply (mem_orthogonal ..).mpr; intro y hy; induction hy using Submodule.span_induction with
 | mem y hy => obtain ⟨i,rfl⟩:=hy; exact h i
 | zero=> simp
 | add _ _ _ _ h k=> simp [inner_add_left,h,k]
 | smul _ _ _ h=> simp [inner_smul_left,h]

private lemma compat (u:Realize 𝕂 Y)(V : Submodule 𝕂 Y) (x : Y) :
    (V.restrictScalars ℝ).starProjection x=V.starProjection x := by
 apply eq_starProjection_of_mem_orthogonal (by exact (V.orthogonalProjectionOnto x).property)
 intro w hw
 rw [u w (x-V.starProjection x),inner_right_of_mem_orthogonal (show w∈ V from hw) (sub_starProjection_mem_orthogonal x)]; simp

private lemma currency {J : Type*} [Fintype J] (F : J→Y) (h : Orthonormal 𝕂 F) (x : Y) :
    (span 𝕂 (range F)).starProjection x= ∑ i,⟪F i,x⟫_𝕂 • F i := by
 apply eq_starProjection_of_mem_orthogonal
 · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span (mem_range_self i))
 apply spanO.mpr; intro i
 simp_rw [inner_sub_right,inner_sum,inner_smul_right,orthonormal_iff_ite.mp h]; simp

private lemma projectionLip (u:Realize 𝕂 Y){J : Type*} [Fintype J] (F : X→J→Y)(S : Set X)(h : ∀ x∈ S,Orthonormal 𝕂 (F x)) (K : ℝ) (k : 0≤K) (p : ∀ i,Lip S K (fun x=> F x i)) :
    Lip S (2*K*Fintype.card J) (fun x=> ((span 𝕂 (range (F x)))ᗮ.restrictScalars ℝ).starProjection) := by
 intro x hx y hy; apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
 intro z; rw [ContinuousLinearMap.sub_apply,compat u,compat u]; simp only [Submodule.starProjection_orthogonal', ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply]; rw [currency (F x) (h x hx),currency (F y) (h y hy),sub_sub_sub_cancel_left,norm_sub_rev,← Finset.sum_sub_distrib]
 refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=> (K*dist x y*‖z‖)*2) (fun i _=> ?_)).trans_eq ?_)
 · let a:= F x i; let b:=F y i; change ‖⟪a,z⟫_𝕂 • a-⟪b,z⟫_𝕂 • b‖≤_
   have ha : ‖a‖=1:= (h x hx).1 _; have hb: ‖b‖=1:=(h y hy).1 _
   rw [show ⟪a,z⟫_𝕂 • a-⟪b,z⟫_𝕂 • b=⟪a-b,z⟫_𝕂 • a+⟪b,z⟫_𝕂 • (a-b) by rw [smul_sub,inner_sub_left, sub_smul]; abel]
   apply (norm_add_le ..).trans; rw [norm_smul,norm_smul,ha,mul_one,mul_two]
   apply add_le_add
   · exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_right (p i x hx y hy) (norm_nonneg _))
   rw [mul_comm ‖⟪b,z⟫_𝕂‖]; exact mul_le_mul (p i x hx y hy) ((norm_inner_le_norm ..).trans (by rw [hb,one_mul])) (norm_nonneg _) (by positivity)
 simp; ring

private lemma codim (𝕂) [RCLike 𝕂] [InnerProductSpace 𝕂 Y][FiniteDimensional 𝕂 Y][IsScalarTower ℝ 𝕂 Y] {J : Type*} [Fintype J] (F : J→Y) (h : Orthonormal 𝕂 F) (hk : Fintype.card J+2 ≤ finrank 𝕂 Y) :
    2*finrank ℝ 𝕂 ≤ finrank ℝ ((span 𝕂 (range F))ᗮ.restrictScalars ℝ) := by
 let V:= (span 𝕂 (range F)); let L:= Vᗮ
 have he:=V.finrank_add_finrank_orthogonal; rw [show finrank 𝕂 V=Fintype.card J from finrank_span_eq_card h.linearIndependent] at he
 have hm:= Module.finrank_mul_finrank ℝ 𝕂 L
 change _≤ finrank ℝ L; rw [← hm,Nat.mul_comm 2]; gcongr; unfold L; omega
-- taper on square of norm
private abbrev taper (r:ℝ):= Real.smoothTransition (2*(1-r))
private theorem expanding (hR:Realize 𝕂 Y) {J:Type*}[Fintype J] (d: finrank ℝ X<2*finrank ℝ 𝕂)(n:Fintype.card J+2≤finrank 𝕂 Y)
 (S T:Set X)(h:IsCompact S)(p:Convex ℝ S)(t:T⊆S)(V:X→J→Y)(v:∀ i,Suit S (fun x=>V x i))(H:∀ x∈S, Orthonormal 𝕂 (V x))(F:X→Y)(e:Suit S F)
 (W:∀ x∈T, ‖F x‖=1 ∧ F x∈ (span 𝕂 (range (V x)))ᗮ) : ∃ Y':X→Y,Suit S Y'∧ EqOn F Y' T∧ ∀ x∈S,‖Y' x‖=1∧ Y' x ∈ (span 𝕂 (range (V x)))ᗮ := by
 let P(x:X):=span 𝕂 (range (V x)); let U(x:X):= (P x)ᗮ.restrictScalars ℝ
 let L(x:X)(y:Y):= y - ∑ i:J, ⟪V x i,y⟫_𝕂 • V x i
 have he(x)(hx:x∈ S)(y:Y): (U x).starProjection y=L x y:=by rw [show U x=(P x)ᗮ.restrictScalars ℝ from rfl, compat hR, Submodule.starProjection_orthogonal',ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,currency _ (H x hx)]
 have hx(f:X→Y)(h:Suit S f):Suit S (fun x=>L x (f x)):=fun x hx=>ContDiffAt.sub (h x hx) (ContDiffAt.sum (fun i _=> ((v i x hx).inner 𝕂 (h x hx)).smul (v i x hx))) -- tune
 let f(x:X):=L x (F x); have hf: Suit S f:= hx F e
 have hU(x)(hx:x∈ S)(y:Y): L x y∈ U x:=he x hx y ▸ by simp
 choose a ha hc using (fun i:J=> suit_cost S _ h p (v i)); let r:ℝ:= 1+ ∑ i:J,a i; have hg:0<r:= lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> (ha i).le)); have hr : Lip S (2*r*Fintype.card J) (fun x=>(U x).starProjection) := projectionLip hR V S H r hg.le (fun i=> (hc i).mono (Subset.refl _) ((Finset.single_le_sum (fun i _=> (ha i).le) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)))
 obtain ⟨a,ha,ht⟩:=suit_cost S _ h p (show Suit S (fun x=>-f x) from fun x h=> (hf x h).neg)
 obtain ⟨b,hb⟩:= h.isBounded.subset_closedBall 0
 let c:=2*r*Fintype.card J; obtain ⟨g,hg',L'⟩:= avoids (X:=X) (Y:=Y) (max b 1) (1+c) a (1/4) (zero_lt_one.trans_le (le_max_right ..)) (by dsimp only [c]; positivity) ha (by norm_num) (by norm_num); obtain ⟨w,hw,K⟩:= L' S U (fun x=>-f x) (hb.trans (closedBall_subset_closedBall (le_max_left ..))) (hr.mono (Subset.refl _) (le_add_of_nonneg_left zero_le_one)) ht (fun x hx=> d.trans_le (codim 𝕂 (V x) (H x hx) n))
 let A(x:X):=f x+taper (‖f x‖^2) • L x w
 have hs : Suit S A:=fun x h=> by refine (hf x h).add ((Real.smoothTransition.contDiffAt.comp x (contDiffAt_const.mul (contDiffAt_const.sub ((hf x h).norm_sq ℝ)))).smul (hx _ (fun _ _=>contDiffAt_const) x h))
 have he'(x)(p:x∈S): 0<‖A x‖:=by
    let r:= ‖f x‖; by_cases l:r≤1/2
    · have ha': taper (r^2)=1:=Real.smoothTransition.one_of_one_le (by have hi:0≤r:=norm_nonneg _; nlinarith)
      change 0<‖f x+taper (r^2) • _‖; rw [ha',one_smul,←he x p w, add_comm, ← sub_neg_eq_add]; exact hg'.trans_le (K x p)
    apply lt_of_lt_of_le (b:=1/4) (by norm_num); unfold A; rw [← sub_neg_eq_add]; apply le_trans _ (norm_sub_norm_le ..); rw [norm_neg,norm_smul, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    calc
      _ ≤ r-1/4:=by linarith
      _ ≤ r- _ := by refine sub_le_sub_left (le_trans (mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one ..)) ?_) _; rw [← he x p w]; exact ((U x).norm_starProjection_apply_le _).trans hw
 let V'(x:X):=‖A x‖⁻¹ • A x; refine ⟨V',fun x hx=> (((hs x hx).norm ℝ (norm_pos_iff.mp (he' x hx))).inv (he' x hx).ne').smul (hs x hx), fun x hx=> ?_,fun x hx=>?_⟩
 · have hh:=W x hx; have heq:f x=F x:=(he x (t hx) _).symm.trans (Submodule.starProjection_eq_self_iff.mpr (show F x∈U x from hh.2)); unfold V' A; rw [heq,hh.1,one_pow,taper,sub_self, mul_zero,Real.smoothTransition.zero,zero_smul,add_zero,hh.1,inv_one,one_smul] -- tune reducible
 unfold V'; refine ⟨?_,show _∈ U x from ((U x).smul_mem _ ((U x).add_mem (hU x hx _) ((U x).smul_mem _ (hU x hx w))))⟩; rw [norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ (he' x hx).ne']
-- no continuity asserted outside S
lemma ascent (u:Realize 𝕂 Y)(S T:Set X)(h:IsCompact S)(p:Convex ℝ S)(t:T⊆S)(n:ℕ)(H:n<finrank 𝕂 Y)(k:finrank ℝ X<2*finrank ℝ 𝕂)
 (F:X→Fin n→Y)(e:∀ i,Suit S (fun x=>F x i))(W:∀ x∈ T, Orthonormal 𝕂 (F x)): ∃ G:X→Fin n→Y,(∀ i,Suit S (fun x=> G x i))∧ EqOn F G T∧ ∀ x∈ S, Orthonormal 𝕂 (G x) := by
 induction n with
 | zero=> exact ⟨F,e,fun _ _=>rfl,fun x hx=>⟨finZeroElim,fun ⦃i⦄=>i.elim0⟩⟩
 | succ n ih=>
    obtain ⟨g,hg,hg',he⟩:= ih (by omega) (fun x i=> F x i.succ) (fun i=>e i.succ) (fun x hx=> (W x hx).comp _ fun _ _=>Fin.succ_inj.mp)
    obtain ⟨a,ha,l,L⟩:= expanding u k (by simp; exact H) S T h p t g hg he (fun x=>F x 0) (e 0) (fun x hx=> ⟨(W x hx).1 _,spanO.mpr (fun i=>by rw [←hg' hx]; exact (W x hx).2 (Fin.succ_ne_zero _))⟩)
    refine ⟨fun x=> Fin.cons (a x) (g x),fun i=> Fin.cases ha (fun i=> by simpa using hg i) i,fun x hx=>funext (fun i=> Fin.cases (l hx) (fun j => by simpa using congrFun (hg' hx) j) i),fun x hx=>?_⟩
    rw [orthonormal_iff_ite]; intro i j; have hu:= spanO.mp (L x hx).2
    refine Fin.cases ?_ (fun i=>?_) i
    · refine Fin.cases ?_ (fun j=>?_) j; simp [inner_self_eq_norm_sq_to_K,(L x hx).1]; simp only [Fin.cons_zero,Fin.cons_succ,if_neg (Fin.succ_ne_zero j).symm]; exact inner_eq_zero_symm.mpr (hu j)
    refine Fin.cases ?_ (fun j=>?_) j; rw [if_neg (Fin.succ_ne_zero _)]; exact hu i; simpa using orthonormal_iff_ite.mp (he x hx) i j
end YM.CF.BProof.Extension.Mar
