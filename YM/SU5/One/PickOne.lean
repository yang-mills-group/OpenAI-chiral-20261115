import VerifiedSatinSelectedSectors

/-!
# Isolate an advance from its separated square system
Purely functional argument independent of how steps obtained or continuity of Fock coefficients. No common-phase choice between different applications of theorem: use single subsequence simultaneously along path in application. Note: if data below given for A with its self under translation, uniqueness may be up to sign; this theorem only claims subselection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pique
open Function Filter NormedSpace Metric ContinuousLinearMap
open scoped Topology BigOperators
variable {E F G:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
 [NormedAddCommGroup F][NormedSpace ℂ F]
 [NormedAddCommGroup G][NormedSpace ℂ G]

/-- A norming set of point evaluations (includes spatial arguments, not topologized or countable). -/
structure Norming {I:Type*}(f:I→F→ₗ[ℂ]ℂ) : Prop where
 below (i:I) (x) : ‖f i x‖≤ ‖x‖
 above {x:F}{r:ℝ}: 0 ≤ r → (∀ i,‖f i x‖ ≤ r)→ ‖x‖≤r

lemma normUp (A:E→ₗ[ℂ]F)(C:ℝ)(h:∀ x, ‖x‖ ≤ (1:ℝ) → ‖A x‖ ≤ C) (x:E): ‖A x‖ ≤ C*‖x‖:=by
 by_cases p:x=0
 · simp [p]
 have he:= norm_pos_iff.mpr p; let z:ℂ:= ↑(‖x‖⁻¹)
 have hx : ‖z • x‖=1:=by simp [norm_smul,z,he.ne']
 have hv : ‖x‖⁻¹ * ‖A x‖≤ C:=by simpa [z,norm_smul] using h _ hx.le
 rwa [←div_eq_inv_mul, div_le_iff₀ he] at hv

section
variable {I J:Type*}{φ:I→ F→ₗ[ℂ]ℂ}{ψ:J→G→ₗ[ℂ]ℂ}
variable (P:Norming φ)(Q:Norming ψ)
-- don't need B linear; specifically copied A with inverted displacements.
variable (A:ℕ→E→ₗ[ℂ]F)(B:ℕ→E→G)(w:ℝ)(hw:0<w)
   (R: ∀ i x, ‖A i x‖ ≤ w*‖B i x‖)
local notation "α" i:max j:max x:max=> φ j (A i x)
local notation "β" i:max j:max x:max=> ψ j (B i x)
include P Q R hw
lemma slice_extract (i:ℕ) {L:ℝ}(u:0<L)(h:∀ x,‖x‖ ≤1→ ∀ (a:I)(b:J),‖φ a (A i x) * ψ b (B i x)‖ ≤ L*(L/w)) : ∀ x, ‖x‖≤ 1→ ‖A i x‖ ≤ L:=by
 intro x c; by_contra! lk
 have ha:∃ a, L<‖φ a (A i x)‖:=by by_contra! hh; exact lk.not_ge (P.above u.le hh)
 have hb: L/w < ‖B i x‖:= (div_lt_iff₀ hw).mpr ((lk.trans_le (R i x)).trans_eq (mul_comm _ _))
 have hh:∃ b,L/w<‖ψ b (B i x)‖:=by by_contra! hv; exact hb.not_ge (Q.above (by positivity) hv)
 obtain ⟨a,l⟩:=ha; obtain ⟨b,p⟩:=hh
 have hc:= h x c a b; rw [norm_mul] at hc; exact not_le_of_gt (mul_lt_mul_of_pos_left p u|>.trans_le (mul_le_mul_of_nonneg_right l.le (norm_nonneg _))) hc

omit P Q R hw
noncomputable def includeContinuous (f:E→ₗ[ℂ]F):E→L[ℂ]F:=by
 classical exact if h:Continuous f then ⟨f,h⟩ else 0
lemma unchanged {f:E→ₗ[ℂ]F}(h:Continuous f): (includeContinuous f).toLinearMap=f:=by unfold includeContinuous; rw [dif_pos h]
include P Q R hw
variable (v:ℝ) (hv: 0≤v)(S:∀ i x, ‖B i x‖ ≤ v*‖A i x‖)
variable (X:I→J→E→E→ℂ)
 (slices: ∀ ε:ℝ,0<ε→∀ᶠ i in atTop, ∀ a b x y, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖φ a (A i x)*ψ b (B i y)-X a b x y‖ ≤ ε)
include slices
local notation "f" i:max=> includeContinuous (A i)
variable (cost: ∃ D:ℝ,∀ a b x y, ‖x‖≤1→‖y‖ ≤1→ ‖X a b x y‖ ≤ D)
include cost
lemma fallsIn : ∃ C:ℝ,0<C ∧ ∀ᶠ i in atTop, (includeContinuous (A i)).toLinearMap=A i ∧ ‖includeContinuous (A i)‖≤C:=by
 obtain ⟨D,h⟩:= cost; let C:= max D 0+1+w
 have ht:0<C:=by dsimp [C]; linarith [le_max_right D 0];
 refine ⟨C,ht,(slices 1 zero_lt_one).mono fun i v=>?_⟩
 have hs:∀ x,‖x‖ ≤ 1→ ‖A i x‖ ≤ C:= slice_extract P Q A B w hw R i ht fun x c a b=>by
    specialize v a b x x c c
    refine ((norm_le_norm_sub_add ..).trans (add_le_add v (h a b x x c c))).trans ?_
    have hb :1 ≤ C/w:=(one_le_div hw).mpr (by dsimp [C]; linarith [le_max_right D 0])
    exact (show 1+D≤ C by dsimp [C]; linarith [le_max_left D 0]).trans (le_mul_of_one_le_right ht.le hb)
 let F':=(A i).mkContinuous C (normUp _ C hs); have hc : Continuous (A i):= F'.continuous
 have hu:= unchanged hc
 refine ⟨hu,(f i).opNorm_le_bound ht.le ?_⟩; intro x
 change ‖((f i).toLinearMap) x‖≤ _; rw [hu]; exact normUp _ C hs x

include hv S
variable [CompleteSpace F]
lemma resolution: ∃ n:ℕ→ℕ, StrictMono n ∧ ∃ F:E→L[ℂ] F,Tendsto (fun i=>includeContinuous (A (n i))) atTop (𝓝 F) := by
 obtain ⟨C,h,u⟩:= fallsIn P Q A B w hw R X slices cost
 have hc(i:ℕ)(e: (f i).toLinearMap=A i)(v:‖f i‖ ≤ C)(x:E)(l:‖x‖ ≤ 1): ‖A i x‖ ≤ C:=by
   rw [←e]; exact ((f i).le_opNorm x).trans ((mul_le_mul v l (norm_nonneg _) h.le).trans_eq (mul_one _))
 by_cases t:∀ a b x y,‖x‖ ≤ 1→‖y‖ ≤ 1→ X a b x y=0
 · refine ⟨id,strictMono_id,0,Metric.tendsto_nhds.mpr fun ε κ=>?_⟩
   let l:=ε/2; have hp:0<l:=by unfold l; positivity
   filter_upwards [slices (l*(l/w)) (by positivity),u] with i q v
   rw [dist_zero_right]; change ‖f i‖ < ε
   apply lt_of_le_of_lt _ (show l<ε from half_lt_self κ); apply ContinuousLinearMap.opNorm_le_bound _ hp.le
   let U:= (f i).toLinearMap
   have ht:∀ x,‖x‖ ≤ 1→‖U x‖ ≤ l:=by rw [show U=A i from v.1]; exact slice_extract P Q A B w hw R i hp (fun x c a b=>by simpa only [t a b x x c c,sub_zero] using q a b x x c c)
   exact normUp U l ht
 push Not at t; obtain ⟨a,b,x,y,p,q,g⟩:= t
 let c(i:ℕ):=ψ b (B i y)
 have B':∃ᶠ i in atTop,c i ∈ Metric.closedBall 0 (v*C):= (u.mono (fun i ⟨e,u⟩=>mem_closedBall_zero_iff.mpr ((Q.below b (B i y)).trans ((S i y).trans (mul_le_mul_of_nonneg_left (hc i e u y q) hv))))).frequently
 obtain ⟨d,l,n,k,z⟩:= (isCompact_closedBall _ _).tendsto_subseq' B'
 have V₀:= k.tendsto_atTop
 have d' : d≠0:=by
   intro he; subst d
   have he : Tendsto (fun i=>‖φ a (A (n i) x)* ψ b (B (n i) y)‖) atTop (𝓝 0):=by
      refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ((V₀.eventually u).mono fun i ⟨t,g⟩=> ?_) (show Tendsto (fun i=> C*‖c (n i)‖) atTop _ from ?_)
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_right ((P.below a _).trans (hc (n i) t g x p)) (norm_nonneg _)
      simpa only [norm_zero, Function.comp_apply,mul_zero] using z.norm.const_mul C
   have ht := tendsto_nhds_unique (show Tendsto (fun i=>φ a (A (n i) x)*ψ b (B (n i) y)) atTop (𝓝 (X a b x y)) from ?_).norm he
   · exact g (norm_eq_zero.mp ht)
   apply Metric.tendsto_nhds.mpr; intro ε u
   filter_upwards [V₀.eventually (slices (ε/2) (by positivity))] with i w
   rw [dist_eq_norm]; exact (w a b x y p q).trans_lt (half_lt_self u)
 -- c * sequence Cauchy, divide by d; avoids eps powers.
 let M:ℕ→E→L[ℂ]F:= fun i => c (n i) • f (n i)
 have hm:CauchySeq M:=Metric.cauchySeq_iff.mpr fun ε r=>by
   let l:=ε/4; have ht:0<l:=by unfold l; positivity
   obtain ⟨N,L⟩:= eventually_atTop.1 (V₀.eventually ((slices l ht).and u))
   refine ⟨N,fun i p j s=>?_⟩
   rw [dist_eq_norm]; apply lt_of_le_of_lt _ (show l+l<ε by unfold l; linarith); apply opNorm_le_bound _ (by positivity)
   refine normUp ((M i-M j).toLinearMap) (l+l) (fun X' K=>P.above (by positivity) fun a'=>?_)
   have he(i:ℕ)(p:i≥N) : φ a' (M i X')=φ a' (A (n i) X')*ψ b (B (n i) y):=by
     unfold M; rw [smul_apply,map_smul,smul_eq_mul,mul_comm]; apply congrArg (fun z=> φ a' z * _); exact DFunLike.congr_fun (L i p).2.1 _ -- issue goal product equality
   change ‖φ a' ((M i-M j) X')‖ ≤ _; rw [sub_apply,map_sub,he i p,he j s]; exact (norm_sub_le_norm_sub_add_norm_sub _ (X a' b X' y) _).trans (add_le_add ((L i p).1 a' b X' y K q) (by rw [norm_sub_rev]; exact (L j s).1 a' b X' y K q))
 obtain ⟨M',m⟩:=cauchySeq_tendsto_of_complete hm
 refine ⟨n,k,d⁻¹ • M',( (z.inv₀ d').smul m).congr' ?_⟩
 filter_upwards [z.eventually (isOpen_ne.mem_nhds d')] with i h
 exact inv_smul_smul₀ h (f (n i))
end
end YM.CF.Pique
