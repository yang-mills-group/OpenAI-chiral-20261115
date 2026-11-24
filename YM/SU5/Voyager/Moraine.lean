import YM.SU5.Voyager.Storm
set_option autoImplicit false
noncomputable section
namespace YM.Spectral.Orbit.Prairie
open Function Filter Set Metric Bornology Finset Complex MeasureTheory Measure
open Boundary Boundary.Probe Caino
open scoped NNReal ENNReal Topology InnerProductSpace ComplexConjugate ComplexOrder BigOperators Classical
variable {K:Type*}[Fintype K][DecidableEq K]
local notation "X"=> Terrain K
variable {H: Hilbert} (T: Orbit H (Terrain K)) (P: PVM H (Terrain K))
variable (b:K→Bool)
-- σ true = forward component
def alley : Set X:= {p|∀ k:K, if b k then 0<p k else p k<0}
local notation "U"=> alley b
lemma alley_open : IsOpen U:=by
 rw [show U= ⋂ i:K, {p:X| if b i then 0<p i else p i<0} from Set.ext fun x=> (by rw [mem_iInter]; rfl)]; apply isOpen_iInter_of_finite; intro i
 cases h:b i with
 | true => simp only [if_true]; exact isOpen_lt continuous_const (by fun_prop)
 | false => simp only [Bool.false_eq_true,↓reduceIte]; exact isOpen_lt (by fun_prop) continuous_const
lemma lanes(p q:ℝ)(t u:ℝ)(h:0<p)(g:0<q)(e:0 ≤ t)(v:0 ≤ u)(y:t+u=1): 0<t*p+u*q:=by rcases eq_or_lt_of_le e with z | z; simp only [← z, zero_mul,zero_add] at y ⊢; simp [y,g]; exact add_pos_of_pos_of_nonneg (mul_pos z h) (mul_nonneg v g.le)
lemma alley_conv : Convex ℝ U:= by
 intro x hx y hy a c hx' hy' z i; have ht:=hx i; have hp:=hy i; simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]; cases h:b i with
 | true=> simp_rw [h,if_true] at *; exact lanes _ _ _ _ ht hp hx' hy' z -- tune
 | false => simp only [h,Bool.false_eq_true, ↓reduceIte] at hp ht ⊢; nlinarith [lanes _ _ a c (neg_pos.mpr ht) (neg_pos.mpr hp) hx' hy' z]
local notation "S"=> (Finset.univ:Finset K)
variable {R g:ℝ}
lemma pointSafe (q:Real.pi>g*R)(w:0<g)(x:X)(u:x∈U)(p': x∈ ball 0 R):0 < lamps g S x:=by
 unfold lamps; rw [Finset.prod_apply]; apply Finset.prod_pos; intro i t; unfold mallet; apply pow_pos; apply norm_pos_iff.mpr; rw [sub_ne_zero]; by_contra! z; unfold plane at z; let a:ℂ:=↑(inner ℝ x (sight g i))*I
 have he : a.im=g*x i:=by simp [a,sight,EuclideanSpace.inner_single_right] -- u membership
 have hg:x i≠0:=by have ht:=u i; by_cases l:b i=true; exact (show 0<x i from (by simpa [l] using ht)).ne'; exact (show x i < 0 from (by simpa [l] using ht)).ne
 have ht: |g*x i| < Real.pi:=calc
      _ ≤ g*‖x‖ := by rw [abs_mul,abs_of_pos w]; exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i) w.le
      _ < _:= lt_trans (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp p') w) q
 have hh : a=0:= exp_inj_of_neg_pi_lt_of_le_pi (he.symm ▸ (abs_lt.mp ht).1) (he.symm ▸ (abs_lt.mp ht).2.le) (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]) (z.trans Complex.exp_zero.symm)
 exact (mul_ne_zero w.ne' hg) (he.symm.trans (congrArg Complex.im hh))
variable (x:H)(p:T.Spectrum P)(G:∀ g:ℝ,0<g→∃ e y:ℝ,Quilt T x g e y)
include p G

variable [Nonempty K]
lemma everyShelf(q:0<R) : ∃ g:ℝ,0<g∧ Furnished (P.diagonal x) (lamps g (Finset.univ:Finset K))∧ ∀ z∈ alley b∩ball 0 R,0<lamps g (Finset.univ:Finset K) z:=by
 let g:= Real.pi/(2*R); have ht:0<g:=by positivity
 obtain ⟨w,q,y⟩:= G g ht; have hu:Real.pi>g*R:=by unfold g; rw [div_mul_eq_mul_div]; apply (div_lt_iff₀ (by positivity)).2; nlinarith [Real.pi_pos]
 exact ⟨g,ht,minted T P g x p ht y,fun x h=>pointSafe b hu ht x h.1 h.2⟩
omit p G
lemma allLanes {α:Type*}[MeasurableSpace α]{μ ν:Measure α} (V:ℕ→Set α)(u:∀ i:ℕ, μ.restrict (V i) ≪ ν) : μ.restrict (⋃ i:ℕ,V i)≪ν:=
 AbsolutelyContinuous.mk (fun s hs z=>by rw [restrict_apply hs, Set.inter_iUnion]; exact measure_iUnion_null (fun i=> (restrict_apply (μ:=μ) (s:=V i) hs).symm.trans (u i z))) -- tune cod

lemma alley_un : U=⋃ i:ℕ,U∩ball (0:X) (i+1):=by
 apply Set.Subset.antisymm; · intro x h; obtain ⟨n,ht⟩:= exists_nat_gt ‖x‖; exact Set.mem_iUnion.mpr ⟨n,h,mem_ball_zero_iff.mpr (by linarith)⟩
 apply Set.iUnion_subset; intro i; exact Set.inter_subset_left
local notation "Ξ"=> P.diagonal x
include p G
lemma occupation : (Ξ).restrict U ≪ volume.restrict U:=by
 let f(i:ℕ):= U∩ball (0:X) (i+1); refine (restrict_restrict_of_subset (Set.Subset.refl U)).symm ▸ (show (((Ξ).restrict U).restrict U) ≪ volume.restrict U from AbsolutelyContinuous.restrict ?_ U)
 show (Ξ).restrict U ≪ volume; rw [alley_un]; apply allLanes; intro i; obtain ⟨g,v,H',B⟩:= everyShelf T P b x p G (by positivity: (0:ℝ)<(i:ℝ)+1); exact H'.allRoom _ B ((alley_open b).inter isOpen_ball) -- names args
lemma growth (g₀: (Ξ) U≠0) : volume.restrict U ≪ (Ξ).restrict U:=by
 let f(i:ℕ):= U∩ball (0:X) (i+1); have he:U=⋃ i:ℕ,f i:= alley_un b -- tune includes vars
 have hi:∃ i:ℕ,Ξ (f i) ≠0:= of_not_not (fun t=>g₀ (by rw [he]; exact measure_iUnion_null (fun i=> of_not_not fun w=> t ⟨i,w⟩)))
 obtain ⟨k,q⟩:= hi; have ht: Monotone f:= fun i j h=> inter_subset_inter_right _ (ball_subset_ball (by exact_mod_cast Nat.add_le_add_right h 1: (i:ℝ)+1 ≤ (j:ℝ)+1 ))
 nth_rw 1 [he]; apply allLanes; intro i; let n:=max i k; have hx:f i ⊆ f n:= ht (le_max_left ..); have hy:f k⊆ f n:=ht (le_max_right ..); have hz: Ξ (f n) ≠ 0:= fun h=>q (measure_mono_null hy h)
 obtain ⟨a,b',H',B⟩:= everyShelf T P b x p G (by positivity: (0:ℝ)<(n:ℝ)+1)
 exact ((restrict_mono_set (μ:=volume) hx).absolutelyContinuous.trans (H'.blooming _ B ((alley_open b).inter isOpen_ball) ((alley_conv b).inter (convex_ball ..)) hz)).trans (restrict_mono_set (μ:=Ξ) (Set.inter_subset_left)).absolutelyContinuous -- Ξ notation binder!
end YM.Spectral.Orbit.Prairie
#print axioms YM.Spectral.Orbit.Prairie.growth
#print axioms YM.Spectral.Orbit.Prairie.occupation
