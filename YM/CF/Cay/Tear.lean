import YM.CF.Cay.Solo
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
open Matrix
open AnalyticBridge.RelativeLogdet.Ink
-- FTC Clock with exact power from b; ContDiff finite
section arc
variable {C M L:ℝ} {p:E}
def tear {E F : Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F](k:ℕ)(f:E→F)(x a:E) : F:= match k with
 | 0=> f x
 | j+1=> tear j (fderiv ℝ f) x a a
lemma turn_d {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] (k:ℕ)(f:E→F)(x a:E)(p:ℝ)(h:ContDiffAt ℝ ((k+1:ℕ):ℕ∞ω) f (x+p•a)): HasDerivAt (fun y:ℝ=> tear k f (x+y•a) a) (tear (k+1) f (x+p•a) a) p:=by
 induction k generalizing F with
 | zero=>
    have hh:HasDerivAt (fun y:ℝ=>x+y•a) a p:=by simpa using (((hasDerivAt_id' p).smul_const a).const_add x)
    exact (h.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p hh
 | succ k ih=>
    have ht:ContDiffAt ℝ ((k+1:ℕ):ℕ∞ω) (fderiv ℝ f) (x+p • a):= h.fderiv_right (by norm_cast)
    exact (ContinuousLinearMap.apply ℝ F a).hasFDerivAt.comp_hasDerivAt p (ih (fderiv ℝ f) ht)
lemma tear_p {E F B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup B][NormedSpace ℝ B](k n:ℕ)(f:E→F)(p:B)(x a:B→E)(hp:Allows n x p M)(ha:Allows n a p L)(h:Allows (n+k) f (x p) C): Allows n (fun i=> tear k f (x i) (a i)) p ((2^n*L)^k*(composeCost n C M)):=by
 induction k generalizing F with
 | zero=> simpa only [tear,Nat.add_zero,pow_zero,one_mul] using h.comp hp -- tune
 | succ k ih=>
    have ht:= Newt.appliance (ih (fderiv ℝ f) h.slide) ha; simp_rw [show ∀ i, tear (k+1) f (x i) (a i)=tear k (fderiv ℝ f) (x i) (a i) (a i) from fun i=>rfl]; exact ht.mono (le_of_eq (by ring))
lemma tear_C {E F B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup B][NormedSpace ℝ B](k n:ℕ)(f:E→F)(p:B)(x a:B→E)(hx:ContDiffAt ℝ (n:ℕ∞ω) x p)(ha: ContDiffAt ℝ (n:ℕ∞ω) a p)(h:ContDiffAt ℝ ((n+k:ℕ):ℕ∞ω) f (x p)): ContDiffAt ℝ (n:ℕ∞ω) (fun i=> tear k f (x i) (a i)) p:=by
 induction k generalizing F with
 | zero=> exact h.comp _ hx
 | succ k ih=> exact (ih (fderiv ℝ f) (h.fderiv_right (by norm_cast))).clm_apply ha
variable (f:A→ℝ)(n k:ℕ)(x a:E→A)
abbrev tale (j:ℕ)(t:ℝ)(p:E):=tear j f (x p+t•a p) (a p)
def grade (k:ℕ)(t:ℝ):ℝ:= (1-t)^k/(k.factorial:ℝ)
lemma note_g(k:ℕ)(t:ℝ): HasDerivAt (grade (k+1)) (-grade k t) t:=by
 have hv:HasDerivAt (fun u:ℝ=>1-u) (-1) t:=by simpa using (hasDerivAt_id' t).const_sub 1
 have hp:=(hv.pow (k+1)).div_const ((k+1).factorial:ℝ)
 refine (show _ = -(grade k t) from ?_) ▸ hp; unfold grade; rw [Nat.factorial_succ,Nat.cast_mul]; dsimp only [Nat.add_one_sub_one]; field_simp -- tune
lemma lateC(k:ℕ)(t:ℝ)(y:E) (h : ContDiffAt ℝ ((k+1:ℕ):ℕ∞ω) f (x y+t• a y)): HasDerivAt (fun t=>∑ i∈range (k+1),grade i t*tale f x a i t y) (grade k t*tale f x a (k+1) t y) t:=by
 induction k with
 | zero=> simp only [Nat.zero_add,sum_range_one]; simp [grade]; exact turn_d 0 f (x y) (a y) t h
 | succ k ih=>
    simp_rw [sum_range_succ _ (k+1)]
    have ht:= ih (h.of_le (by exact_mod_cast Nat.le_succ _)); let Y(u:ℝ):=grade (k+1) u*tale f x a (k+1) u y; have hv:HasDerivAt Y _ t:= (note_g k t).mul (turn_d (k+1) f (x y) (a y) t h)
    refine (show _=grade (k+1) t * tale f x a (k+1+1) t y from ?_) ▸ ht.add hv; unfold tale; ring -- tune
variable [FiniteDimensional ℝ E] (p:E)
lemma tale_p(C D L:ℝ)(ht:∀ᶠ y in 𝓝 p, ContDiffAt ℝ (n:ℕ∞ω) (x) y∧ Allows n a y L ∧ ∀ u ∈ interval, Allows n (fun y=>x y+u•a y) y D ∧ Allows (n+(k+1)) f (x y+u • a y) C):
 Allows n (fun y=>(∑ i∈range (k+1),grade i 1*tale f x a i 1 y)-(∑ i∈range (k+1),grade i 0*tale f x a i 0 y)) p ((2^n*L)^(k+1)*composeCost n C D):=by
 let W:= (fun i:E×ℝ=> x i.1+i.2 • a i.1); let P:=fun i:E×ℝ=> grade k i.2*tale f x a (k+1) i.2 i.1; let Z(y:E) := ContDiffAt ℝ (n:ℕ∞ω) (x) y∧ Allows n a y L ∧ ∀ u ∈ interval, Allows n (fun y=>x y+u•a y) y D ∧ Allows (n+(k+1)) f (x y+u • a y) C
 have H y (hy: Z y): Arc P n y :=by
    intro t hp; let g:=grade k; have he:ContDiff ℝ (n:ℕ∞ω) g:=by unfold g grade; fun_prop
    have hu := hy.2.1.smooth.comp (y,t) (f:=Prod.fst) contDiffAt_fst
    have hh:ContDiffAt ℝ (n:ℕ∞ω) W (y,t):= ((hy.1.comp _ contDiffAt_fst).add (contDiffAt_snd.smul hu))
    exact (he.contDiffAt.comp (f:=Prod.snd) _ contDiffAt_snd).mul (tear_C (k+1) n f (y,t) W (a ∘ Prod.fst) hh hu (hy.2.2 _ hp).2.smooth)
 have hl:=ht.self_of_nhds; apply (spirit (H p hl) ?_).germ
 · filter_upwards [ht] with y hy
   rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun t=>∑ i∈range (k+1),grade i t*tale f x a i t y) ?_ ((H _ hy).slice.intervalIntegrable_of_Icc zero_le_one)]; intro u hu; exact lateC f x a k _ y ((hy.2.2 _ (by simpa only [Set.uIcc_of_le zero_le_one] using hu)).2.smooth.of_le (by exact_mod_cast (Nat.le_add_left (k+1) n))) -- tune
 intro t h; have hh:=tear_p (k+1) n f p (fun y=>x y+t • a y) a (hl.2.2 t h).1 hl.2.1 (hl.2.2 t h).2; refine (hh.smul (grade k t)).mono ((mul_le_of_le_one_left hh.nonneg ?_)); have hp:0 ≤ 1-t:= sub_nonneg.mpr h.2; rw [abs_of_nonneg (show 0 ≤ grade k t by unfold grade; positivity)]; unfold grade; exact div_le_one_of_le₀ ((pow_le_one₀ hp (sub_le_self _ h.1)).trans (Nat.one_le_cast.mpr (Nat.factorial_pos _))) (by positivity) -- tune
end arc
end YM.CF.Cay
