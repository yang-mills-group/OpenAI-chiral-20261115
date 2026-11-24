import YM.SU5.Registration.Postcards.Poster

/-!
 # Euclidean crossing (116) by finite averages escaping to infinity.
 
 Enough in this version to run many usual *Eu boost-plane* tests. No full-cone estimate
 used in the cluster pricing, in E or in M! (Need equality of unconditioned point-moment at the indicated
 tests as structural angular estimate.) Our method uses real-angle co-rotation even
 in the payments evaluating (116). Works with REAL displacements large even in every axis,
 need not supply time-ground projector equality to joint projection of unconditioned.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Passage
open Boundary Mink Analysis Function Set Filter OS.Semigroup
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
open CF.Buffered.Afterglow.Tower.VacuumSelection
open CF.Buffered.Afterglow.Hierarchy.Seld
open CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Carton
variable {H : Hilbert} (S : OS.Semigroup H timeAxis)
open ContinuousLinearMap MeasureTheory Small
variable {S} {V : Type*}[AddCommGroup V][Module ℂ V] (B:Carton S V){n m:ℕ}
-- use Postcards/ bridge with temporal fare subtracting before pricing
local notation "T" => TrainJ V
variable {X:Type*} [TopologicalSpace X][MeasurableSpace X][OpensMeasurableSpace X][CompactSpace X] (μ:Measure X)[IsFiniteMeasure μ]
variable {H₀:X→Hilbert}{S₀:∀ x,OS.Semigroup (H₀ x) timeAxis}
open Courts
set_option linter.unusedSectionVars false
variable [Measure.IsOpenPosMeasure μ]
variable (R:Courts V)(L:Ortho)(i:SpaceAxis)(t:ℝ)(F:X→InkWaves V)
noncomputable abbrev cruise (n:ℕ):ℝ:=2*Real.pi/(n:ℝ)
lemma cruise_period (n:ℕ)(h:0<n) : plane i (cruise n)^n=1:=by
 have hg(t:ℝ)(n:ℕ): plane i t^n=plane i ((n:ℝ)*t):=by
    induction n with
    | zero=> simp [plane,oneParameter_zero]
    | succ n ih=> rw [pow_succ,ih]; simp [add_mul,plane, parameter_add]
 have hn:0<(n:ℝ):=Nat.cast_pos.mpr h
 apply Ortho.ext; intro x; rw [hg,show (n:ℝ)*cruise n=2*Real.pi from (by unfold cruise; field_simp),Ortho.move_one]; obtain ⟨h,v,t⟩:= Work.A13.plane_givens (show timeAxis≠i.castSucc from (Fin.castSucc_ne_last i).symm) x (2*Real.pi)
 apply PiLp.ext; intro j; by_cases e:j=timeAxis; · subst j; rw [h,Real.cos_two_pi,Real.sin_two_pi,one_mul,zero_mul,add_zero]
 by_cases y:j=i.castSucc; · subst j; rw [v,Real.cos_two_pi,Real.sin_two_pi,one_mul,zero_mul,sub_zero]
 exact t j e y
-- period implies selfadjoint era rotated by TWO (without requiring any ST covariance estimate in directions other than time3).
-- arithmetic lemma $R_n$ circulant
private lemma group_ear (Z:ℕ→ℝ) (n:ℕ)(z:Z n=Z 0):∑ i∈ Finset.range n,Z (i+1)=∑ i∈ Finset.range n,Z i:=by
 let t:=Finset.sum_range_succ' Z n; rw [Finset.sum_range_succ Z n,z] at t; exact add_right_cancel t.symm
open RCLike
private lemma fits_out (c d:ℂ): ‖c-d‖^2=(star c*c).re+(star d*d).re-2*(star c*d).re:=by
 simp [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re]; ring
-- integrate financial tropical from Album hypothesis.
private lemma integral_dup {f g:X→ℂ} (r:Continuous f)(s:Continuous g):
 (∫ x, ‖f x-g x‖^2 ∂μ) = (∫ x, star (f x)*f x ∂μ).re + (∫ x, star (g x)*g x ∂μ).re -2*(∫ x, star (f x)*g x ∂μ).re :=by
 let A (f g:X→ℂ):= fun x=> star (f x)*g x
 have h(f g:X→ℂ)(r:Continuous f)(s:Continuous g):Integrable (A f g) μ:= (r.star.mul s).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hG(f g:X→ℂ)(r:Integrable (A f g) μ): Integrable (fun x=> (star (f x)*g x).re) μ:=r.re
 let p:= h f f r r; let q:=h g g s s; let t:=h f g r s;
 have hR(f g:X→ℂ)(r:Integrable (A f g) μ): (∫ x, (star (f x)*g x).re ∂μ) = (∫ x, star (f x)*g x ∂μ).re:= integral_re r
 simp_rw [fits_out]; rw [integral_sub (show Integrable (fun x=>(star (f x)*f x).re+(star (g x)*g x).re) μ from (hG f f p).add (hG g g q)) ((hG f g t).const_mul 2), integral_add (hG f f p) (hG g g q), integral_const_mul,hR f f p,hR g g q,hR f g t]
-- use only with orbit finite.ORDER positivity via amplitude
variable {F} {J:JMap V} {U:∀ x,Carton (S₀ x) V}
lemma Album.finite_orbit (p:Album μ F U J) (r:ℝ)(N:ℕ) (e:0<N) (θ:∀ j:sizedStep,ampleStep (Ortho.move (plane i r) (compass j))) (z:Gratuity R J (plane i r))(t:SpinsAt μ R (plane i r) F)(a:List (TrainJ V))(g:∀ k:ℕ,Auction (advert R (plane i r^k) a))(f:plane i r^N=1)(x:X):
 Figures (F x) (advert R (plane i r^2) a)=Figures (F x) a:=by
 let L:= plane i r; let b:= advert R L; let T'(n:ℕ):=advert R (L^n) a; let C (k):= fun x=> Figures (F x) (T' k)
 have hc(k:ℕ): Continuous (C k):= p.ticket _ (g k);
 let d(k:ℕ):= (inkCross μ F (T' k) (T' k)).re; have hb:T' 0=a:=by simp [T']
 have hL(k:ℕ): T' (k+1)=b (T' k):=by unfold b T'; rw [pow_succ',project_ag R L (proper_param ..) (element_year L (proper_param ..) k)];
 have hG(k:ℕ): Auction (b (T' k)):= (hL k) ▸ g _
 let v(n):=∫ x, ‖C n x - C (n+2) x‖^2 ∂μ; have hv(n:ℕ):v n=d n + d (n+2) -2*d (n+1):=by
    unfold v; rw [integral_dup μ (hc n) (hc (n+2))];
    suffices h: inkCross μ F (T' n) (T' (n+2))= inkCross μ F (T' (n+1)) (T' (n+1)) from (by change _= _; dsimp only [d]; rw [← h]; rfl)
    rw [ show n+2=n+1+1 from rfl,hL (n+1)]; nth_rw 2 [hL n]; exact (across_theta μ R (T' n) (T' (n+1)) p _ _ θ z t (g _) (g _) (hG _) (hG _)).symm
 have ht:T' N=a:=by unfold T'; rw [f,advert_none]
 let he1:= group_ear d N (show d N=d 0 from by unfold d; rw [ht,hb]); have ha:= group_ear (fun k=>d (k+1)) N (show d (N+1)=d (0+1) from by unfold d; rw [hL,hL,ht,hb])
 have hn: ∑ i∈ Finset.range N, v i=0:=by simp_rw[hv]; rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum, show (∑ i∈ Finset.range N,d (i+2))=(∑ i∈ Finset.range N,d (i+1)) from ha,he1]; ring
 let Lk:= fun x=> ‖C 0 x - C 2 x‖^2; have pK:∀ x:X, 0≤ Lk x:=fun _=>sq_nonneg _; have hb:C 0 x= Figures (F x) a:=congrArg (Figures (F x)) hb
 have hh(n:ℕ):0≤v n:= integral_nonneg (fun _=>sq_nonneg _)
 have hp: ∫ x,Lk x ∂μ=0:= (le_trans (Finset.single_le_sum (f:=v) (fun i _=> hh i) (Finset.mem_range.mpr e)) hn.le).antisymm (hh 0)
 have hy: Continuous Lk:=( (hc 0|>.sub (hc 2)).norm).pow _; have hU: Lk=0:= (hy.ae_eq_iff_eq μ continuous_zero).mp ((integral_eq_zero_iff_of_nonneg pK (hy.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 hp)
 have hz: ‖C 0 x- C 2 x‖^2=0:=congrFun hU x; exact (sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith only [hz]))).symm.trans hb
end YM.SatinWFixed.Passage
open YM.SatinWFixed.Passage
#print axioms Album.finite_orbit
#print axioms cruise_period
