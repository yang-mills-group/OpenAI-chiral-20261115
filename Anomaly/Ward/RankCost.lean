import YM.CF.Cascade.Seashore
import Anomaly.Weigh
/-!
Check the identity profile at these SPECIFIED Xs. Each site's internal trace
pays flat rank zero.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill
open Nacre Next.Free Exterior Precision Wilson Gauge
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 24000
variable {a:Type}[DecidableEq a][Fintype a]
open Laurent Rush Phase Bloch SU
variable {N: Side}
lemma cartSite (f:Cover→Op a)(x y:Site N)(i j:a): cart N f (x,i) (x,j)=cart N f (y,i) (y,j):=by
 apply tsum_congr (g:=fun z=>wagon N f z (y,i) (y,j))
 intro z; rw [wagon_app,wagon_app]; by_cases h:wrap N z=0
 · simp only [h, add_zero,ite_true]
   suffices g:wind x z=wind y z by rw [g]
   have ht(t:Site N):wind t z=mode (mel t) z:=by
      have he:=wave_advance (mode_fee t) t z; rw [h,add_zero] at he; exact mul_right_cancel₀ (Complex.exp_ne_zero _) (he.trans (mul_comm ..)) -- not constant; refine fixes k independent both
   have hh:= wave_advance (mode_fee x) y z; rw [h,add_zero] at hh; exact (ht x).trans (mul_right_cancel₀ (Complex.exp_ne_zero _) (hh.trans (mul_comm ..))).symm
 simp [h]
variable {j:ℕ}
lemma flat_same (p:1 ≤ j)(M: Tulip.Male)(x y:Site N) :
 let S:=funde j M N (profile 1)-tickA N
 siteRead x S=siteRead y S:=by
 intro S; unfold siteRead S; rw [profile_trivial,funde_flat _ p]; simp_rw [Matrix.sub_apply,Matrix.kroneckerMap_apply]
 apply sum_congr rfl; intro i _; apply sum_congr rfl; intro m _; rw [cartSite (y:=y)]; congr 1
 unfold tickA; rw [plane_diag]; simp [portW,helix,Lat.spin,jump_apply] -- tune
lemma site_rank (p:1≤j)(M:Tulip.Male)(x:Site N):(siteRead x (funde j M N (profile 1)-tickA N))=0:=by
 let S:= funde j M N (profile 1) - tickA N
 have h: Matrix.trace S=0:=by unfold S; rw [Matrix.trace_sub,sub_eq_zero]; exact Cascade.rank_z N p M
 unfold Matrix.trace at h; rw [Fintype.sum_prod_type,Fintype.sum_prod_type] at h
 have hx:∑ y:Site N,siteRead y S=0:=h
 have he(y:Site N):siteRead y S=siteRead x S:=flat_same p M y x
 simp_rw [he,sum_const,card_univ,nsmul_eq_mul,mul_eq_zero] at hx; exact hx.resolve_left (by exact_mod_cast Fintype.card_ne_zero)
lemma round_site (p:1≤j)(M:Tulip.Male)(x:Site N)(r:ℕ): Matrix.trace ((funde j M N (profile 1)-tickA N)* windmill x r)=0:=by rw [wind_read]; exact nothing _ x where
 nothing (l: List Axis)(x:Site N):squareSum (fun y=>siteRead y (funde j M N (profile 1)-tickA N)) r l x=0:=by
  induction l generalizing x with
  | nil=> exact site_rank p M x
  | cons i l ih=> unfold squareSum; exact Finset.sum_eq_zero fun y v=> ih _

open Py Py.Rate Py.Rate.LocalLimit Py.Rate.LocalLimit.Preparation
lemma unbilled {o:Seat N} {a b d:ℝ}{X:SOp N}(p:Soak o X a b d)(g:0≤a)(t:0<d): ‖Matrix.trace (X (profile 1))‖ ≤ b:=by
 refine (norm_sum_le ..).trans ((p.siteCost g (⟨profile 1,1,guard0 t.le,by simpa using t⟩)).trans' ?_); apply sum_le_sum; intro i _; exact single_le_sum (fun j _=> norm_nonneg (X (profile 1) i j)) (mem_univ i)
lemma identityPrice {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}{J:Course P F}{i k s m:ℕ}{a b c d:ℝ}{X Z R K}(h:CartPins J i k s m a b c d X Z R K)(p:0≤ a):
   ‖Matrix.trace (R (profile 1))‖ ≤ Real.exp (-a*(((RootBook J i k s).p.B/10:ℕ):ℝ))*b:=by
 let H:= h.ropes.tubes; have g:= H.readsX 1 (guard0 P.dpos.le); have v:= unbilled H.tailX p P.dpos
 rw [show Matrix.trace (K (profile 1))= -Matrix.trace (R (profile 1)) from ?_,norm_neg] at v -- orientation! v substitute RHS of draw; change
 exact v
 rw [eq_neg_iff_add_eq_zero,add_comm,←Matrix.trace_add,←g]; exact round_site (show 1 ≤ P.K.j by rw [P.kJ]; omega) .. -- tune order
end YM.CF.Swell.Sonar
