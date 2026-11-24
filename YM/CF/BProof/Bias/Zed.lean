import YM.CF.BProof.Bias.Ell
import YM.CF.BProof.Bias.Wing
import YM.CF.BProof.Bias.Recur
import YM.CF.Laic.Inlets
/-! Prepare Z-Lift aperture and local tail with actual input prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}(M:Male)(h:1≤j)
abbrev Zenith(j:ℕ)(M:Male)(N:Side): Op (Single N):= relic (zag j M)
lemma zen_y : Zenith j M N * tickA N= Zenith j M N := by
 have hp:tickA N= relic (fun _=>sky):=by rw [← ticka,←lift_spin (N:=N) (u:=true),←paint_pill]; simp only [pill_plus]
 rw [hp,relic_mul]; exact congrArg _ (funext (fun i=>zag_yes j M i)) -- tune
lemma sky_t : tickA N=relic (fun _=>sky):=by rw [← ticka,←lift_spin (N:=N) (u:=true),←paint_pill]; simp only [pill_plus]
lemma zen_n : tickA N*Zenith j M N=0:=by rw [sky_t,relic_mul,←relic_zero]; apply congrArg; funext i; exact zag_off ..
abbrev redP (j:ℕ)(M:Male)(N:Side):=spar j M (1:Streak N)
include h
lemma redP_eq : redP j M N=relic (red j M):= (paint_real j h M).symm
lemma zen_frame : Zenith j M N * redP j M N=(1-tickA N)*redP j M N:=by
 rw [sky_t,redP_eq M h,relic_mul,←relic_one,relic_sub,relic_mul]; apply congrArg; funext i; exact zag_at j M h i
lemma zen_find : redP j M N*(tickA N+Zenith j M N) = tickA N+Zenith j M N:=by
 rw [sky_t,redP_eq M h,relic_add,relic_mul]; apply congrArg; funext i; exact zag_ready j M h i
omit h
lemma temporal_near {D:Type}[TopologicalSpace D](b:Feet N D)(x:D){A: Raw D (Single N)}{t v:Tag b.st}{p: Stint.Pay}(h:Earn p t v A)(i:ℕ): Near ht i (tailPay p i) (A x):=by
 obtain ⟨Q,X,W,L,U⟩:= h.holds; let B:=lop Q i x; have hu:= tailEarn W L U i x; refine ⟨B,?_ ,hu⟩; intro r s g; apply lop_rad Q X W x r s; rw [b.index,b.town]; change i<separation (node r.1.1) (node s.1.1); have he: delta1 N (ht r) (ht s) ≤ separation r.1.1 s.1.1:=component_le (r.1.1-s.1.1) 0; rw [show separation _ _=2*separation r.1.1 s.1.1 from (by unfold node; rw [separation_translate]; exact Laic.emptio (assembly N) _ _ : separation (node r.1.1) (node s.1.1)=_)]; omega
-- expenditure tracking for constant times
lemma Near.absorb {I:Type}[Fintype I][DecidableEq I]{F:I→Per N}{p:ℝ}{r:ℕ}{A B:Op I}(h: Near F r p A)(g: Span F 0 B)(u:‖B‖≤1): Near F r p (A*B):=by obtain ⟨W,w,h⟩:=h; refine ⟨W*B,(add_zero _ : r+0=r) ▸ span_mul w g,?_⟩; rw [← sub_mul]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) u).trans h)
lemma Near.push {I:Type}[Fintype I][DecidableEq I]{F:I→Per N}{p:ℝ}{r:ℕ}{A B:Op I}(h: Near F r p B)(g: Span F 0 A)(u:‖A‖≤1): Near F r p (A*B):=by obtain ⟨W,w,h⟩:=h; refine ⟨A*W,(zero_add _ : 0+r=r) ▸ span_mul g w,?_⟩; rw [← mul_sub]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) u).trans h)
lemma Near.off {I:Type}[Fintype I][DecidableEq I]{F:I→Per N}{p:ℝ}{r:ℕ}{A B:Op I}(h: Near F r p B)(g: Span F r A): Near F r p (A-B):=by obtain ⟨W,w,h⟩:=h; refine ⟨A-W,subP g w,?_⟩; rw [show A-B-(A-W)= -(B-W) by abel,norm_neg]; exact h
variable (w:Per N){p:Stint.Pay}{b v:ℝ}
abbrev haloW (w:Per N):=wing 1 w
abbrev AngleZ (j:ℕ)(M:Male)(w:Per N) := Zenith j M N * haloW w
include h
lemma bills (bp:0≤b)(vp:0≤v)(x:∀ i∈Label 1 w, 1-b≤hat j M i ∧ (hat j M i)⁻¹-1 ≤ v^2) (H:∀ i:ℕ, Near ht i (tailPay p i) (redP j M N)): Tango ht b v p (AngleZ j M w):=by
 let A:=redP j M N; let S:=haloW w; let Z:= Zenith j M N; let T:=tickA N; let K:=T-T*A*T; let Y:=(1-T)*A*T; constructor; refine ⟨Y*S,K*S,?_,?_,?_,?_⟩; rotate_left 1
 · have hf:K*S=relic (fun i=> if i∈Label 1 w then (1-hat j M i) • sky else 0):=by
      unfold K T A S haloW wing modality; rw [sky_t,redP_eq M h,relic_mul,relic_mul,relic_sub,relic_mul]; apply congrArg; funext i; by_cases t:i∈ Label 1 w; rw [if_pos t]; simp only [Pi.mul_apply,Pi.sub_apply,red_y,thinK,t,ite_true,mul_one,sub_smul,one_smul]; simp [thinK,t]
   rw [hf]; apply relic_up bp; intro i; split; rename_i t; rw [norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr (hat_e ..)),sprojNorm sky_h sky_pos,mul_one]; linarith [(x i t).1]; simpa
 · change ‖Z*S‖ ≤ v; unfold S haloW wing modality; rw [relic_mul]; apply relic_up vp; intro i; by_cases t:i∈ Label 1 w; simp only [Pi.mul_apply,thinK,t,ite_true,mul_one]; exact (sq_le_sq₀ (norm_nonneg _) vp).mp ((zag_norm j M h i).trans_le (x i t).2); simpa [thinK,t]
 · have hP:IsStarProjection T:=by unfold T; rw [←ticka]; exact cutM_idp _
   have hu: Span ht 0 T:=by unfold T; rw [←ticka]; exact span_cut ht _
   have htT: ‖T‖≤1:=hP.norm_le _; have hx: ‖S‖≤1:=(mode_p (Label 1 w)).norm_le _; have hl: Span Bias.ht 0 S:= wing_t 1 w (by decide)
   intro i; let hU: Near Bias.ht i (tailPay p i) (A*T):=(H i).absorb hu htT; unfold Y K; rw [mul_assoc (1-T) A,mul_assoc T A]; exact ⟨(hU.push (subP (span_one _) hu) (hP.one_sub.norm_le _)).absorb hl hx, ((hU.push hu htT).off (hu.up (by omega))).absorb hl hx⟩
 -- recurrence
 have hu:Z=Y+Z*K:= by
     unfold Z Zenith Y K T A; rw [sky_t,← relic_one,redP_eq M h,relic_sub,relic_mul,relic_mul,relic_mul,relic_mul,relic_sub,relic_mul,relic_add]; apply congrArg; funext i; exact zag_recur j M h i
 have hl:Commute S K:=by unfold K T A; rw [sky_t,redP_eq M h,relic_mul,relic_mul,relic_sub]; exact mode_comm _ _
 change Z*S= _; rw [←mul_assoc (Z*S) K,S |> (fun _=> mul_assoc Z S K),hl.eq,←mul_assoc Z K S,mul_assoc (Z*K), (mode_p ..).1.eq,← add_mul, ← hu] -- tune
end YM.CF.BProof.Bias
