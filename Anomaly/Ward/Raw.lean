import Anomaly.Ward.Warp
import Anomaly.PitchMark
/-!
The payload. Keep X, the actual truncated probe. No limit or replacement by a projected
quote from a different Shop.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill
open Nacre Next.Rank.Spindle LampP Exterior Precision Wilson
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 24000
private lemma fundLoan {a:ℝ}{m:ℕ}(f:0<a):∃ L:ℝ,0<L∧∀ i:ℕ,(i+1:ℝ)^m ≤ L * Real.exp (a*i):=by
 let u:=a/(m+1:ℝ); have he:0<u:=div_pos f (by positivity)
 let B:=max 1 u⁻¹; have hz:1≤B:=le_max_left ..; have hu:1/B≤u:=by rw [div_le_iff₀ (zero_lt_one.trans_le hz)]; exact (Eq.le (mul_inv_cancel₀ he.ne').symm).trans (mul_le_mul_of_nonneg_left (le_max_right ..) he.le)
 refine ⟨B^m,pow_pos (zero_lt_one.trans_le hz) _,fun i=>?_⟩; have h:i+1≤ B*Real.exp (u*i):=by
    rw [← div_le_iff₀' (zero_lt_one.trans_le hz),add_div,show (i:ℝ)/B=(1/B)*i by ring]; refine (add_le_add (mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg _)) ((div_le_one (zero_lt_one.trans_le hz)).mpr hz)).trans (Real.add_one_le_exp _)
 refine (pow_le_pow_left₀ (by positivity) h _).trans ?_; rw [mul_pow,←Real.exp_nat_mul]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply Real.exp_monotone; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
 exact (mul_le_mul_of_nonneg_right (by linarith : (m:ℝ) ≤ m+1) he.le).trans_eq (by unfold u; field_simp)
lemma diceRate {a C:ℝ}(p:0<a)(v:0<C): ∃ D:ℝ,0<D∧∀ b:ℕ,∀ x:ℝ,0 ≤ x → expDice b C x ≤ D*Real.exp (a*b)*x:=by
 let c:= ((3:ℝ)^4* Fintype.card PlaqAxes * Fintype.card SU.group.ColorIndex)^2 * (2*C * 4^2)
 obtain ⟨L,f,T⟩:= fundLoan (m:=10) p
 let P:=max 1 (c*L); refine ⟨P,zero_lt_one.trans_le (le_max_left ..),fun b x pp=>?_⟩
 have h_1: 0≤c:=by unfold c; positivity
 let y:ℝ:=b; have hy:0≤y:=Nat.cast_nonneg _; let z:= y+1
 calc
   expDice b C x ≤ ((3*z)^4* Fintype.card PlaqAxes* Fintype.card SU.group.ColorIndex)^2 *(2*C*x*(4*z)^2):=by unfold expDice z y; push_cast; gcongr <;> first| positivity | linarith
   _ = c * z^10*x:=by unfold c; ring
   _ ≤ P*Real.exp (a*(b:ℝ))*x:=by refine mul_le_mul_of_nonneg_right ?_ pp; apply le_trans (mul_le_mul_of_nonneg_left (T b) h_1); rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_pos _).le

variable {b k:ℕ}{n:Side}{m:ℕ}{a d α C M D q:ℝ} (p:0<d) {o:Seat n}{X:SOp n} (h:Trunk o X b a M d)(K:mintQ α C d m)
local notation "Πp" => tangD n
local notation "Y" => fieldDir SU.group (More n) 1

def rawQ (X:SOp n)(U:Pane n) := Matrix.trace (X (profile U))
def stepQ (X:SOp n)(x:tangD n):= rawQ X (increment 1 x)-rawQ X 1
structure Knit (X:SOp n) (o:Seat n) (l:ℕ) (d κ x φ w :ℝ) (r:ℕ) (Y0:tableQ SU.group (More n) ℂ):Prop where
  circle: ∀ z:tangD n, ‖z‖<κ → Allows r (stepQ X) z (2*φ*x)
  poses: ∀ i:Y, tariff Y0 (receipt i)=trim 2 (stepQ X) (collect SU.group i)
  roles: fderiv ℝ (stepQ X) 0=0
  card : costs Y0 ≤ w
  inHall: Regional o l Y0
  engage: ∀ (i: fenceP n d) (f: Seat n→ SU.group.El), rawQ X (gauge f i.val) = rawQ X i.val
  landsQ: ∀ (i j:fenceP n d), Agrees (halo l {o}) i.val j.val→ rawQ X i.val=rawQ X j.val

variable (w:0<a)(y: ∀ b:ℕ,∀ x:ℝ,0 ≤ x → expDice b C x ≤ D*Real.exp (a*b)*x)
lemma step_idle (X:SOp n):stepQ X 0=0:=by unfold stepQ; rw [show increment 1 (0:Πp)=(1:Pane n) from (by funext i; simp [increment]),sub_self]
private lemma tariffSum {I:Type*}[Fintype I]{n:Side}(F:I→tableQ SU.group n ℂ)(x:columnQ SU.group n) : tariff (∑ i,F i) x=∑ i,tariff (F i) x:=by unfold tariff; simp_rw [Finset.sum_apply,Finset.smul_sum]; rw [sum_comm]
include p h K w y
lemma coverQ (q: 2 ≤ m) (g:0<D) (t: 2*(b+1)<(More n).val) : ∃ P:tableQ SU.group (More n) ℂ, Knit X o b d α M C (D*M) m P:=by
 obtain ⟨F,U,v,k,u,e⟩:= h.home
 have hR(i:fenceP n d): rawQ X i.val=∑ S:Sa n,soloQ p (F S) i.val:=by unfold rawQ; rw [show X (profile i.val)=_ from e ⟨_,insideQ i p⟩, Matrix.trace_sum]; exact sum_congr rfl fun S _=> by unfold soloQ lens; rw [dif_pos (show Guard _ _ from i.property)]
 let z:fenceP n d:= ⟨1,guard0 p.le⟩
 have hu:∀ τ:Πp, ‖τ‖<α→ stepQ X τ=∑ S: Sa n, fluxJet p (F S) τ:=by
    intro x q; unfold stepQ; rw [show rawQ X (increment 1 x)=_ from hR ⟨_,K.2.2.2.1 x q⟩, show rawQ X 1=_ from hR z,←sum_sub_distrib]
 have Hx:∀ x:Πp, ‖x‖<α → stepQ X =ᶠ[𝓝 x] (∑ i:Sa n, fluxJet p (F i)):=by intro x ht; filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht)] with y hy; rw [Finset.sum_apply]; exact hu _ (mem_ball_zero_iff.mp hy)
 have hW:=Hx 0 (norm_zero.trans_lt K.1); let L(S:Sa n):= ledgerV (U S); have hv(S:Sa n):0≤L S:= sum_nonneg (fun i _=> sum_nonneg (fun j _=> (v S).nonn i j)); have hi: ∑ S,L S≤ M:=by apply le_trans _ u; exact sum_le_sum fun S _=> le_mul_of_one_le_left (hv _) (rent_one w.le _)
 have ht₀(i:Sa n): U i=0 → ∀ (x:fenceP n d),soloQ p (F i) x.val=0:=by
    intro q x; have he: lens p (F i) x.val=0:=by rw [lens,dif_pos (show Guard _ _ from x.property)]; ext i' j; exact norm_le_zero_iff.mp (((v i).expo i' j).bounded _ |>.trans_eq (by rw [q]; rfl))
    unfold soloQ; rw [he, Matrix.trace_zero]
 have HF(S:Sa n):∃ T:tableQ SU.group (More n) ℂ, costs T ≤ D*(rent a S)*L S ∧ Regional o b T∧∀ i:Y, tariff T (receipt i)=trim 2 (fluxJet p (F S)) (collect SU.group i):=by
    by_cases T: U S=0
    · refine ⟨0,by simp only [costs,Pi.zero_apply,norm_zero,sum_const_zero]; have hp':= rent_pos a S; have hh:= hv S; positivity,(fun i v j=>(v rfl).elim),fun i=>?_⟩; have hp: fluxJet p (F S) =ᶠ[𝓝 0] fun _=> 0:=by filter_upwards [ball_mem_nhds 0 K.1] with y hy; unfold fluxJet; rw [show soloQ p (F S) (increment 1 y)=0 from ht₀ S T ⟨_,K.2.2.2.1 y (mem_ball_zero_iff.mp hy)⟩,show soloQ p (F S) 1 = 0 from ht₀ S T z,sub_zero]
      simp only [tariff,Nacre.trim,cake,(hp.iteratedFDeriv ℝ 2).eq_of_nhds,Pi.zero_apply,iteratedFDeriv_const_of_ne (by norm_num: 2≠0),smul_zero,sum_const_zero]; rfl
    have hs:=k S T; obtain ⟨V,hv',hp',L'⟩:= party o p (v S) K q (footprintGeodesic (f_then (v S) T) hs.1 le_rfl) (by omega:2*(S.card+1)<_)
    refine ⟨V,hv'.trans (y S.card _ (hv S)),fun i hi j=> ?_,fun i=>(L' i).symm⟩
    exact Corona.halo_mono hs.2.le le_rfl (hp' i hi j)
 choose T y P' Q0 using HF
 let W':=∑ i,T i
 have hk(i):=(feeLens p (v i) K 0 (norm_zero.trans_lt K.1)).order q
 refine ⟨W',⟨(fun i hi'=> ?_),(fun i=> ?_),?_,?_,?_,?_,?_⟩⟩
 · have hQ:= allows_sum (s:=univ) fun (j:Sa n) _=> feeLens p (v j) K i hi'; refine (hQ.mono ?_).germ (((Hx _ hi').trans (Eventually.of_forall (fun j=> Finset.sum_apply ..))).symm)
   rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hi (mul_nonneg zero_le_two K.2.2.1.le)
 · unfold W' trim cake; rw [tariffSum,(hW.iteratedFDeriv ℝ 2).eq_of_nhds]; simp_rw [Q0]; rw [iteratedFDeriv_sum_apply (u:=univ) (fun j _=> (hk j).smooth)]; simp only [Nacre.trim,cake,Finset.smul_sum,Tensor.diagonal, ContinuousMultilinearMap.sum_apply]
 · rw [hW.fderiv_eq, fderiv_sum]; swap; · exact fun i _=> (hk i).smooth.differentiableAt (by norm_num)
   exact sum_eq_zero (fun i _=>(flatCut p (v i) K q).1)
 · unfold costs W'; simp_rw [Finset.sum_apply]; apply le_trans (sum_le_sum (fun (i:ChainKey SU.group (More n)) _=> norm_sum_le univ (fun j=> T j i))); rw [sum_comm]; apply (sum_le_sum (fun i _=> y i)).trans
   simp_rw [mul_assoc,←mul_sum]; exact mul_le_mul_of_nonneg_left u g.le
 · intro i hx p; unfold W' at hx; rw [Finset.sum_apply] at hx
   obtain ⟨k,u,h⟩:= exists_ne_zero_of_sum_ne_zero hx; exact P' k i h p
 · intro i f; rw [show rawQ X (gauge f i.val)= _ from hR ⟨_,(show Guard _ _ from i.property).cov f⟩,hR i]
   exact sum_congr rfl fun S _=> taxLocal p (v S) i f
 intro i j t; rw [hR i,hR j]; apply sum_congr rfl; intro S _; by_cases T:U S=0
 · rw [ht₀ S T i, ht₀ S T j]
 have h0:= k S T; exact congrArg Matrix.trace (coinLocal p (v S) (agrees_mono t (coe_subset.mpr (footprintGeodesic (f_then (v S) T) h0.1 h0.2.le))))
end YM.CF.Swell.Sonar
