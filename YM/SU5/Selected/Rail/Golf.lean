import YM.SU5.Selected.Rail.Wallis
/-! # Hankel integral controls moments even after a transverse Fourier shift with arbitrarily large *fixed* W. No quantifying across polynomial degree. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder NNReal ENNReal
local notation "I"=>Complex.I
local notation "φ" => 2*π
attribute [local instance] opCStarAlgebra
open Finset
local notation "d" y:max v:max=> dollar y v
variable {n k:ℕ}{x:Facet3}{W:FaceL} (h:k≥3){p:ℕ} (Z:Fin p→ℂ)
def aero(Z:Fin p→ℂ)(k:ℕ)(n:ℕ)(x:Facet3):ℂ:= ∑ i:Fin p,∑ j:Fin p, star (Z i) * (hammer k (n+i.val+j.val) x* Z j)
def gleam(Z:Fin p→ℂ)(k:ℕ)(n:ℕ)(x:Facet3)(v:FaceL):ℝ:=stake k n x v*‖plum Z x v‖^2
lemma gleam_c {x:Facet3}(c:x∈Cliff)(e:4≤n):HasSum (fun v=>(↑(gleam Z k n x v):ℂ)) (aero Z k n x):=by
 let Y(v:FaceL)(i:Fin p):ℝ:= d x v ^ i.val
 let A(v):=stake k n x v; let s (i j:Fin p)(v):= star (Z i) * (↑(A v)*((Y v i:ℂ)*(Y v j:ℂ)) * Z j)
 have he (v:FaceL)(i j:Fin p): ↑(A v)*((Y v i:ℂ)*(Y v j:ℂ))=(stake k (n+i.val+j.val) x v:ℂ):=by rw [script_add,script_add]; unfold Y A; push_cast; ring
 have h(i j:Fin p):HasSum (s i j) (star (Z i)*(hammer k (n+i.val+j.val) x*Z j)):=by unfold s; simp_rw [he]; exact ((counts_t (k:=k) c (by omega)).mul_right _).mul_left _
 have ht(v:FaceL): ∑ i, ∑ j,s i j v=(gleam Z k n x v:ℂ):=by
    rw [gleam,Complex.ofReal_mul,←Complex.normSq_eq_norm_sq,← Complex.mul_conj]; unfold plum s Y A; simp_rw [map_sum,sum_mul,mul_sum,map_mul]; symm; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; simp; ring
 have hs(i:Fin p): HasSum (fun v=>∑ j,s i j v) (∑ j:Fin p, star (Z i)*(hammer k (n+i.val+j.val) x*Z j)):=by simpa only [Finset.sum_apply] using hasSum_sum (s:=univ) (f:=s i) (fun (j:Fin p) _=> h i j)
 simp_rw [←ht,aero]; simpa only [Finset.sum_apply] using hasSum_sum (s:=univ) (f:=fun i v=> ∑ j,s i j v) (fun (i:Fin p) _=> hs i)
lemma gleam_nonneg (z:x∈Cliff)(v:FaceL):0≤ gleam Z k n x v:= mul_nonneg (stake_pos z k n v) (sq_nonneg _) -- stake_pos args not known
include h
lemma aero_c:ContinuousOn (aero Z k n) hill:= by
 unfold aero; have hp(t:ℕ):=hammer_c h t; fun_prop -- no auto include h? `def ContinuousOn` elabs before h binder include first
omit h
-- core Gauss around tiny point fixed polynomial. interpret re
lemma flying {n:ℕ}(e:4≤n)(z:x∈Cliff):
     HasSum (gleam Z k n x) (aero Z k n x).re ∧ (aero Z k n x).im=0:=by
 have h:=gleam_c Z z (k:=k) e; have hp:=Complex.hasSum_re h; have hg:=Complex.hasSum_im h; constructor; · exact hp
 exact hg.unique (show HasSum _ 0 from hasSum_zero) -- names
#check stake_pos
lemma studio (z:x∈Cliff)(t:∀ v, 0≤ gleam Z k n x v)(e:4≤n): 0≤(aero Z k n x).re:=hasSum_le (f:=fun _:FaceL=> (0:ℝ)) t hasSum_zero (flying Z e z).1 -- defeq zero
lemma stone_vibe (u:ℕ)(z:x∈Cliff){T c:ℝ}(hT:0≤T)(p:T ≤ dollar x 0)(h:0≤(grappa W x).re)(hc:c≤ royalty k W Z x): c*T^u≤(grappa W x*aero Z k (4+u) x).re:=by
 rw [Complex.mul_re,(flying Z (by omega) z).2,mul_zero,sub_zero]
 have ht: (grappa W x).re * gleam Z k (4+u) x 0 ≤ _ := mul_le_mul_of_nonneg_left (le_hasSum (flying Z (by omega) z).1 _ (fun i _=> gleam_nonneg Z z _)) h
 apply le_trans _ ht; apply (mul_le_mul_of_nonneg_right hc (pow_nonneg hT u)).trans
 have hp:0≤ royalty k W Z x:= mul_nonneg h (gleam_nonneg Z z 0); apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT p _) hp).trans; unfold gleam royalty; rw [script_add]; exact Eq.le (by ring)
lemma stone_halt {z:ℝ} (u:ℕ)(t:x∈Cliff)(p:z≤‖x‖)(q:0<z) :
    -((aero Z k 4 x).re * (Real.exp (-z))^u) ≤(grappa W x * aero Z k (4+u) x).re:=by
 have hf(v):0 ≤ gleam Z k 4 x v:= gleam_nonneg Z t v
 have ht(v:FaceL): d x v≤ Real.exp (-z):= Real.exp_le_exp.mpr (neg_le_neg (p.trans (least v t.1)))
 have hv(v:FaceL): gleam Z k (4+u) x v ≤ gleam Z k 4 x v *(Real.exp (-z))^u:=by
    apply le_trans _ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤d x v from (Real.exp_pos _).le) (ht v) u) (hf v)); unfold gleam; rw [script_add]; exact Eq.le (by ring)
 rw [Complex.mul_re,(flying Z (by omega) t).2,mul_zero,sub_zero]; have h:=hasSum_le hv (flying Z (by omega) t).1 ((flying Z (by omega) t).1.mul_right _)
 have he: -1 ≤ (grappa W x).re:= (abs_le.mp (grappa_m ..)).1; nlinarith only [mul_le_mul_of_nonneg_right he (studio (k:=k) (n:=4+u) Z t (gleam_nonneg Z t) (by omega)),h]
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms stone_halt
#print axioms stone_vibe
#print axioms flying
#print axioms aero_c
