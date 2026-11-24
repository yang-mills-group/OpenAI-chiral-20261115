import GaugeFieldConstruction.Cloud
/-!
# weighted jet bill, pair Leg on physical T, arbitrary families of tangent reads
-/
set_option autoImplicit false
set_option maxHeartbeats 45000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {f c:Side}{G:Ratio c f} {M:Male}{b:Bool}{o:Skye.Seat f}{Q:Op (Single f)}{h HI:ℝ}{t k r:ℕ}
-- symbolic tensor barriers. cost even for same labels.
abbrev ThetaS (i j:Mill→ℂ)(x:Mill × Mill):= star (i x.1)* j x.2
def ThetaX (x: Mill×Mill):= wagN 3 x.1 + wagN 3 x.2
lemma θPos (x): 0≤ThetaX x:= add_nonneg (zero_le_one.trans (wagE ..)) (zero_le_one.trans (wagE ..))
def θLook (f g:ℕ→ Mill→ℂ)(n:ℕ): Mill × Mill →ℂ:= ∑ r∈ range n, ∑ i∈ range (n-r),ThetaS (f r) (g i)
private def θsplit (f g:ℕ→ Mill→ℂ)(n:ℕ): Mill ×Mill→ℂ:= ∑ r∈ range (n+1), ThetaS (f r) (g (n-r))
lemma Look_next (f g:ℕ→ Mill→ℂ)(n:ℕ): θLook f g (n+1)= θLook f g n+ θsplit f g n:=by
 unfold θLook θsplit; rw [sum_range_succ,sum_range_succ (f:=fun r=>ThetaS (f r) (g (n-r)))]; rw [Nat.add_sub_cancel_left,Nat.sub_self,sum_range_one]; rw [← add_assoc, ←sum_add_distrib]; congr 1; apply sum_congr rfl; intro i p; have he:i<n:=mem_range.mp p; rw [show n+1-i=n-i+1 from by omega,sum_range_succ]
lemma ητ_input (a b:Mill→ℂ)(x y:ℕ)(p q:ℝ)(e:chime (wagN x) a p)(h:chime (wagN y) b q):chime (fun i:Mill×Mill=> wagN x i.1* wagN y i.2) (ThetaS a b) (p*q):=by
 let v i:= q*(wagN x i*‖a i‖); apply SBprod (F:=fun i j=> (wagN x i* wagN y j)*‖ThetaS a b (i,j)‖) (f:=v)
 · intro i; apply SBqual' (SBscale h (show 0≤ wagN x i*‖a i‖ from mul_nonneg (zero_le_one.trans (wagE ..)) (norm_nonneg _))) (fun _=> mul_nonneg (mul_nonneg (zero_le_one.trans (wagE ..)) (zero_le_one.trans (wagE ..))) (norm_nonneg _)) (le_of_eq (mul_comm ..)); intro j; apply le_of_eq; unfold ThetaS; rw [norm_mul,norm_star]; ring
 exact SBmono (SBscale e (t:=q) (SBgoed h)) (le_of_eq (mul_comm ..))
lemma sum_upking (a b: Mill→ℂ)(s t v w:ℝ)(p:chime (wagN 0) a s)(q:chime (wagN 3) a t)(h:chime (wagN 0) b v)(x:chime (wagN 3) b w) : chime ThetaX (ThetaS a b) (t*v+s*w):=by apply SBqual (SBplus (ητ_input a b 3 0 _ _ q h) (ητ_input a b 0 3 _ _ p x)) (fun i=>mul_nonneg (θPos i) (norm_nonneg _)); intro i; unfold ThetaX; simp only [wagN,pow_zero,mul_one,one_mul, add_mul,le_refl]
lemma withinZ {E F:Mill×Mill→ℂ}{Z W:ℝ}(p:chime ThetaX E Z)(q: chime ThetaX F W): chime ThetaX (E+F) (Z+W):= SBqual (SBplus p q) (fun i=>mul_nonneg (θPos i) (norm_nonneg _)) fun i=>(mul_le_mul_of_nonneg_left (norm_add_le (E i) (F i)) (θPos i)).trans_eq (mul_add ..)
lemma withinB {E F:Mill×Mill→ℂ}{Z W:ℝ}(p:chime ThetaX E Z)(q: chime ThetaX F W): chime ThetaX (E-F) (Z+W):= SBqual (SBplus p q) (fun i=>mul_nonneg (θPos i) (norm_nonneg _)) fun i=>(mul_le_mul_of_nonneg_left (norm_sub_le (E i) (F i)) (θPos i)).trans_eq (mul_add ..)
lemma withinC {E:Type}(S:Finset E)(A:E→ Mill ×Mill →ℂ)(V:E→ℝ)(h:∀ i∈ S,chime ThetaX (A i) (V i)): chime ThetaX (∑ i∈S,A i) (∑ i∈S,V i):= by
 classical
 induction S using Finset.induction_on with
 | empty=> simp [FlightFlux.chime,SumBudget] -- tune conflict
 | @insert i S p ih=> rw [sum_insert p,sum_insert p]; exact withinZ (h _ (mem_insert_self ..)) (ih fun i u=>h i (mem_insert_of_mem u))
local notation "ρ"=> αN G.count
-- *cone costs in max norm before Logos.*
variable {F G':ℕ→ Mill →ℂ}{X Y:Mill→ℂ} {B L u v s:ℝ}
structure Upk (F:ℕ→ Mill→ℂ)(X:Mill→ℂ)(B L A:ℝ):Prop where
 value: chime (wagN 0) X B
 weigh: chime (wagN 3) X (B*(1+A*L)^3)
 access (r:ℕ)(h:r≤2)(n:ℕ)(k:n≤3): chime (wagN n) (F r) (B*A^r*L^r)
 near (f:A*L≤1) (r:ℕ)(h:r≤3)(n:ℕ)(k:n≤3): chime (wagN n) (X-∑ i∈range r,F i) (12*B*A^r*L^r)
variable (a c d q:ℝ) (T:Upk F X a c d)(iT:Upk G' Y q c d)
local notation "Θq"=> ThetaS X Y
local notation "L₀"=> d*c
private abbrev ℓflags (X:Mill→ℂ)(F:ℕ→Mill→ℂ)(i:ℕ):= X-∑ k∈ range i,F k
lemma κ_turn (n:ℕ): Θq - θLook F G' n = ThetaS (ℓflags X F n) Y + ∑ i∈range n, ThetaS (F i) (ℓflags Y G' (n-i)):=by -- algebra
 unfold θLook; ext1 x; simp only [Finset.sum_apply,Pi.sub_apply,Pi.add_apply]; unfold ThetaS ℓflags; simp only [Finset.sum_apply, Pi.sub_apply,Pi.add_apply,star_sub,star_sum]; simp only [sub_mul,mul_sub, mul_sum,sum_mul, sum_sub_distrib]; abel
include T iT
lemma κ_near (p:0 <a)(b:0<q)(g:0<d)(w:d*c≤1)(e:1 ≤ c)(r:ℕ)(u:r≤3): chime ThetaX (Θq - θLook F G' r) ((1800:ℝ)*a*q*d^r*c^3):=by
 rw [κ_turn]
 let E:= ThetaS (ℓflags X F r) Y; let V:=a*q*d^r*c^r; have hc:0<c:=zero_lt_one.trans_le e; have hz:0≤V:=by positivity
 have hp: chime ThetaX E (108*V):=by
    apply SBmono (sum_upking _ _ _ _ _ _ (T.near w r u 0 (by omega)) (T.near w r u 3 (by omega)) iT.value iT.weigh)
    calc
      _ ≤ 12 * a * d ^ r * c ^ r * q + 12 * a * d ^ r * c ^ r * (q*(2:ℝ)^3) := by gcongr <;> linarith
      _ = _:=by unfold V; ring
 let X'(i) :=ThetaS (F i) (ℓflags Y G' (r-i))
 have hx(i:ℕ)(z:i∈range r): chime ThetaX (X' i) (24*V):=by
    have hi:i<r:=mem_range.mp z; let hT:= T.access i (by omega); let ht:= iT.near w (r-i) (by omega)
    apply SBmono (sum_upking _ _ _ _ _ _ (hT 0 (by omega)) (hT 3 (by omega)) (ht 0 (by omega)) (ht 3 (by omega))); apply le_of_eq; unfold V; have he:d^r=d^i*d^(r-i):=(pow_add d i (r-i)).symm.trans (congrArg _ (Nat.add_sub_of_le hi.le))|>.symm -- tune
    have hz:c^r=c^i*c^(r-i):= (by rw [←pow_add, Nat.add_sub_of_le hi.le])
    rw [he,hz]; ring
 apply SBmono (withinZ hp (withinC (range r) X' (fun _=>24*V) hx)); rw [sum_const, card_range,nsmul_eq_mul]; unfold V; let P:=a*q*d^r; have hP:0 ≤ P:=by unfold P; positivity
 calc _ = (108+(r:ℝ)*24)*(P*c^r):=by unfold P; ring
      _ ≤ 1800*(P*c^3):= by have h : (r:ℝ)≤3:=(by exact_mod_cast u); have hv': c^r ≤ c^3:= pow_le_pow_right₀ e u; gcongr <;> linarith
      _ = _:= by unfold P; ring
lemma κ_outer (p:0 <a)(b:0<q)(g:0<d)(w:1 ≤ d*c)(e:d≤1)(c':1 ≤c)(r:ℕ)(u:r≤3): chime ThetaX (Θq - θLook F G' r) ((1800:ℝ)*a*q*d^r*c^3):=by
 let C:= d*c; let E:= a*q*C^3; have he:0 < C:=zero_lt_one.trans_le w; have hz:0 ≤ E:=by unfold E; positivity
 have hh : chime ThetaX Θq (16*E):=by
    apply SBmono (sum_upking X Y _ _ _ _ T.value T.weigh iT.value iT.weigh)
    calc
        _ ≤ a*(2*C)^3*q+a*(q*(2*C)^3):=by change a*(1+C)^3*q+a*(q*(1+C)^3)≤_; have h:1+C≤2*C:=(by change 1≤ C at w; linarith); gcongr
        _ = _:=by unfold E; ring
 let X':=θLook F G' r
 have hp: chime ThetaX X' (18*E):=by
    have hx(i :ℕ)(z:i∈range r): let S:= range (r-i); chime ThetaX (∑ j∈S,ThetaS (F i) (G' j)) (6*E):=by
        let hX:= mem_range.mp z; have hV:=T.access i (by omega); intro S; apply SBmono (withinC S _ (fun _=>2*E) _); · rw [sum_const, show S.card=r-i from card_range _, nsmul_eq_mul]; have h: ((r-i:ℕ):ℝ)≤3:=(by exact_mod_cast (show r-i≤3 by omega)); linarith only [mul_le_mul_of_nonneg_right h (show 0≤2*E by positivity)]
        intro j l; have hg:j< r-i:=mem_range.mp l; have ht:=iT.access j (by omega); apply SBmono (sum_upking _ _ _ _ _ _ (hV 0 (by decide)) (hV 3 le_rfl) (ht 0 (by decide)) (ht 3 le_rfl)); -- tune
        calc
            _ = 2*(a*q)*C^(i+j):=by unfold C; rw [pow_add]; ring
            _ ≤ 2*(a*q)*C^3:=by exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ w (by omega)) (by positivity)
            _ = _:=by unfold E; ring
    apply SBmono (withinC (range r) (fun i=> ∑ j∈range (r-i),ThetaS (F i) (G' j)) (fun _=>6*E) hx); rw [sum_const,card_range,nsmul_eq_mul]; linarith only [mul_le_mul_of_nonneg_right (show (r:ℝ) ≤3 from by exact_mod_cast u) (show 0 ≤ 6*E from by positivity)]
 apply SBmono (withinB hh hp); rw [show 16*E+18*E=34*a*q*d^3*c^3 from (by unfold E C; ring)]; have ht:d^3 ≤ d^r:= pow_le_pow_of_le_one g.le e u; gcongr; norm_num -- tune
end Boom
end YM.CF.TableF
end
