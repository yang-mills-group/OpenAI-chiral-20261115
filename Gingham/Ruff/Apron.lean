import Gingham.Ruff.Kestrel
import Gingham.Ruff.Cote
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

variable (f g:Chin N→OP N)
def block (u:Side)(y:Site N):=
 ∑ x∈apron u, WW (y+wrap N x)
lemma block_comm (u:Side)(y:Site N):
 Commute (tickA N) (block u y) := by
  unfold block Commute SemiconjBy
  rw [mul_sum,sum_mul]; exact sum_congr rfl fun _ _=> (WW_A ..).eq
lemma WW_disjoint {x y:Site N}(h:x≠y):WW x * WW y = 0:=by
  have t:(WW x* WW y)*1=0:=by
    rw [mul_assoc]; ext i j;rw [WWi,WWi,Matrix.zero_apply];split_ifs with hx hy
    · exact False.elim (h (hx.symm.trans hy))
    all_goals rfl
  rwa [mul_one] at t

lemma block_p (u:Side)(y:Site N)(h: 2*u.val < N.val):
 IsStarProjection (block u y):=by
  have q(x:Cover)(p:x∈apron u)(i:Axis):
      -(N.val:ℤ)<2*x i ∧ 2*x i≤(N.val:ℤ):=by
    have := apron_spec.mp p i; omega
  unfold block
  constructor
  swap
  · -- order?
    change star (∑ x∈apron u, WW (y+wrap N x)) = _
    rw [star_sum]
    exact sum_congr rfl fun x _=>(WW_p (y+Lattice.wrap N x)).isSelfAdjoint
  change (∑ x∈apron u,WW (y+wrap N x)) * _ = _


  rw [mul_sum];apply sum_congr rfl
  intro x p; rw [sum_mul,sum_eq_single_of_mem x p (fun z r b=>WW_disjoint
      (fun t=> b (wrap_injOn N (q z r) (q x p) (add_left_cancel t))))]
  exact (WW_p _).isIdempotentElem.eq

def yoke (u:Side)(y:Site N)(p:Chin N):=
 (f p-tickA N) * block u y
lemma yoke_sum (u:Side)(y:Site N)(p:Chin N):
 yoke f u y p=∑ x∈apron u,breast f (y+wrap N x) p:=by rw [yoke,block,mul_sum]; rfl

def oriole (u:Side)(y:Site N)(p:Chin N):=𝒪 (f p) (g p) (block u y)
def bust (u:Side)(y:Site N)(p:Chin N):= 𝒜 (f p) (tickA N) (block u y)
def bond (u:Side)(i:Axis)(t:Site N)(p:Chin N):=
  purl u (fun y=>sprit f g i y p) i t

lemma bust_yoke (u:Side)(y:Site N)(p:Chin N):
   bust f u y p= Matrix.trace (yoke f u y p):=rfl


theorem cadenza (u:Side)(y:Site N)(p:Chin N)(h:IsStarProjection (f p)):
    ∑ i, (bond f g u i (y+pleat u i) p - bond f g u i (y-pleat u i) p)=
     oriole f g u y p:=by
  simp only [bond]
  rw [←tucks u (fun i y=> sprit f g i y p), oriole, block, ←𝒪_sum]
  exact sum_congr rfl fun x _=> sprit_div f g _ p h


abbrev Garland (y:Site N)(u:Side):= Dahlia y (2*(u.val+1)) 5
def seamMoney (u:Side)(x:ℝ):ℝ:= (apron u).card*x

variable {a c e:ℝ}{f g}

lemma patron (u:Side)(y:Site N)(ha:0≤a)(h:Solo a c f e):
 Garland y u (a/2) (seamMoney u (c+wingRent Fir.Aop a)) (yoke f u y) e := by
  have X(j:Cover) (p:j∈apron u):
      Garland y u a (c+wingRent Fir.Aop a) (breast f (y+wrap N j)) e:=by
    apply (dahlia
           (feathers1 (y+wrap N j) h)
           (show separation y _ ≤ u.val+1 from by
             rw [separation_comm,separation,add_sub_cancel_left]
             exact (Work.E01.pdist_wrap_le (bottled p)).trans (by omega))).shape
    intro S i j' _ _ _ t v w
    exact (t v w).trans (by omega)
  have q:= Brooch.sumK (apron u) (fun _=>c+wingRent Fir.Aop a) (fun x p=>breast f (y+wrap N x) p.val)
      (s:=bail N e) (t:=bail N e) (fun j h=> X j h)
  simp only [sum_const,nsmul_eq_mul,←yoke_sum] at q
  exact q.drop (by linarith)


lemma courier (u:Side)(y:Site N)(i:Axis)(ha:0<a)(h:Solo a c f e)(g':Solo a c g e):
  Garland y u (a/2) (seamMoney u (aviary a c)) (bond f g u i y) e:=by
  have hc:= (show Dahlia y 0 5 _ _ _ _ from moorhen ha h g' i y).positive
  have X(j:Cover)(p:j∈flap u i):
      Garland y u (a/2) (aviary a c) (sprit f g i (y+wrap N j-Lattice.step i)) e:=by
    let z:=y+wrap N j-Lattice.step i
    have hx:separation y (y+wrap N j)≤u.val:=by
      rw [separation_comm,separation,add_sub_cancel_left]
      exact Work.E01.pdist_wrap_le (bottled (mem_filter.mp p).1)
    have hv:separation (y+wrap N j) z ≤1:=by
      unfold z;rw [reverseSep];exact pdist_step _
    have hz:separation (node y) (node z)≤ 2*(u.val+1):=by
      rw [iguana]
      exact Nat.mul_le_mul_left _ ((separation_triangle ..).trans (add_le_add hx hv))
    apply (show Dahlia z 0 5 _ _ _ _ from moorhen ha h g' i z).shape
    intro S _ _ _ _ _ T x w
    exact (separation_triangle _ (node z) x).trans ((add_le_add hz (T x w)).trans (by simp))


  refine (Brooch.sumK (flap u i) (fun _=>aviary a c)
      (fun j p=> sprit f g i (y+wrap N j-Lattice.step i) p.val)
      (s:=bail N e) (t:=bail N e) (fun j p=>X j p)).books ?_
  simp only [sum_const,nsmul_eq_mul,seamMoney]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card (Finset.filter_subset _ _)) hc
#print axioms cadenza
#print axioms courier

