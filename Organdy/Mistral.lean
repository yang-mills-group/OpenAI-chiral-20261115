
import Organdy.Chrys
import Organdy.Dawn
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Larva
open Filter Topology Metric Lattice Exterior Precision 
open Tulip Branch Cube Lat Tenant Drapes _root_.Zephyr.Chern

open scoped Matrix.Norms.L2Operator Matrix
attribute [local instance] opCStarAlgebra
local notation "G" => SU.group
variable {N m:Side}{d r:ℝ}


open Pressure Wilson Work.F03 Next.Rank.Spindle Payne
variable {S:Band N}{P:Oil N}{C:Toll (Single N)}
variable {o:Site (More N)}{k:ℕ}

variable (h:Piece d S C P) (R:Rules G)(t:Spool d r)
 (e:2*(k+1)<(More N).val)(f:∀i∈leaks S,separation o i.1≤k)
def scale (k:ℕ)(r c:ℝ):=sweets r*c*(1+r)*(stretch k)^2
lemma scaleN (k:ℕ){c:ℝ}(p:0≤r)(q:0≤c):0≤scale k r c:=by
 have e:=sweets_nonneg p;unfold scale;positivity

include h R t e f
lemma warden {V U:Wilson.Config SU.group (More N)}(a:Tiny d V)
 (l:∀i∈leaks S,V i=U i)
 {b:ℝ}(p:0≤b)(z:stretch k*b < min R.c r)
 (w: Cheap o k U b):
 ‖story P V - sketch P 0‖ ≤ scale k r (ledgerV C) * b^2 :=by
 obtain ⟨g,Y,v,j⟩:= dawn R e p (z.trans_le (min_le_left ..)) w
 have n:‖Y‖< r:= v.trans_lt (z.trans_le (min_le_right ..))
 have u:story P V = sketch P Y:=by
   apply reword h a (pinpoint t (show ‖Y‖<2*r by linarith [t.1])) g
   intro i y
   rw [←j i (f i y)]
   simp only [Lattice.gauge,l i y]

 rw [u,scale,mul_assoc (sweets r * ledgerV C * (1+r)), ←mul_pow]
 apply (ryme h t n).trans
 exact (mul_le_mul_of_nonneg_left
   (pow_le_pow_left₀ (norm_nonneg _) v 2)
   (mul_nonneg (fiction h t).honey.plus (by linarith [t.1]))).trans_eq (by ring)

lemma ordained' (x: Dir (More N)) (M:ℝ) (p:0≤M)
 (l:∀i:Cell (More N),separation o i.1≤k+1 → ‖faceCurl i x‖ < M):
 ‖poem P x‖ ≤ scale k r (ledgerV C)*M^2 :=by
 let a:=scale k r (ledgerV C)*M^2
 let v:=sweets r * ledgerV C * ‖x‖^3
 
 have hx:Tendsto (fun q:ℝ=> v*q+a) (𝓝[>] 0) (𝓝 a):=
    by
    have u:Continuous (fun q=> v*q+a):=by fun_prop
    simpa only [mul_zero,zero_add] using (u.continuousWithinAt (x:=0) (s:=Set.Ioi 0)).tendsto
 apply ge_of_tendsto hx
 -- filter rhs
 have j: ∀ᶠ q:ℝ in 𝓝[>] 0, q*‖x‖<r:=
   (continuous_id'.mul continuous_const).continuousWithinAt.tendsto.eventually
     (gt_mem_nhds (show (0:ℝ)*‖x‖<r by simpa using t.1))
 have m: ∀ᶠ q:ℝ in 𝓝[>] 0, stretch k*(q*M) < min R.c r:=
   (continuous_const.mul (continuous_id'.mul continuous_const)).continuousWithinAt.tendsto.eventually
     (gt_mem_nhds (show stretch k*((0:ℝ)*M)<min R.c r by rw [zero_mul,mul_zero];exact lt_min R.radius t.1))
 filter_upwards [j,m,cheapShots _ _ l,self_mem_nhdsWithin] with q q0 n w u
 change 0<q at u
 have g:‖q•x‖<r:=by simpa [norm_smul,abs_of_pos u] using q0
 let b:=poem P x

 have hu:‖poem P (q•x)‖=q^2*‖b‖:=by
    obtain ⟨Q,p,-⟩:= poem_bend h t
    unfold b
    rw [p,p,map_smul,map_smul Q, LinearMap.smul_apply,norm_smul,norm_smul,Real.norm_eq_abs,abs_of_pos u]
    ring
 apply le_of_mul_le_mul_left _ (pow_pos u 2)
 change q^2*‖b‖ ≤ _
 rw [←hu]
 apply (norm_le_norm_sub_add _ (sketch P (q•x)-sketch P 0)).trans
 rw [norm_sub_rev]
 refine (add_le_add (rhyme h t g) (warden h R t e f (V:=represent (q•x))
   (pinpoint t (show ‖q•x‖<2*r by linarith [t.1])) (fun i _=>rfl) (mul_nonneg u.le p) n w)).trans_eq ?_
 rw [norm_smul,Real.norm_eq_abs,abs_of_pos u]
 unfold v a;ring

lemma ordained (x: Dir (More N)) (M:ℝ) (p:0≤M)
 (l:∀i:Cell (More N),separation o i.1≤k+1 → ‖faceCurl i x‖ ≤ M):
 ‖poem P x‖ ≤ scale k r (ledgerV C)*M^2 :=by
 have hx:Tendsto (fun q:ℝ=>scale k r (ledgerV C)*q^2) (𝓝[>] M) (𝓝 (scale k r (ledgerV C)*M^2)):=(continuous_const.mul (continuous_id'.pow 2)).continuousWithinAt
 apply ge_of_tendsto hx
 filter_upwards [self_mem_nhdsWithin] with y q
 exact ordained' h R t e f x y (p.trans ((show M<y from q).le)) (fun i v=> (l i v).trans_lt q)
