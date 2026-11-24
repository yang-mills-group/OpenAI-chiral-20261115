import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Damask
open Function Set Filter Complex Metric Polynomial
open scoped Topology BigOperators Polynomial Classical


/-- Entire + integer order of growth. -/
theorem slow (n:ℕ){f:ℂ→ℂ}{c:ℝ}(d:Differentiable ℂ f)
   (r:∀z:ℂ,1≤‖z‖→ ‖f z‖≤ c*‖z‖^n) :
 ∃ p:ℂ[X], p.natDegree≤n ∧ ∀z:ℂ,p.eval z=f z:=by
 induction n generalizing f c with
 | zero=>
    refine ⟨C (f 0),by simp,fun z=>?_⟩
    rw [eval_C]
    refine d.apply_eq_apply_of_bounded (isBounded_range_iff.mpr ?_) _ _
    obtain ⟨k,h⟩:∃k:ℝ, ∀ z∈closedBall (0:ℂ) 1, ‖f z‖≤k:=by
        obtain ⟨y,b⟩:= (isCompact_closedBall (0:ℂ) 1).bddAbove_image d.continuous.norm.continuousOn
        exact ⟨_,fun z p=> b (mem_image_of_mem _ p)⟩
    have u(z:ℂ):‖f z‖ ≤ max k c:=by
       by_cases p:1≤‖z‖
       · exact (r z p).trans (by simp)
       exact le_max_of_le_left (h z (by simpa using (lt_of_not_ge p).le))
    exact ⟨_,fun x y=> (dist_le_norm_add_norm ..).trans (add_le_add (u x) (u y))⟩

 | succ n ih=>
    let g:= dslope f 0
    have e:Differentiable ℂ g := differentiableOn_univ.mp ((differentiableOn_dslope univ_mem).mpr d.differentiableOn)
    have b(z):z*g z=f z-f 0:=by simpa only [sub_zero,smul_eq_mul] using sub_smul_dslope f 0 z
    have h(z:ℂ)(p:1≤‖z‖):‖g z‖≤ (c+‖f 0‖)*‖z‖^n:= by
        apply le_of_mul_le_mul_left _ (show (0:ℝ)<‖z‖ from by linarith)
        rw [← norm_mul,b,mul_comm] -- targets?
        have j:(1:ℝ) ≤ ‖z‖^(n+1):= one_le_pow₀ p
        have m:‖f z-f 0‖≤ c*‖z‖^(n+1)+‖f 0‖*‖z‖^(n+1):=
           (norm_sub_le ..).trans (add_le_add (r z p) (le_mul_of_one_le_right (norm_nonneg _) j))
        refine m.trans_eq ?_; rw [pow_succ];ring
    obtain ⟨a,u,v⟩:=ih e h
    refine ⟨X * a + C (f 0), (natDegree_add_le ..).trans (max_le ?_ ?_),fun z=>?_⟩
    · exact natDegree_mul_le.trans (by rw [natDegree_X];omega)
    · simp
    simp [v,b]


def disc(z:ℂ):ℂ:=exp (z * I)

local notation "τ"=> 2*Real.pi
lemma disc_norm(z:ℂ): ‖disc z‖=Real.exp (-z.im):=by simp [disc,norm_exp]
lemma disc_ne(z:ℂ):disc z≠0:= exp_ne_zero _
lemma disc_deep(t:ℝ):disc (t*I)=Real.exp (-t):=by
 rw [disc,mul_assoc,I_mul_I]; simp
lemma disc_cusp(z:ℂ):Periodic.qParam (τ) z=disc z:=by
 unfold Periodic.qParam disc
 push_cast
 apply congrArg
 have u:=Real.pi_pos.ne'
 field_simp
lemma disc_daily:Periodic disc (↑(τ:ℝ):ℂ):=by
 intro z
 unfold disc;push_cast
 rw [add_mul,exp_add,exp_two_pi_mul_I,mul_one]

structure Oscillates (n:ℕ)(f:ℂ→ℂ): Prop where
 turns : Periodic f (↑(τ:ℝ):ℂ)
 hol : Differentiable ℂ f
 cost : ∃c:ℝ,∀z, ‖f z‖ ≤ c*Real.exp |z.im| ^ n

def Studded (n:ℕ)(f:ℂ→ℂ):Prop:=
 ∃p:ℂ[X], p.natDegree ≤ n+n ∧ ∀z,p.eval (disc z)=disc z ^ n * f z

open Asymptotics


theorem Oscillates.daily {n:ℕ}{f:ℂ→ℂ}(h:Oscillates n f):Studded n f:=by
 obtain ⟨c,g⟩:=h.cost
 let F(z:ℂ):=disc z ^ n * f z
 have he:Periodic F (↑(τ:ℝ):ℂ):=fun z=>by simp only [F,disc_daily z,h.turns z]
 have hF:Differentiable ℂ F:=by unfold F disc; have :=h.hol; fun_prop
 have hx(z:ℂ): ‖F z‖≤ c*(Real.exp (-z.im) ^ n * Real.exp |z.im| ^ n):=by
    dsimp only [F]; rw [norm_mul,norm_pow,disc_norm]
    exact (mul_le_mul_of_nonneg_left (g z) (by positivity)).trans_eq (by ring)
 have hy:BoundedAtFilter (comap Complex.im atTop) F:=by
    apply (isBigO_iff_isBigOWith.mpr ⟨c,?_⟩)
    refine (isBigOWith_iff.mpr ?_)
    filter_upwards [tendsto_comap.eventually (eventually_ge_atTop (0:ℝ))] with z hz
    exact (hx z).trans_eq (by rw [abs_of_nonneg hz,←mul_pow,←Real.exp_add];simp)
 let G:=Periodic.cuspFunction (τ) F
 have ht:0<(τ):=by positivity
 have hz:DifferentiableAt ℂ G 0:= Periodic.differentiableAt_cuspFunction_zero ht he (Eventually.of_forall hF) hy

 have hG:Differentiable ℂ G:=by
    intro u
    by_cases p:u=0
    · exact p ▸ hz
    rw [← Periodic.qParam_right_inv ht.ne' p]
    exact Periodic.differentiableAt_cuspFunction ht.ne' he (hF _)
 have hh(z):G (disc z)=F z:=by rw [← disc_cusp]; exact Periodic.eq_cuspFunction ht.ne' he z
 have hL(u:ℂ)(p:1≤‖u‖): ‖G u‖≤ c*‖u‖^(n+n):=by
    have r:u≠0:=by intro q;rw [q,norm_zero] at p;norm_num at p
    let z:=Periodic.invQParam (τ) u
    have hZ:disc z = u:= (disc_cusp z).symm.trans (Periodic.qParam_right_inv ht.ne' r)
    rw [← hZ,disc_norm] at p
    rw [← hZ,disc_norm,hh]
    refine (hx z).trans_eq ?_
    have d:z.im≤0:= neg_nonneg.mp (Real.one_le_exp_iff.mp p)
    rw [abs_of_nonpos d,pow_add]
 obtain ⟨p,r,t⟩:= slow _ hG hL
 exact ⟨p,r,fun z=>(t _).trans (hh z)⟩



variable {r:ℕ}{f:ℂ→ℂ}
abbrev Rank (r:ℕ):=Fin (r+r+1)
def hoops (r:ℕ)(u:Rank r→ℂ)(z:ℂ)(i:Rank r):ℂ:=
 (disc z ^ r)⁻¹ * disc (u i)^r *
   Polynomial.eval (disc z) (Lagrange.basis Finset.univ (disc ∘ u) i)

lemma Studded.interp (h:Studded r f)(u:Rank r→ℂ)(v:Injective (disc ∘ u))(z:ℂ):
 f z=∑ i,hoops r u z i * f (u i):=by
 obtain ⟨p,n,t⟩:=h
 apply mul_left_cancel₀ (pow_ne_zero r (disc_ne z))
 rw [← t,Finset.mul_sum]
 have d:p.degree<↑(Finset.univ:Finset (Rank r)).card:=by
    refine degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr ?_)
    simpa [Rank] using Nat.lt_succ_of_le n
 rw [Lagrange.eq_interpolate v.injOn d,Lagrange.interpolate_apply,eval_finsetSum]
 refine Finset.sum_congr rfl fun i _=>?_
 rw [eval_mul,eval_C,Function.comp_apply,t, hoops]
 let b:=disc z ^ r
 have y:b≠0:= pow_ne_zero r (disc_ne z)
 have w(w c d:ℂ): w*c*d=b*(b⁻¹*w*d*c):=by field_simp
 exact w _ _ _

#print axioms Oscillates.daily
#print axioms Studded.interp

def risen(t:ℝ):ℂ:=t*I
abbrev coin (t:ℝ):ℂ:=disc (risen t)
lemma coin_day(t:ℝ):coin t=Real.exp (-t):= disc_deep t
lemma coin_inj:Injective coin:= fun x y t=> neg_injective (Real.exp_injective
     (Complex.ofReal_injective ((coin_day x).symm.trans (t.trans (coin_day y)))))

def levy (n:ℕ)(i:Rank n):ℝ:=i.val
def raised (n:ℕ)(i:Rank n):ℂ:=risen (levy n i)
lemma raised_disc (n:ℕ):Injective (disc ∘ raised n):=
 coin_inj.comp (Nat.cast_injective.comp Fin.val_injective)

def Grows (n:ℕ)(g:ℝ→ℂ):Prop:=
 ∃p:ℂ[X],p.natDegree≤n+n ∧ ∀t,(coin t)^n * g t=p.eval (coin t)
lemma Grows.of_raised {g:ℝ→ℂ}
 (e:∀t,g t=∑ i, hoops r (raised r) (risen t) i * g (levy r i)): Grows r g:=by
 let h:Rank r→ℂ:= coin ∘ levy r
 let V:=fun i:Rank r=>h i ^ r * g (levy r i)
 let J:= Lagrange.interpolate Finset.univ h V
 have d:=Lagrange.degree_interpolate_lt V
    (v:=h) (s:=Finset.univ) ((raised_disc r).injOn)
 refine ⟨J,?_,fun t=>?_⟩
 · -- degrees

   by_cases b:J=0
   · rw [b]; simp
   exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt b).mpr (by simpa [J,Rank] using d))
 rw [e t, Finset.mul_sum, show J= Lagrange.interpolate _ h V from rfl,Lagrange.interpolate_apply,eval_finsetSum]
 refine Finset.sum_congr rfl fun i _=>?_
 rw [eval_mul,eval_C,hoops]
 have k:coin t ^ r ≠ 0:=pow_ne_zero _ (disc_ne _)
 change (coin t ^ r)*((coin t ^ r)⁻¹ * h i ^ r * _ * g (levy r i))=
    h i ^ r * g (levy r i) * Polynomial.eval (coin t) (Lagrange.basis Finset.univ (disc ∘ (raised r)) i)
 rw [←mul_assoc,←mul_assoc,←mul_assoc,mul_inv_cancel₀ k]
 unfold coin; ring



-- local equality extends among rates, via polynomial

lemma Grows.matches {g h:ℝ→ℂ}{m n:ℕ}(a:Grows m g)(b:Grows n h)
 (e:Set.Infinite {t|g t=h t}):g=h:=by
 obtain ⟨p,_,u⟩:=a; obtain ⟨q,_,v⟩:=b
 let P:= X ^ n * p
 let Q:= X ^ m * q
 have r(t):P.eval (coin t)=coin t ^ (n+m) * g t :=by dsimp only [P];rw [eval_mul,eval_pow,eval_X,←u,pow_add,mul_assoc]
                                                          --
 have s (t):Q.eval (coin t)=coin t ^ (n+m) * h t :=by dsimp only [Q];rw [eval_mul,eval_pow,eval_X,←v,Nat.add_comm,pow_add,mul_assoc]
 have y:P=Q:=Polynomial.eq_of_infinite_eval_eq _ _
    ((e.image coin_inj.injOn).mono (by
      rintro _ ⟨t,j,rfl⟩
      change Polynomial.eval _ _=_
      rw [r,s,(show g t=h t from j)]))
 funext t
 apply mul_left_cancel₀ (pow_ne_zero (n+m) (disc_ne (risen t)))
 rw [←r,←s,y]
#print axioms Grows.matches
