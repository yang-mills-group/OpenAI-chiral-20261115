import ZecaSprig
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open Lattice Regis.Head.Brecht Regis.Circuit Stationary

/-- analytic box halfwidth δ<preset 1/4 in normalized UV units. -/
def cask (R:ℝ): Set ℂ:= {z|‖z‖<R∧|z.im|<1/4}
lemma cask_open(R:ℝ):IsOpen (cask R):=
 IsOpen.inter (isOpen_lt continuous_norm continuous_const)
      (isOpen_lt (f:=fun z:ℂ=> |z.im|) (by fun_prop) continuous_const)
lemma cask_sub {R:ℝ}{x y:ℂ} (p:x∈cask R)(q:y∈cask R):
 x-y∈weatherBand ∧ |(x-y).im|≤1/2 ∧ ‖x-y‖≤R+R:=by
 unfold cask at *
 simp only [mem_setOf_eq] at *
 have a:=abs_lt.mp p.2; have z:=abs_lt.mp q.2
 have e:=Complex.sub_im x y
 exact ⟨show |(x-y).im|<1 by rw [e];exact abs_lt.mpr ⟨by linarith,by linarith⟩,
      by rw [e]; exact abs_le.mpr ⟨by linarith,by linarith⟩,
      (norm_sub_le x y).trans (add_le_add p.1.le q.1.le)⟩

variable (colA:PlaqAxes→ℝ)(G:Gauge)
lemma faun_tar (b:Axis) (t β:ℝ)(p:1≤t)(R:ℝ):
 ∃D:ℝ, Tar (cask R) D (fun z w=>faun colA G b t β (z-w)):=by
 obtain ⟨D,t0⟩:=bearing colA G b t β p (R+R)
 have a:= fauna_d colA G b t β p

 refine ⟨D,
    fun w e=> a.comp (differentiableOn_id.sub_const w)
                      (fun z f=>(cask_sub f e).1),
    fun z e=> a.comp ((differentiableOn_const z).sub differentiableOn_id)
                      (fun w f=>(cask_sub e f).1),
    fun z w e f=>t0 _ (cask_sub e f).2.1 (cask_sub e f).2.2⟩
-- finite sets of data, uniform bound.
structure Spot where
 b: Axis
 t:ℝ
 β:ℝ

lemma cask_meet{σ:Type*}[Finite σ]
 (A:σ→Spot) (h:∀i,1≤ (A i).t)(R:ℝ):
 ∃D>0,∀i,Tar (cask R) D
    (fun z w=>faun colA G (A i).b (A i).t (A i).β (z-w)):=by
 choose d l using fun i=>faun_tar colA G (A i).b (A i).t (A i).β (h i) R
 obtain ⟨D,y⟩: BddAbove (Set.range d):=(Set.finite_range _).bddAbove
 exact ⟨max 1 D, zero_lt_one.trans_le (le_max_left ..),
   fun i=>⟨(l i).hol,(l i).hol',fun z w v u=>
           ((l i).ub z w v u).trans ((y (Set.mem_range_self i)).trans (le_max_right ..))⟩⟩
#print axioms cask_meet
