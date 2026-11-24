import Velour.Escutcheon.Acre
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Motifs
open Set Filter Function Mink Mink.Lorentz Real
open scoped Topology BigOperators InnerProductSpace
open _root_.YM.OS.Semigroup (scroll)
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
def lobes:=Subgroup.closure {g:Lorentz | ∃b t,scroll b t=g}
lemma ornate(b:SpaceAxis)(t:ℝ):scroll b t∈lobes:=Subgroup.subset_closure ⟨b,t,rfl⟩
lemma detach (x:E4)(e:x∈inside)(b:SpaceAxis):
 ∃s:ℝ,(let y:=spatial (act (scroll b s) x); 
         y b=0 ∧ ∀i,i≠b→y i=spatial x i):= by
   let v:= (Ray.fromAxis b)
   have a:0<time x:=(strict_self _).mp e |>.1
   let t:= -(v.along x)/(time x)
   have y:|v.along x|<time x:=lt_of_le_of_lt (v.along_le x) e
   have r:|t|<1:=by
      simp only [t,abs_div,abs_neg,abs_of_pos a]
      exact (div_lt_one a).mpr y
   refine ⟨artanh t,?_,fun i h=>?_⟩
   · let d:= artanh t
     have q:=v.newProjection d x
     have j: sinh d=t*cosh d :=
       (div_eq_iff (cosh_pos _).ne').mp ((tanh_eq_sinh_div_cosh ..).symm.trans
         (tanh_artanh (show t∈Ioo (-1) 1 from abs_lt.mp r)))
     change v.shift d x b.castSucc=0
     rw [← Ray.onAxis b, q, j]
     dsimp only [t]
     field_simp
     ring   -- use v.along identity nondefeq!
   change spatial (v.shift (artanh t) x) i=_
   rw [v.newSpace]
   simp [v,Ray.fromAxis,h]

lemma all_time (g:Lorentz):
 ∃k∈lobes,Pin (k*g):=by
   let x:=basis timeAxis
   have e:x∈inside:=by simp [x,inside]
   have t(m:Finset SpaceAxis):∃k∈lobes,
           ∀i∈m,spatial (act (k*g) x) i=0:= by
       induction m using Finset.induction with
       | empty=>exact ⟨1,lobes.one_mem,by simp⟩
       | insert i f he ih=>
         obtain ⟨k,e',v⟩:=ih
         obtain ⟨r,d⟩:=detach _ ((stays (k*g) _).mpr e) i
         refine ⟨scroll i r*k,lobes.mul_mem (ornate i r) e',?_⟩
         rw [mul_assoc,act_mul]
         intro j h
         by_cases w:j=i
         · exact w.symm ▸ d.1
         exact (d.2 _ w).trans (v _ ((Finset.mem_insert.mp h).resolve_left w))
   obtain ⟨k,p,a⟩:=t Finset.univ
   have l:(spatial (act (k*g) x))=0:=PiLp.ext fun i=>a i (Finset.mem_univ _)
   refine ⟨k,p, ext_by (l.trans roll_space.symm) ?_⟩
   rw [roll_clock]
   have y:=keeps (k*g) x
   unfold Mink.m at y; rw [l, show spatial x=0 from roll_space,show time x=1 from roll_clock] at y
   nlinarith [(strict_self _).mp ((stays (k*g) _).mpr e)|>.1]


lemma filigree(g:Lorentz):∃k∈lobes,∃Q:Lorentz,Pin Q ∧ g=Q*k:=by
 obtain ⟨k,p,t⟩:=all_time g⁻¹
 refine ⟨k,p,(k*g⁻¹)⁻¹,(congrArg _ t.symm).trans (starts _ _),by group⟩

lemma expires(x:E4)(e:x∈spacelike):
 ∃g:Lorentz, time (act g x)=0:=by
 let y:=spatial x
 have v: |time x|<‖y‖:= (lateral _).mp e
 have a:0<‖y‖:=lt_of_le_of_lt (abs_nonneg _) v
 let D:Ray:=⟨‖y‖⁻¹ • y,by
    rw [norm_smul, norm_of_nonneg (inv_nonneg.mpr a.le)]
    exact inv_mul_cancel₀ a.ne'⟩
 have h:D.along x=‖y‖:=by
    change inner ℝ y (_ • y)=‖y‖
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
 let t:= -(time x)/‖y‖
 have r:|t|<1:=(by rw [show |t|=|time x|/‖y‖ by rw [abs_div, abs_neg, abs_of_pos a]]
                   exact (div_lt_one a).mpr v)
 refine ⟨D.boost (artanh t),?_⟩
 have j: sinh (artanh t)=t*cosh (artanh t):=
   (div_eq_iff (cosh_pos _).ne').mp ((tanh_eq_sinh_div_cosh ..).symm.trans
      (tanh_artanh (abs_lt.mp r)))
 rw [Ray.boost_at,D.newClock,h,j]; dsimp only [t]; field_simp
 ring


theorem aside(x:E4)(e:x∈spacelike):
 ∃g∈lobes,∃b:SpaceAxis,
   |time (act g x)| < |act g x b.castSucc|:=by
 obtain ⟨m,i⟩:=expires x e
 obtain ⟨k,p,Q,u,rfl⟩:=filigree m
 have j: time (act k x)=0:= ( (pin_iff Q).mp u _).symm.trans i
 refine ⟨k,p,?_⟩
 rw [j,abs_zero]
 by_contra! l
 have w:spatial (act k x)=0:=PiLp.ext fun i=> (abs_eq_zero.mp
      (le_antisymm (l i) (abs_nonneg _)))
 have a:0<‖spatial (act k x)‖:= (abs_nonneg _).trans_lt
   ((lateral _).mp (by unfold spacelike; rw [mem_setOf,keeps];exact e))
 rw [w,norm_zero] at a; exact (lt_irrefl _ a)
#print axioms filigree
#print axioms aside


open YM.Damask
/-- No hypothesis in several boost parameters along an *arbitrary* sandwiched factor! -/
def Pattern(f:Lorentz→ℂ):Prop:=∀(g:Lorentz)(b:SpaceAxis),∃d:ℕ,
 Grows d (fun t=> f (scroll b t*g))

variable {f g:Lorentz→ℂ}(p:Pattern f)(r:Pattern g)
open scoped Topology
open Filter
include p r
lemma sustained (k:Lorentz)(e:f =ᶠ[𝓝 k] g)(b:SpaceAxis)(v:ℝ):
 f =ᶠ[𝓝 (scroll b v*k)] g:=by
 let P:= {m:Lorentz|f=ᶠ[𝓝 m] g}
 have t:P ∈ 𝓝 k:= (eventually_eventually_nhds (p:=fun y=> f y=g y)).mpr e
 have hh:∀y∈P,f (scroll b v*y)=g (scroll b v*y):=by
   intro y i
   obtain ⟨m,i'⟩:=p y b
   obtain ⟨l,j⟩:=r y b
   refine congrFun (i'.matches j ?_) v
   have h:ContinuousAt (fun t=>scroll b t * y) (0:ℝ):=
        (Ray.continuousBoost (Ray.fromAxis b)).continuousAt.mul continuousAt_const
   have u:{t | f (scroll b t*y)=g (scroll b t*y)}∈ 𝓝 0:=
        h.eventually (p:=fun w=>f w=g w) (by change f =ᶠ[𝓝 (scroll b 0*y)] g; rw [scroll, Ray.boost_start,one_mul]; exact i)
   exact infinite_of_mem_nhds 0 u
 let Q:=scroll b v
 have c:Continuous (fun y:Lorentz => Q⁻¹ * y):=continuous_const.mul continuous_id
 have w(x:Lorentz):Q⁻¹*(Q*x)=x:=by group


 have z:Tendsto (fun y=>Q⁻¹*y) (𝓝 (Q*k)) (𝓝 k):=by simpa [w] using c.tendsto (Q*k)
 filter_upwards [z.eventually t] with y h
 simpa [Q] using hh _ h

theorem enthroned(k:Lorentz)(v:k∈lobes)(e:f =ᶠ[𝓝 k] g): f 1=g 1:=by
 have w(h:Lorentz)(d:h∈lobes): f =ᶠ[𝓝 (h*k)] g:=by
    refine Subgroup.closure_induction_left (s:={g:Lorentz|∃b t,scroll b t=g})
      (p:= fun x _=> f =ᶠ[𝓝 (x*k)] g) (by simpa using e) ?_ ?_ d
    · rintro _ ⟨b,t,rfl⟩ y _ eq
      rw [mul_assoc]; exact sustained p r _ eq b t
    rintro _ ⟨b,t,rfl⟩ y _ eq
    rw [mul_assoc, scroll, Ray.boost_neg]
    exact sustained p r _ eq b (-t)
 simpa using (w _ (lobes.inv_mem v)).self_of_nhds
#print axioms enthroned
