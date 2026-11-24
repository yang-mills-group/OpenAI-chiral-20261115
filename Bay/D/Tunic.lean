import YM.SU5.Thin.Woods.Fabric
import Bay.D.Ivora
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Buffered.Afterglow

variable {N:Side}
abbrev soar (F:Pane N→ℝ)(z:ℂ)(r:Kite (More N))(V:Pane N):ℂ:=
    1+z*(F (r.swirl V):ℂ)
structure Tunic(o d:Seat N)(F:Pane N→ℝ)(z:ℂ)(A:Fabric N):Prop where
 fit: AtSupport false A.S A.x
 fit₁:A.o∈A.S
 fit₂:A.b∈A.S
 role: ∃ (r:Kite (More N))(y:ℂ), (y=z∨y=star z) ∧
   A.x=Hookah.chalkOp (soar F y r) ∧ r.rise o=A.o ∧ r.rise d=A.b

variable {o d:Seat N}{F:Pane N→ℝ} {z:ℂ}{A:Fabric N}

lemma Tunic.rev (h:Tunic o d F z A)(i:Axis)(u:ℤ): Tunic o d F z (A.twistL i u):=by
 let q: Kite (More N):= ⟨Signed.mirror i, wrap (More N) (2 • (u • step i))⟩
 obtain ⟨r,y,v,hx,hy,hz⟩:=h.role
 refine ⟨h.fit.refl i u,mem_image_of_mem _ h.fit₁,mem_image_of_mem _ h.fit₂,q*r,star y,v.elim (fun e=>Or.inr (by rw [e])) (fun e=>Or.inl (by rw [e,star_star])),?_,?_,?_⟩
 

 · funext V
   change reflMark i u A.x V=_
   rw [hx]
   unfold reflMark Hookah.chalkOp soar
   rw[theta_smul,theta_one,show (reflFields i u V).1=q.swirl V.1 from rfl,Kite.union,star_add,star_one,star_mul',Complex.star_def,Complex.conj_ofReal]
 · rw [Kite.r_mul,hy];rfl
 rw[Kite.r_mul,hz];rfl

lemma blaze (z:ℂ): ‖1+z‖≤ Real.exp (z.re+‖z‖^2):=by
 apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (Real.exp_pos _).le
 rw [←Real.exp_nat_mul, Complex.sq_norm]
 refine le_trans ?_ (Real.add_one_le_exp _)
 rw [Complex.normSq_add, Complex.sq_norm]
 simp
 nlinarith only [Complex.normSq_nonneg z]

lemma Tunic.limit (h:Tunic o d F z A)(M:ℝ)(f:∀x, ‖F x‖≤M)(x:Fields N):
 ‖A.x x‖ ≤ 1+‖z‖*M:=by
 obtain ⟨r,y,v,hx,_⟩:=h.role
 have hv: ‖y‖=‖z‖:=by rcases v with e|e <;>simp[e]
 rw[hx,Hookah.chalkOp,norm_smul,norm_one,mul_one]
 apply (norm_add_le ..).trans
 rw [norm_one,norm_mul,hv,Complex.norm_real]
 gcongr; apply f

variable {J:List (Fabric N)}

lemma Tunic.count (h:Sylvan (Tunic o d F z) 0 J)(M:ℝ)
  (hm:0≤M)(f:∀x, ‖F x‖≤M)(x:Fields N):
 ‖buffet J x‖ ≤ (1+‖z‖*M)^J.length:=by
 induction J with
 | nil=>rw [buffet_empty,List.length_nil,pow_zero,Pi.one_apply,norm_one]
 | cons i L ih=>
   have v:Sylvan (Tunic o d F z) 0 L:= ⟨fun i j=>h.core i (List.mem_cons_of_mem _ j), (List.pairwise_cons.mp h.annex).2⟩
   rw [buffet_more,List.length_cons,pow_succ',Pi.mul_apply]
   exact (norm_mul_le ..).trans
     (mul_le_mul ((h.core i List.mem_cons_self).limit M f x) (ih v) (norm_nonneg _) (by positivity))

lemma tunic_prod (x:Fields N) (f:Fin J.length→ℂ)
 (p:∀i,(J.get i).x x=f i • 1): buffet J x = (∏ i, f i) •1 :=by
 induction J with
 | nil=> simp [buffet]
 | cons i J ih=>
   let t:Fin J.length→ℂ:=fun j=>f j.succ
   have h:i.x x=f 0 • 1:=p 0
   rw [buffet_more, Pi.mul_apply, ih t (fun j=>p j.succ),h,Algebra.smul_mul_assoc,one_mul,smul_smul, show ∏ j,f j = _ from Fin.prod_univ_succ f]

lemma Tunic.invoice (h:Sylvan (Tunic o d F z) 0 J)(M:ℝ)
 (f:∀x, ‖F x‖≤M):

 ∃ (gs:Fin J.length→Kite (More N)) (c:Pane N→ℂ),
 Packed gs o d ∧ buffet J =Hookah.chalkOp c ∧
 ∀x, ‖c x‖≤Real.exp (z.re * gusts gs F x + J.length * (‖z‖^2*M^2)):=by
 let I:=Fin J.length
 have s (i:I):=h.core (J.get i) (List.get_mem ..)
 choose gs y v p e₁ e₂ using fun i=> (s i).role
 let c(x:Pane N):= ∏ i, soar F (y i) (gs i) x
 have ti(b:Seat N)(t:∀i:I,(gs i).rise b∈(J.get i).S): Injective (fun i=>(gs i).rise b):=by
   have hne {i j:I}(l:i<j):(gs i).rise b≠(gs j).rise b:=by
     intro y
     have hh:= h.annex.rel_get_of_lt l _ (t i) _ (t j)
     rw [y,separation_self] at hh; omega
   intro i j x; exact le_antisymm (le_of_not_gt fun l=>hne l x.symm) (le_of_not_gt fun l=>hne l x)
 refine ⟨gs,c,⟨ti _ (fun i=>by rw[e₁];exact (s i).fit₁),ti _ (fun i=>by rw[e₂];exact (s i).fit₂)⟩,funext fun x=>tunic_prod x _ (fun i=>by rw [p]),?_⟩

 intro x
 have e(i:I): ‖soar F (y i) (gs i) x‖≤Real.exp (z.re * F ((gs i).swirl x) + ‖z‖^2*M^2):=by

    refine (blaze _).trans (Real.exp_monotone ?_)
    have hy: (y i).re=z.re ∧ ‖y i‖=‖z‖:=by rcases v i with w|w <;>simp [w]
    rw [Complex.mul_re, Complex.ofReal_re,hy.1, Complex.ofReal_im,mul_zero,sub_zero,norm_mul,hy.2,mul_pow,Complex.norm_real]
    gcongr; exact f _
 unfold c;rw [norm_prod]
 refine le_trans (prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>e i)) ?_
 rw[←Real.exp_sum,sum_add_distrib,←mul_sum,sum_const, card_univ]
 exact le_of_eq (by rw[nsmul_eq_mul,Fintype.card_fin];rfl)
end YM.CF.Bay.D
