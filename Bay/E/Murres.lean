import Bay.E.Cabin
import Bay.D.Barque

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


namespace Silk
open Buffered Lifted D StressExchange


open scoped YM.CF.Buffered
variable {o:Cover}{b:ℕ}{t d L:ℝ}
local notation "AΩ"=>Band o b

structure SilkPay(o:Cover)(b:ℕ)(t d L:ℝ)(f:LinksC→ℂ):Prop where
 meas:Measurable f
 flat(x):‖f x‖≤L
 seated(x y):Agrees (Band o b) x y→ f x=f y
 sleepy(x):¬landingC b o t x→f x=0
 low{x y}:landingC b o t x→landingC b o t y→
    dist (f x) (f y)≤L*(((nubs (Band o b)).card * dist (inlet (Band o b) x) (inlet (Band o b) y))/|d|)

lemma launch {ι:Type}[Fintype ι]{F:ℕ→ι→LinksC→ℂ}(h:∀n i,SilkPay o b t d L (F n i)) :
 ∃ φ:ℕ→ℕ,StrictMono φ∧∃f:ι→LinksC→ℂ,∀i,SilkPay o b t d L (f i)∧TendstoUniformly (fun n=>F (φ n) i) (f i) atTop:=by
 classical
 by_cases hn:Nonempty ι
 swap
 · haveI:IsEmpty ι:=not_nonempty_iff.mp hn
   exact ⟨id,strictMono_id,fun _ _=>0, isEmptyElim⟩ -- binder
 have l:0≤L:=(norm_nonneg _).trans ((h 0 (Classical.choice hn)).flat 1)

 have v(i):Fleet (fun n=>F n i):=
   shipFleet (D:=setOf (landingC b o t)) (inlet AΩ) (inlet_bounds _) _
     ⟨L,fun n=>(h n i).flat⟩
     ⟨L*(nubs AΩ).card / |d|+1,by positivity,fun x a y z n=>le_trans ((h n i).low a z) (by
         rw[←mul_div_assoc,←mul_assoc, mul_div_right_comm]
         exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg)⟩
     (fun n=>(h n i).sleepy)
 let V(n)(x:ι×LinksC):=F n x.1 x.2
 have w:Fleet V:= by
   refine ⟨⟨L,fun n x=>(h n x.1).flat x.2⟩,fun ε p=>?_⟩
   choose A a using fun i=>(v i).2 ε p
   refine ⟨univ.biUnion fun i=>(A i).image (Prod.mk i),?_⟩
   rintro ⟨i,x⟩
   rcases a i x with u|u
   · exact Or.inl u
   obtain ⟨y,t,g⟩:=u
   exact Or.inr ⟨(i,y),mem_biUnion.mpr ⟨i,mem_univ _,mem_image_of_mem _ t⟩,g⟩
 obtain ⟨φ,W,g,u⟩:= w.launch
 refine ⟨φ,W,fun i x=>g (i,x),fun i=>?_⟩
 let x(k):= u.tendsto_at (i,k)

 refine ⟨⟨measurable_of_tendsto_metrizable (f:=fun n=>F (φ n) i) (fun n=>(h (φ n) i).meas) (tendsto_pi_nhds.mpr x),
    fun k=>le_of_tendsto ((x k).norm) (Eventually.of_forall fun j=>(h _ i).flat _),?_,?_,?_⟩,?_⟩
 · intro k r t
   exact tendsto_nhds_unique_of_eventuallyEq (x k) (x r) (Eventually.of_forall fun j=>(h _ i).seated _ _ t)
 · intro k r
   exact tendsto_nhds_unique_of_eventuallyEq (x k) tendsto_const_nhds (Eventually.of_forall fun j=>(h _ i).sleepy _ r)
 · intro k r s t
   exact le_of_tendsto ((x k).dist (x r)) (Eventually.of_forall fun j=>(h _ i).low s t)
 exact Metric.tendstoUniformly_iff.mpr fun ε p=>(Metric.tendstoUniformly_iff.mp u ε p).mono fun n h x=>h (i,x)

variable {p:BudgetPoint}{N:Side}{k:ℕ}{X:Pane N→Op (Single N)}

structure Spool (N:Side)(χ:Op (Single N)→ℂ):Prop where
 seethe:Continuous χ
 temper x y:χ x-χ y=χ (x-y)
 curls(x):‖χ x‖≤cork x

lemma spool{χ:Op (Single N)→ℂ}(w:Spool N χ)
 (h:Awning X p (wrap _ o) k L d) (hb:p.B=b)(ht:p.threshold=t) (k0:k≤b) (e:AtEase AΩ N):
   SilkPay o b t d L (χ∘X∘craft AΩ N):=by
 subst b t
 let B:=Band o p.B
 let c:=craft B N
 have l:0≤L:=le_trans ((norm_nonneg _).trans (w.curls _)) (h.shadeU 1)
 have H(x): c x∈setAwning p (wrap _ o)↔landingC p.B o p.threshold x:= craft_tick e p.threshold x
 refine ⟨w.seethe.measurable.comp (h.meas.comp craft_cont.measurable),fun x=>(w.curls _).trans (h.shadeU (c x)),fun x y g=> congrArg χ (h.dep _ _ (craft_support e g)),?_,?_⟩

 · intro x u
   change χ (X (c x))=_
   rw [h.fence (c x) (mt (H x).mp u)]
   have y:= w.temper 0 0
   simpa using y.symm
 intro x y u z
 rw[dist_eq_norm,Function.comp_apply,Function.comp_apply,Function.comp_apply, w.temper]
 apply le_trans (le_trans (w.curls _) (h.shadeL ((H _).mpr u) ((H _).mpr z)))
 exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (fare_inlet (k0.trans (Nat.le_add_left ..)) e x y) (abs_nonneg _)) l
lemma spoolZ:Spool N Matrix.trace:= ⟨by fun_prop, by simp, cork_tc⟩
lemma spoolDiag:Spool N (diagonal N):= by


 refine ⟨by unfold diagonal;fun_prop,fun x y=>?_,fun x=> ?_⟩
 · rw[diagonal,diagonal,diagonal, mul_sub,Matrix.trace_sub]
 apply le_trans (cork_tc _)
 rw [touchP,cutM,cork,cork]
 simp_rw [Matrix.diagonal_mul]
 apply sum_le_sum; intro i _
 apply sum_le_sum; intro j _
 split <;> simp
lemma spoolTax {S:Finset Cover}(i j:Beam S):Spool N (fun x=>tariff N x i j):=by
 refine ⟨by unfold tariff;fun_prop,fun x y=>?_,fun x=>?_⟩
 · rw[tariff,tariff,tariff,Matrix.sub_apply,mul_sub]
 have h(k:Beam S):‖ap N k‖=1:=by 
   have t: ‖ap N k‖^2=1:=by rw [sq,←norm_mul,show ap N k * ap N k=1 from Rush.fee_one _,norm_one] -- ap
   nlinarith [norm_nonneg (ap N k)]
 rw [tariff,norm_mul,norm_mul,h,h,mul_one,one_mul]
 exact (norm_entry ..).trans (cork_norm x)
end YM.CF.Bay.Silk
