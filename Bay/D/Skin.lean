import Bay.D.Myrtle
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

variable {N:Side}{p:BudgetPoint}{o:Seat N}{k:ℕ}{r L:ℝ}
-- Raw scalar receipt. Need not require centered. Mask off zero and
-- f0=0 for pressure qualification kept separately.
structure Skin (p:BudgetPoint)(o:Seat N)(k:ℕ)(r L:ℝ)
     (f:Pane N→ℂ)(c:ℂ)(A:Icey (Cella (More N))):Prop where
 rake:Rake (Lagoon k o) L A
 small(v):v∈setAwning p o → ‖f v-c‖≤L*p.threshold^2
 turns{v y}: v∈setAwning p o→‖y‖≤r →
      Agrees (roost k o) v (represent y)→
          ‖f v - (c+splash A (brine y))‖≤L*‖y‖^3
variable {f:Pane N→ℂ}{c:ℂ}{A:Icey (Cella (More N))}
namespace Skin
lemma more(s:Skin p o k r L f c A){l:ℝ}(h:L≤l): Skin p o k r l f c A:=
 ⟨s.rake.widen le_rfl h,fun v t=>(s.small v t).trans (mul_le_mul_of_nonneg_right h (sq_nonneg _)),
    fun u z j=>(s.turns u z j).trans (mul_le_mul_of_nonneg_right h (by positivity))⟩
lemma zero:Skin p o k r 0 (0:Pane N→ℂ) 0 0:=by constructor; exact Rake.zero; simp; simp [splash]

variable {M:ℝ}{g:Pane N→ℂ}{d:ℂ}{B:Icey (Cella (More N))}
lemma add(s:Skin p o k r L f c A)(q:Skin p o k r M g d B):Skin p o k r (L+M) (f+g) (c+d) (A+B):=by
 refine ⟨s.rake.add q.rake,fun v t=>?_,fun{v y} t h j=>?_⟩
 · rw[Pi.add_apply,add_sub_add_comm,add_mul];exact (norm_add_le ..).trans (add_le_add (s.small v t) (q.small v t))
 rw[Pi.add_apply,splash,swirl_add, add_add_add_comm c d,add_sub_add_comm,add_mul]
 exact (norm_add_le ..).trans (add_le_add (s.turns t h j) (q.turns t h j))

lemma scale(s:Skin p o k r L f c A)(a:ℂ):
    Skin p o k r (‖a‖*L) (a • f) (a*c) (a • A):=by
 refine ⟨s.rake.shake a,fun v t=>?_,fun {v y} t h j=>?_⟩
 · rw[Pi.smul_apply,smul_eq_mul,←mul_sub,norm_mul,mul_assoc]
   exact mul_le_mul_of_nonneg_left (s.small v t) (norm_nonneg _)
 rw[Pi.smul_apply,smul_eq_mul,splash,swirl_scalar,←mul_add,←mul_sub,norm_mul,mul_assoc]
 exact mul_le_mul_of_nonneg_left (s.turns t h j) (norm_nonneg _)

lemma spin(s:Skin p o k r L f c A):
    Skin p o k r L (fun v=>star (f v)) (star c) (fun i j=>star (A i j)):=by
 refine ⟨⟨fun i j=>congrArg star (s.rake.sym ..),?_,?_⟩,fun v t=>?_, ?_⟩

 -- order goals?
 · intro i j h;exact s.rake.fits _ _ (by contrapose! h;simp [h])
 · simp only [swill,norm_star];exact s.rake.fee
 · rw[←star_sub,norm_star]; exact s.small v t
 intro v y t h j
 have he:splash (fun i j=>star (A i j)) (brine y)=star (splash A (brine y)):=by simp only [splash,swirl,star_sum,star_smul,star_trivial] -- tune
 rw[he,←star_add,←star_sub,norm_star];exact s.turns t h j

lemma fin{I:Type*}(F:I→Pane N→ℂ)(C:I→ℂ)(B:I→Icey (Cella (More N)))(g:I→ℝ)(u:Finset I)
   (h:∀i∈u,Skin p o k r (g i) (F i) (C i) (B i)):
   Skin p o k r (∑i∈u,g i) (∑i∈u,F i) (∑i∈u,C i) (∑i∈u,B i):=by
 induction u using Finset.induction_on with
 | empty=> simp only [sum_empty];exact zero
 | @insert i u b ih=> simp only [sum_insert b]; exact (h _ (mem_insert_self ..)).add (ih fun j p=>h _ (mem_insert_of_mem p))
end Skin

-- Measurability, full support, gauge, and modulus purchased for later limits.
-- May retain larger constant here (though still volume-independent).
structure Vinyl (p:BudgetPoint)(o:Seat N)(k:ℕ)(d L:ℝ)(f:Pane N→ℂ):Prop where
 nonneg:0≤L
 small(v):‖f v‖≤L
 meas:Measurable f
 hue(g:Seat N→E)(x:Pane N):f (Lattice.gauge g x)=f x
 localV:LocalOn (roost (12+p.B) o) f
 fence(v):v∉setAwning p o→f v=0
 polish{x y}: x∈setAwning p o→y∈setAwning p o→
    ‖f x-f y‖≤L*(fare (roost k o) (profile x) (profile y)/|d|)
namespace Vinyl
variable {d:ℝ}
lemma more(s:Vinyl p o k d L f){l:ℝ}(h:L≤l): Vinyl p o k d l f:=
 {s with small:=fun v=>(s.small v).trans h,nonneg:=s.nonneg.trans h, polish:=fun u v=>(s.polish u v).trans (mul_le_mul_of_nonneg_right h (div_nonneg (fare_t ..) (abs_nonneg _)))}
lemma zero : Vinyl p o k d 0 (0:Pane N→ℂ):=by
 refine ⟨le_rfl,?_,measurable_const,fun _ _=>rfl,fun _ _ _=>rfl,fun _ _=>rfl,?_⟩<;>simp
lemma scale(s:Vinyl p o k d L f)(a:ℂ): Vinyl p o k d (‖a‖*L) (a • f):=by
 refine ⟨mul_nonneg (norm_nonneg _) s.nonneg,fun v=>?_,?_,?_,?_,?_,?_⟩
 · rw[Pi.smul_apply, norm_smul]; exact mul_le_mul_of_nonneg_left (s.small v) (norm_nonneg _)
 · exact measurable_const.smul s.meas
 · exact fun _ _=>congrArg (a • ·) (s.hue ..)
 · exact fun _ _ h=>congrArg (a • ·) (s.localV _ _ h)
 · intro v h; rw[Pi.smul_apply,s.fence v h,smul_zero]
 intro x y u v;rw[Pi.smul_apply,Pi.smul_apply,←smul_sub,norm_smul,mul_assoc]
 exact mul_le_mul_of_nonneg_left (s.polish u v) (norm_nonneg _)

lemma add(s:Vinyl p o k d L f){g:Pane N→ℂ}{M:ℝ}(t:Vinyl p o k d M g): Vinyl p o k d (L+M) (f+g):=by
 refine ⟨add_nonneg s.nonneg t.nonneg,fun v=>(norm_add_le ..).trans (add_le_add (s.small v) (t.small v)),s.meas.add t.meas,
   fun _ _=>congrArg₂ (·+·) (s.hue ..) (t.hue ..),fun _ _ h=>congrArg₂ (·+·) (s.localV _ _ h) (t.localV _ _ h),?_,?_⟩
 · intro v w; rw[Pi.add_apply,s.fence v w,t.fence v w,zero_add]
 intro x y u v; rw[Pi.add_apply,Pi.add_apply,add_sub_add_comm,add_mul]
 exact (norm_add_le ..).trans (add_le_add (s.polish u v) (t.polish u v))
lemma fin{I:Type*}(F:I→Pane N→ℂ)(g:I→ℝ)(u:Finset I)
   (h:∀i∈u,Vinyl p o k d (g i) (F i)):
   Vinyl p o k d (∑i∈u,g i) (∑i∈u,F i):=by
 induction u using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact zero
 | @insert i u b ih=> simp only [sum_insert b]; exact (h _ (mem_insert_self ..)).add (ih fun j p=>h _ (mem_insert_of_mem p))
lemma spin(s:Vinyl p o k d L f): Vinyl p o k d L (fun v=>star (f v)):=by
 refine ⟨s.nonneg,fun v=>le_trans (norm_star _).le (s.small v),continuous_star.measurable.comp s.meas,fun _ _=>congrArg star (s.hue ..),

   fun _ _ h=>congrArg star (s.localV _ _ h),fun v w=>by simp[s.fence v w], ?_⟩
 intro x y u v; rw[←star_sub,norm_star];exact s.polish u v

open scoped Buffered in -- for MeasurableSpace? Need type inst weird.
lemma color{V:Pane N→ Op (Single N)}(h:Awning V p o k L d):
    Vinyl p o k d L (Matrix.trace ∘ V):=by 
 refine ⟨(norm_nonneg _).trans ((cork_tc _).trans (h.shadeU (1:Pane N))),fun v=>(cork_tc _).trans (h.shadeU v),?_, ?_,fun _ _ t=>congrArg Matrix.trace (h.dep _ _ t), fun v e=>by simp[h.fence v e],?_⟩
 · have ht: Continuous (Matrix.trace: Op (Single N)→ℂ):=by fun_prop
   exact ht.measurable.comp h.meas
 · intro g x; rw[Function.comp_apply,h.fixed];change Matrix.trace (((tradew _ g).val * V x) * star _)=_
   rw [Matrix.trace_mul_cycle,(tradew _ g).property.1,one_mul];rfl
 · intro x y u v;dsimp only [Function.comp_apply];rw[←Matrix.trace_sub]
   exact (cork_tc ..).trans (h.shadeL u v)
end Vinyl

end YM.CF.Bay.D
