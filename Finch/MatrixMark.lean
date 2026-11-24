import Finch.Value
import YM.CF.Buffered.Probes
import YM.SU5.Exchange.Stack.Manor

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill Buffered StressExchange Window

variable {N:Side}{P:SOp N}{o:Seat N}{a b c d v s t:ℝ}{p:BudgetPoint}{k r:ℕ}
structure NativeMark (S:Sa N)(X: Evaluation N) (v:ℝ):Prop where
 foot : AtSupport false S (toMark X)
 moves : covariant (toMark X)
 sup (V:Pane N) : ‖X V‖ ≤ v

namespace NativeMark
variable {S:Sa N} {X Y:Evaluation N}
lemma enlarge (h:NativeMark S X v)(T:Sa N)(u:S⊆T): NativeMark T X v:= {h with foot:= h.foot.mono u}
lemma zero : NativeMark S 0 0:= ⟨AtSupport.zeroM,fun _ _=>(map_zero _).symm,fun _=>norm_zero.le⟩
lemma add (h:NativeMark S X v)(k:NativeMark S Y c): NativeMark S (X+Y) (v+c):=by
 refine ⟨h.foot.addM k.foot,fun g x=>?_,fun U=> (norm_add_le ..).trans (add_le_add (h.sup U) (k.sup U))⟩
 change toMark X _ + toMark Y _ = twist _ (toMark X x+ toMark Y x); rw [map_add,←h.moves g x, ←k.moves g x]
lemma smul (h:NativeMark S X v)(t:ℂ): NativeMark S (t • X) (‖t‖*v):=by
 refine ⟨h.foot.smulM t,fun g x=>?_,fun U=>?_⟩
 · change t • toMark X _ = twist _ (t • toMark X x); rw [twist_scalar, ←h.moves g x]
 rw [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (h.sup _) (norm_nonneg _)
lemma sub (h:NativeMark S X v)(k:NativeMark S Y c): NativeMark S (X-Y) (v+c):=by simpa [sub_eq_add_neg] using h.add (k.smul (-1))
lemma sum {ι:Type*}(s:Finset ι)(f:ι→Evaluation N)(c:ι→ℝ)(k:∀ i∈s,NativeMark S (f i) (c i)):
    NativeMark S (∑ i∈s,f i) (∑ i∈s,c i):=by
 induction s using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; exact NativeMark.zero
 | insert i s h ih=> rw [sum_insert h,sum_insert h]; exact (k i (mem_insert_self ..)).add (ih fun _ g=>k _ (mem_insert_of_mem g))
end NativeMark

def spurMark (A:Loom N)(p:BudgetPoint)(o:Site N)(P:SOp N) : Evaluation N:=
 fun V : Pane N=> preJ (tickA N) (markMatrix A p (node o) P V)
def inkCost (A:Loom N)(p:BudgetPoint)(o:Site N)(P:SOp N) (V:Pane N):ℂ:= Matrix.trace (markMatrix A p (node o) P V)
def gaugeOnlyMark (A:Loom N)(p:BudgetPoint)(o:Site N)(P:SOp N): Evaluation N:=
 fun V=> inkCost A p o P V • 1
abbrev markZone(p:BudgetPoint)(o:Site N) : Sa N:= halo (p.B+12) {node o}
lemma preJA_equiv (t: Seat N→SU.E)(M:Op (Single N)): twist (quantU (tradew N t)) (preJ (tickA N) M)=preJ (tickA N) (twist (tradew N t) M):=by
 unfold preJ; rw [map_add,twist_scalar,map_one,dg_cov,map_mul,map_sub,map_one,map_mul,Cascade.tick_g]
 rw [←show twist (tradew N t) (tickA N * M) = tickA N* twist (tradew N t) M from by rw [map_mul,Cascade.tick_g],trace_twist]

variable {A:Scree.Loom N}{O:Site N}(h:Roof N b d r A)(u:0<d)(X:Trunk (node O) P k a v d)(l:k+r ≤ p.B)(f:p.threshold ≤ b)(z:0≤a)
include h u X l f z
lemma ticket_ink : NativeMark (markZone p O) (gaugeOnlyMark A p O P) v:=by
 let V:=markMatrix A p (node O) P
 let F: Op (Single N)→FC (Single N):=fun P=> Matrix.trace P • (1:FC _); have e:Continuous F:= (continuous_id.matrix_trace).smul continuous_const
 refine ⟨AtSupport.fromEval _ (Girt.pole_w V F e (ink_envelope h u X z p)) (fun i j g=>congrArg F (ink_local h u X l f _ _ g)) (fun _=>Reed.Fine.one.scale _),?_,?_⟩
 · intro t U; unfold toMark simultaneous gaugeOnlyMark; simp only [Prod.map_fst]; rw [inkCost,ink_gauge h u X l f,trace_twist,twist_scalar,map_one]; rfl
 intro U; unfold gaugeOnlyMark inkCost; rw [norm_smul,norm_one,mul_one]; exact (trace_book _).trans (book_ink h u X _ _ z)
lemma ticket_spur : NativeMark (markZone p O) (spurMark A p O P) (2*v):=by
 let V:=markMatrix A p (node O) P
 let F: Op (Single N)→FC (Single N):=preJ (tickA N); have e:Continuous F:= (((continuous_const.mul continuous_id).matrix_trace).smul continuous_const).add ((Girt.dgCT (Single N)).comp ((continuous_const.mul continuous_id).mul continuous_const))
 refine ⟨AtSupport.fromEval _ (Girt.pole_w V F e (ink_envelope h u X z p)) (fun i j g=>congrArg F (ink_local h u X l f _ _ g)) (fun x=>?_),?_,?_⟩
 · unfold spurMark; rw [touchP]; exact inSector _ _ _ (ink_spots h u X _ _ _ (Corona.halo_mono (by omega) le_rfl))
 · intro t U; unfold toMark simultaneous spurMark; simp only [Prod.map_fst]; rw [ink_gauge h u X l f,preJA_equiv]
 intro U; unfold spurMark; rw [touchP]; exact (pre_book _ _).trans (mul_le_mul_of_nonneg_left (book_ink h u X _ _ z) (by positivity))

/-- (128), unscaled carrier. Uses only first field. -/
def finchWardMark (A:Loom N)(p:BudgetPoint)(O:Site N)(J:Axis→SOp N)(P:SOp N)(m:ℕ):Evaluation N:=
  gaugeOnlyMark A p O P + ∑ i:Axis, (spurMark A p (O+m • step i) (co_Ψ (O+m • step i) O (J i))-spurMark A p (O-m • step i) (co_Ψ (O-m • step i) O (J i)))

-- support includes also windmill contact Region (price layout of next step)
abbrev wardZone (p:BudgetPoint)(O:Site N)(m:ℕ): Sa N:= halo (24*m+p.B+12) {node O}
omit h u X l f z in
lemma zone_fit (x O : Site N)(m:ℕ)(p:BudgetPoint)(v:separation O x≤ m) : markZone p x ⊆ wardZone p O m:=by
 intro j b; obtain ⟨y,e,t⟩:=halo_spec.mp b
 apply halo_spec.mpr; refine ⟨node O,mem_singleton_self _,(separation_triangle _ y j).trans ?_⟩; rw [mem_singleton.mp e,Hove.ζdist]; rw [mem_singleton.mp e] at t; omega
abbrev wardValue (v:ℝ):ℝ:=v+4*(2*(Tenant.quota^2*v)+2*(Tenant.quota^2*v))
lemma ticket_ward (J:Axis→SOp N)(t:∀ i:Axis, Trunk (node O) (J i) k a v d)(m:ℕ) :
    NativeMark (wardZone p O m) (finchWardMark A p O J P m) (wardValue v):=by
 let V:= wardZone p O m
 have hx(i:Axis)(x:Site N)(g:separation O x≤ m): NativeMark V (spurMark A p x (co_Ψ x O (J i))) (2*(Tenant.quota^2*v)):= by
    have ht:= (t i).travels (taxiPlus (x-O)); rw [platforms,add_sub_cancel] at ht; exact (ticket_spur h u ht l f z).enlarge V (zone_fit x O _ _ g)
 let D:=2 * (Tenant.quota^2*v) +2*(Tenant.quota^2*v)
 have hp(i:Axis): NativeMark V (spurMark A p (O+m • step i) _-spurMark A p (O-m • step i) _) D:= (hx i _ (stopBeam O i m).1).sub (hx i _ (stopBeam O i m).2)
 have he: wardValue v= v+ ∑ _i:Axis,D:=by simp [wardValue,D,nsmul_eq_mul,Axis]; ring
 rw [he]; exact ((ticket_ink h u X l f z).enlarge V (zone_fit O O _ _ (by simp))).add (NativeMark.sum univ _ _ (fun i _=> hp i))
end YM.CF.Swell
