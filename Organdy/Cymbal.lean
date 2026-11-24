import Organdy.Vellum
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra



section
variable {I:Type*} [LinearOrder I] [Fintype I]
lemma trace_spends (A:Op I):‖Matrix.trace A‖ ≤ motes A := by
 exact (norm_sum_le ..).trans (sum_le_sum fun i _=>single_le_sum (f:=fun j=> ‖A i j‖) (fun _ _=>norm_nonneg _) (mem_univ i))
lemma dg_spends (A:Op I):‖dg A‖ ≤ motes A:=by
 refine (norm_sum_le ..).trans (sum_le_sum fun i _=>(norm_sum_le ..).trans (sum_le_sum fun j _=>?_))
 rw [norm_smul]; refine mul_le_of_le_one_right (norm_nonneg _) ((norm_mul_le ..).trans ?_)
 have ht:‖takeF j‖ ≤ 1 := by unfold takeF; rw [norm_star]; exact Graph.cost_u _
 exact (mul_le_mul (Graph.cost_u i) ht (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
lemma preJ_spends (T:Finset I) (A:Op I):‖preJ (cutM T) A‖ ≤ 2*motes A:=by
 have hi:motes (cutM T*A)≤ motes A:=by
    refine sum_le_sum (fun i _=>sum_le_sum fun j _=>?_)
    rw [cutM, Matrix.diagonal_mul]; split; rw [one_mul]; rw [zero_mul,norm_zero]; exact norm_nonneg _
 have he:motes (cutM T*A*(1-cutM T))≤ motes A:=by
    rw [←dim_cut]; refine le_trans (sum_le_sum (fun i _=>sum_le_sum fun j _=>?_)) hi
    rw [show cutM Tᶜ=Matrix.diagonal _ from rfl,Matrix.mul_diagonal];split; rw [mul_one]; rw [mul_zero,norm_zero]; exact norm_nonneg _

 rw [two_mul]
 exact (norm_add_le ..).trans (add_le_add
    (by rw [norm_smul,norm_one,mul_one]; exact (trace_spends _).trans hi)
    ((dg_spends _).trans he))

lemma preJ_zero(A:Op I):preJ A 0=0:=by simp [preJ,dg,dyad]
lemma preJ_turn (A X:Op I) (u:UNI I) (p:twist u A=A): twist (quantU u) (preJ A X)=preJ A (twist u X):=by
 have hi := trace_twist u (A*X); rw [map_mul,p] at hi
 unfold preJ
 rw [map_add,twist_scalar,map_one,dg_cov,map_mul,map_mul,map_sub,map_one,p,hi]

lemma sector_aboard {b:Bool} {X:FC I}{S T: Finset I}(p:Sector S b X)(v:S⊆T):Sector T b X:=by
 induction p with
 |zero=> exact Sector.zero _
 |one=> exact Sector.one
 |up i h=>exact Sector.up i (v h)
 |down i h=>exact Sector.down i (v h)
 |mul _ _ ih ih'=>exact ih.mul ih'
 |add _ _ ih ih'=>exact ih.add ih'
 |scale _ u ih=>exact ih.scale u

end
variable {N:Side}{F G: Mark N}{U V:phy N}{a b:ℝ}{S T:Support (More N)}
local notation "Ω"=>Single N
open Reed (Fine)

/-- Pointwise witness down to every inserted field. 'Real' means physical,
not a complex phase choice. -/
structure Cymbal (S:Support (More N))(F:Mark N) (U:phy N) (a:ℝ) :Prop where
 realc : AtSupport false S F
 suprem(y:Fields N) : ‖F y‖ ≤ a
 color : covariant F
 spare(x:Orbit N) : Sector (modesIn N S) false (U x)

 first(U V W: Pane N): F (U,V)=F (U,W)
 tie(x:Orbit N)(V:Pane N):
    acts (star (F (x.1,V))) (mateK N)=acts (star (U x)) (mateK N)
namespace Cymbal
variable (h:Cymbal S F U a) (i:Cymbal S G V b)
lemma raise (v:S⊆T)(h:Cymbal S F U a): Cymbal T F U a :=
 {h with
    realc :=h.realc.mono v
    spare :=fun x=>sector_aboard (h.spare x) (modes_monotone v)}

lemma elastic (v:a≤b)(h:Cymbal S F U a):Cymbal S F U b:=
 {h with suprem := fun x=>(h.suprem x).trans v}

include h
lemma resize (w:ℂ): Cymbal S (w • F) (w • U) (‖w‖*a):=by
 refine ⟨h.realc.smulM w,fun x=>?_,fun g x=>?_,fun x=>(h.spare x).scale w,fun x y z=>congrArg (w•·) (h.first x y z),fun x y=>?_⟩
 · rw [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (h.suprem x) (norm_nonneg _)
 · simp only [Pi.smul_apply,twist_scalar,h.color g x]
 · simp only [Pi.smul_apply,star_smul,act_smul,h.tie]

lemma negative : Cymbal S (-F) (-U) a:=by simpa using h.resize (-1)
include i
lemma plus : Cymbal S (F+G) (U+V) (a+b):=by

 refine ⟨h.realc.addM i.realc,fun x=>(norm_add_le ..).trans (add_le_add (h.suprem x) (i.suprem x)),fun g x=>?_,fun x=>(h.spare x).add (i.spare x),fun x y z=>?_,fun x y=>?_⟩
 · simp only [Pi.add_apply,map_add,h.color g x,i.color g x]
 · simp only [Pi.add_apply,h.first x y z,i.first x y z]
 · simp only [Pi.add_apply,star_add,act_add,h.tie,i.tie]
lemma less : Cymbal S (F-G) (U-V) (a+b):=by rw [sub_eq_add_neg,sub_eq_add_neg]; exact h.plus i.negative
omit h i
lemma none : Cymbal S 0 0 0 :=
 ⟨.zeroM,fun x=>by simp,fun g x=> by simp,fun _=>.zero _,fun _ _ _=>rfl,fun _ _=>rfl⟩
lemma sum {ι:Type*} (t:Finset ι)(F:ι→ Mark N)(G:ι→ phy N)(a:ι→ℝ)(v:∀ i∈t,Cymbal S (F i) (G i) (a i)):
 Cymbal S (∑ i∈t,F i) (∑ i∈t,G i) (∑ i∈t,a i):=by
 induction t using Finset.induction_on with
 |empty=>simp only [sum_empty]; exact none
 |insert i t hi ih=>
    simp only [sum_insert hi]; exact (v _ (mem_insert_self ..)).plus (ih (fun j k=>v _ (mem_insert_of_mem k)))
end Cymbal

def clef (A:Pane N→ Op Ω):Mark N:=fun x=> Matrix.trace (A x.1) • 1
def harp (A:Pane N→ Op Ω):Mark N:=fun x=>preJ (tickA N) (A x.1)

variable {Jα:Pane N→ Op (Single N)}
lemma slatClef (e:∀ x,U x=Matrix.trace (Jα x.1) • 1)(h:Slat S Jα b) : Cymbal S (clef Jα) U b:=by
 have hb(x:Fields N):‖clef Jα x‖ ≤ b:=by
    rw [clef,norm_smul,norm_one,mul_one]
    exact (trace_spends _).trans (h.quick x.1)
 have t : Continuous (fun M:Op Ω=> Matrix.trace M • (1:FC Ω)):= by fun_prop
 exact ⟨⟨⟨t.measurable.comp (h.bright.comp measurable_fst), b,hb⟩,fun x y w _=>congrArg (fun z:Op Ω=>Matrix.trace z • 1) (h.local_ _ _ w),fun x=>Fine.one.scale _⟩,
   hb,fun g x=>by simp only [clef, simultaneous,Prod.map,h.move,trace_twist,twist_scalar,map_one],fun x=>e x ▸ Sector.one.scale _,fun _ _ _=> rfl,fun x V=>by rw [e x];rfl⟩

lemma slatHarp (e:∀ x,U x=dg (Jα x.1))(h:Slat S Jα b): Cymbal S (harp Jα) U (2*b):=by
 have hb(x:Fields N):‖harp Jα x‖ ≤ 2*b:=by
    unfold harp;rw [touchP]
    exact (preJ_spends ..).trans (mul_le_mul_of_nonneg_left (h.quick _) (by norm_num))
 have t: Continuous (preJ (tickA N)):=by unfold preJ; fun_prop
 refine ⟨⟨⟨t.measurable.comp (h.bright.comp measurable_fst),2*b,hb⟩,fun x y w _=>congrArg (preJ _) (h.local_ _ _ w),?_⟩,hb,?_,?_,fun _ _ _=>rfl,?_⟩

 · intro x; rw [harp,touchP]; exact inSector _ _ _ (h.core _)
 · intro g x
   change preJ _ (Jα (Lattice.gauge g x.1))=twist _ (preJ _ _)
   rw [h.move, preJ_turn _ _ _ (Cascade.tick_g _)]
 · intro x;rw [e]; exact pair_charge (h.core _)
 · intro x y;rw [e]; exact (bra_eq _ (by rw [touchP]; exact cutM_idp _) _ (tickB N)).symm

lemma Cymbal.weave (f:Cymbal S F U a)(g:Cymbal T G V b)(ha:0≤a) (p:Disjoint S T)
    : Cymbal (S∪T) (F*G) (U*V) (a*b):=by
 let u := f.raise (subset_union_left (s₂:=T))
 let v := g.raise (subset_union_right (s₁:=S))
 refine ⟨u.realc.mulM v.realc,fun x=>
 (norm_mul_le ..).trans (mul_le_mul (f.suprem x) (g.suprem x) (norm_nonneg _) ha),
 fun t x=>by simp only [Pi.mul_apply,map_mul,f.color t x,g.color t x],
 fun x=>(u.spare x).mul (v.spare x),
 fun x y z=>by simp only [Pi.mul_apply, f.first x y z,g.first x y z],
 ?_⟩
 intro x y; let z:Fields N:=(x.1,y)
 have d:Disjoint (modesIn N T) (modesIn N S):=
    disjoint_left.mpr (fun i t l=> disjoint_left.mp p ((modes_at S i).mp l) ((modes_at T i).mp t))
 have r: G z * U x= U x * G z:=by simpa [Sector.grainB] using
   (Reed.Fine.sector (g.realc.allV z)).apart (f.spare x) d
 have q: V x * U x = U x * V x:=by simpa [Sector.grainB] using (g.spare x).apart (f.spare x) d
 change acts (star (F z*G z)) (mateK N)=acts (star (U x * V x)) (mateK N)

 have w: acts (star (F z)) (mateK N)=acts (star (U x)) (mateK N):=f.tie x y
 have t: acts (star (G z)) (mateK N)=acts (star (V x)) (mateK N):=g.tie x y
 rw [star_mul,act_mul,w,←act_mul,←star_mul, ←r,←q,star_mul,star_mul,act_mul,act_mul,t]
end YM.CF.Organdy
