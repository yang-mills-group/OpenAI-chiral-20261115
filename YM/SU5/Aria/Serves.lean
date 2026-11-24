import YM.SU5.Aria.Marquee
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric Casting
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "R"=> ruler P.par.block
local notation "ρ"=> P.width
local notation "ξ"=> P.laysM
local notation "Μ"=> timeMesh P.par
variable (i n:ℕ)(D:P.Apron)
local notation "S₀"=> P.shifts j
-- move of Pose unchanged aperture; actual rectangular bodies
noncomputable def plenumShift (n:ℕ)(j:Axis)(w:ℤ): Vantage:= Pi.single j (bell (timeMesh P.par) n w)
lemma step_shield (p:ℤ)(a:Cover)(x:RSpace) (b:x∈ Tapestry.shield Λ P.width n (a+ (R*p)•step j)):
     x-2 • (P.plenumShift n j p)∈ Tapestry.shield Λ P.width n a:=by
 intro z; have h:=b z
 by_cases e:z=j
 · subst z; let t:=precisionAt Λ n; change |t*x j-(((a+_•_ :Cover) j:ℤ):ℝ)|≤_ at h; have he:=Apron.distance_mark P n p; change _= (↑(R*p):ℝ) / t at he; rw [eq_div_iff (positiveScale Λ n).ne'] at he
   rw [Pi.sub_apply,Pi.smul_apply,nsmul_eq_mul,Nat.cast_ofNat,plenumShift,Pi.single_eq_same]
   rw [SlabMark.moves,if_pos rfl,Int.cast_add,← he] at h; simp only [_root_.mul_sub]; simpa only [t,mul_comm (precisionAt Λ n) (2*bell Μ n p),sub_add_eq_sub_sub_swap] using h -- tune
 simp only [plenumShift,Pi.sub_apply,Pi.smul_apply,Pi.single_eq_of_ne e,smul_zero,sub_zero]
 rw [SlabMark.moves,if_neg e] at h; exact h
lemma step_poses (p q:Vantage)(x:RSpace)(g:x - 2 • q∈ D.scenery P p): x∈D.scenery P (p+q):=by
 intro i; have hw:=g i; change |(x-2•q:Vantage) i-2*p i|≤_ at hw; rw [Pi.sub_apply,Pi.smul_apply,nsmul_eq_mul,Nat.cast_ofNat] at hw; convert hw using 1; rw [Pi.add_apply,_root_.mul_add,sub_add_eq_sub_sub_swap]
lemma step_print (p:ℤ) (z:Vantage) (O:Finset Cover) (h:printedHere Λ P.width n O (D.scenery P z)) : printedHere Λ P.width n (plow K j p O) (D.scenery P (z+P.plenumShift n j p)):= by
 intro i t u v; obtain ⟨j,v',rfl⟩:= plow_stays K j p O t; exact step_poses P D _ _ u (h j v' (P.step_shield _ n p j u v)) -- shadow
lemma step_enclosure (p:ℤ)(z:Vantage)(f:P.Test)(h:f∈ keep Λ P.width n (K) true (D.scenery P z)) : P.shifts j p f∈ keep Λ P.width n K true (D.scenery P (z+P.plenumShift n j p)):=by
 obtain ⟨B,u,t⟩:=h; exact ⟨_,P.shifts_support j p _ u,P.step_print j n D p z B t⟩
variable (p:Cover)
def jettyT (L: List Axis):Vantage := (L.map (fun i=> P.plenumShift n i (p i))).sum
lemma jettyT_full : P.jettyT n p Vacancy.ordinate = ξ (P.vtile n p):=by
 funext k
 have ht(L:List Axis)(v:L.Nodup): P.jettyT n p L k=if k∈L then bell Μ n (p k) else 0:=by
    induction L with
    | nil=> simp [jettyT]
    | cons i L ih=>
      obtain ⟨v,h⟩:= List.nodup_cons.mp v; rw [show P.jettyT n p (i::L)=P.plenumShift n i (p i)+P.jettyT n p L from rfl, Pi.add_apply,ih h]; unfold plenumShift; by_cases e:k=i
      · subst i; simp [v]
      simp [e]
 rw [ht Vacancy.ordinate Vacancy.ordinate_one,if_pos (Vacancy.ordinates k)]; rfl
lemma jetty_inside (L:List Axis)(f:P.Test)(z:Vantage)(h:f∈keep Λ P.width n K true (D.scenery P z)): P.cruise L p f∈ keep Λ P.width n K true (D.scenery P (z+P.jettyT n p L)):=by
 induction L with
 | nil=> simpa [cruise,jettyT] using h
 | cons i L t=> rw [P.cruise_step,AlgHom.comp_apply,show P.jettyT n p (i::L)=P.jettyT n p L+P.plenumShift n i (p i) from add_comm ..,←add_assoc]; exact P.step_enclosure i n D (p i) _ _ t -- `rfl` add_comm left def
variable (Q:P.Register)
include Q
lemma calibrated_location (a:D.s≤n) : P.chartAll p (D.full P n)∈keep Λ P.width n K true (D.scenery P (P.laysM (P.vtile n p))):=by
 have he:=P.jetty_inside n D p Vacancy.ordinate (D.full P n) 0 (D.throughMark P n a Q); rwa [P.jettyT_full,zero_add] at he
omit Q
section union
variable {I : Type*} (A:I→P.Apron)(q:I→ Vantage)(L:List I)(r:I → Cover)
def neighborhoods : Set RSpace:=⋃ i∈{i|i∈L}, (A i).scenery P (q i)
include Q
lemma slots_home {O:Set RSpace}(h:∀i∈L,(A i).s≤n)(b:∀ i∈ L,(A i).scenery P (ξ (P.vtile n (r i)))⊆ O):
    P.fullScroll n A r L∈keep Λ P.width n K true O:=by
 induction L with
 | nil=> exact Subalgebra.one_mem _
 | cons i l t=>exact (keep Λ P.width n K true O).mul_mem (rooms Λ P.width n K true _ (b _ (List.Mem.head ..)) (P.calibrated_location n (A i) (r i) Q (h i (List.Mem.head ..)))) (t (fun i v=> h i (List.Mem.tail _ v)) (fun i v=> b i (List.Mem.tail _ v)))
lemma purse_home (h:∀ i∈L,(A i).s≤n): let S:=P.neighborhoods A (P.laysM ∘ (P.vtile n ∘ r)) L; P.fullScroll n A r L∈keep Λ P.width n K true S∧ P.fullScroll n A r L∈enclave K:=⟨P.slots_home n Q A L r h (fun i y=>Set.subset_biUnion_of_mem (show _∈{i|i∈L} from y) (u:=fun i=>(A i).scenery P (ξ (P.vtile n (r i))))) ,P.full_scroll_effect n A r L⟩ -- arguments
omit Q
lemma pay_places (q:Vantage) : IsCompact (D.scenery P q):=by
 let s (i:Axis):= Set.Icc (2*q i-2*D.realWidth P i) (2*q i+2*D.realWidth P i); convert isCompact_pi_infinite (s:=s) (fun i=> isCompact_Icc) using 1; ext x; simp only [Apron.scenery,Set.mem_setOf_eq]; simp_rw [abs_le]; refine forall_congr' fun i=> ?_; simp only [s,Set.mem_Icc]; constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith -- api
lemma pay_porches : IsCompact (P.neighborhoods A q L):= by
 classical
 unfold neighborhoods; rw [show {i | i ∈ L} = (L.toFinset:Set I) from (by ext; simp)]; exact L.toFinset.finite_toSet.isCompact_biUnion fun i _=> pay_places ..
lemma separated_keeps (k l:I) (h:P.resignY j A q k<P.porchY j A q l): Disjoint ((A k).scenery P (q k)) ((A l).scenery P (q l)):=by
 apply Set.disjoint_left.mpr; intro x d p; specialize d j; specialize p j; unfold resignY porchY Apron.time_panel Apron.time_edge at h; obtain ⟨d,y⟩:=abs_le.mp d; obtain ⟨e,f⟩:=abs_le.mp p; linarith
end union
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
