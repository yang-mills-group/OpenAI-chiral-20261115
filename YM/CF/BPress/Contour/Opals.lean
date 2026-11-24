import YM.CF.BPress.Contour.Orbit
/-! Component price. Boost station ball. Non-cyclic requests to ambient functions.Separate. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Contour
open RG Wilson Push.SectorMeasure Env Finset MeasureTheory Function Palmer Ledger Branch
open scoped Classical Topology BigOperators
variable {Y I:Type}{Φ:Y→ Type*}[DecidableEq I][Fintype I][Fintype Y][DecidableEq Y][∀ i,MeasurableSpace (Φ i)][∀ i,Nonempty (Φ i)][Nonempty Y]
variable {Z:Y→ Finset Y}{T:I→Finset Y} {D:(Seal Y)→ I→ (∀ i,Φ i)→ℂ}{G:Seal Y→(∀ i,Φ i)→ℂ}
variable {μ ν:∀ i, Measure (Φ i)}[∀ i,IsProbabilityMeasure (μ i)][∀ i,IsFiniteMeasure (ν i)] {q:ℝ}{a:I→ℝ}
variable (Z a) (q)
def quartz (S: Finset Y):= if Core Z S then q^S.card else 0
def beads : Seal Y⊕ I→ℝ:= Sum.elim (quartz Z q) a -- tune order
variable {Z a q}(H:Cabin Z T D G) (p:∀ i,i∈ Z i)
structure SumP (Z:Y→Finset Y)(T:I→ Finset Y)(D:(Seal Y)→ I→ (∀ i,Φ i)→ℂ)(G:Seal Y→(∀ i,Φ i)→ℂ)(μ ν:∀ i,Measure (Φ i))(q:ℝ)(a:I→ℝ) : Prop extends Cabin Z T D G where
 boost:0≤q
 fromSea(Q)(h:Core Z Q): ∫ i,‖G Q i‖∂century μ ν Q ≤ quartz Z q Q
 fromEarth(E i x):‖D E i x‖ ≤ a i
variable (C:SumP Z T D G μ ν q a)
namespace SumP
include p C
lemma motes {K:Finset (Seal Y)}(h:Fleet Z K): ∫ i,‖buoy G K i‖∂century μ ν (floor K) ≤ ∏ i∈ K,quartz Z q i:=by
 induction K using Finset.induction_on with
 |empty=> simp [floor,buoy]
 |insert i K e ih=>
    have he:= h.subs (subset_insert i K); have hb:= h.1 i (mem_insert_self ..); have ht: floor (insert i K)=i∪floor K:= biUnion_insert; have hp: ∀ x,‖buoy G (insert i K) x‖=‖G i x‖*‖buoy G K x‖:=fun x=> by rw [buoy,prod_insert e,norm_mul]
    have hQ: Disjoint (station Z i) (berth Z K):=by
      refine disjoint_left.mpr fun a q v=>?_ ; obtain ⟨j,v,w⟩:= mem_biUnion.mp v; exact disjoint_left.mp (h.2 (mem_insert_self i K) (mem_insert_of_mem v) (ne_of_mem_of_not_mem v e).symm) q w
    simp_rw [hp,ht]; rw [autumn μ ν i (floor K) (pins i p) (Cabin.port p) (C.extent i hb).norm (C.toCabin.know_boat he).norm hQ, prod_insert e]; refine mul_le_mul (C.fromSea i hb) (ih he) (integral_nonneg (fun _=>norm_nonneg _)) ((integral_nonneg (fun _=>norm_nonneg _)).trans (C.fromSea i hb))
omit p in
lemma home(i:I): 0≤a i:= (norm_nonneg _).trans (C.fromEarth ∅ i (Classical.arbitrary _))
omit p in
lemma bead (x:Seal Y⊕I):0≤ beads Z q a x:=by -- tune
 cases x with|inl i=> exact ite_nonneg (pow_nonneg C.boost _) le_rfl|inr i=> exact C.home i
lemma bill_cost {K:Finset (Seal Y)}(g:Fleet Z K)(J:Finset I) : ‖channel D G μ ν K J‖ ≤ (∏ i∈K,quartz Z q i)*∏ i∈J,a i:=by
 let E:= floor K; let w(i:I):=a i; have he:= C.toCabin.sailsC g J; have hp(v:∀ i,Φ i):‖lance D G K J v‖≤ ‖buoy G K v‖ *∏ i∈ J,a i:=by unfold lance; rw [norm_mul, norm_prod (s:=J)]; exact mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=> C.fromEarth ..)) (norm_nonneg _)
 apply (norm_integral_le_integral_norm _).trans; let U:= century μ ν E; refine (integral_mono (μ:=U) (integrableX he U).norm ((integrableX (C.toCabin.sail g) U).norm.mul_const _) hp).trans ?_; rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right (C.motes p g) (prod_nonneg (fun i _=>C.home i))
lemma pile (P: Finset (Seal Y⊕I)): ‖line Z D G μ ν P‖ ≤ ∏ i∈ P,beads Z q a i:=by
 unfold line; split; next h=> rw [prod_sum_eq_prod_toLeft_mul_prod_toRight]; exact C.bill_cost p h _
 rw [norm_zero]; exact prod_nonneg (fun j _=>C.bead j)
end SumP
section bound
variable {F: Branch.Field Y} {m:Lattice.Side}{u γ x:ℝ}
lemma bill_core (g:evenT F Z)(Q:Sole F m)(P:Stakes m u γ)(hq:0≤q)(hw:Cash Z (fun _=>q) (u+u) γ): Cash (lead Z) (quartz Z q) u (till_cost m γ):=by
 have he:= spark_pay g Q P hw; have hp(S:Seal Y): (∏ _ ∈ S,q)=q^S.card:= by simp
 simp_rw [hp] at he; refine ⟨fun i=> he.1 _,?_⟩; intro x; convert he.hits x using 1; ext T; by_cases g: Core Z T <;> simp [score,lead,g,quartz, (show Core Z T=Spark Z T from rfl)|>.symm,station] -- tune spark
lemma cash_beads (p:Cash (lead Z) (quartz Z q) u γ)(t:Cash T a u x): Cash (chart Z T) (beads Z q a) u (γ+x):=by
 refine ⟨fun i=> Sum.rec (motive:=fun i=>0≤ beads Z q a i) (fun _=>p.pos _) (fun _=>t.pos _) i,fun i=> ⟨fun j=> ?_, (hasSum_fintype _).summable,?_⟩ ⟩; · cases j with|inr j=> exact (t.hits i).1 j|inl j=> exact (p.hits i).1 j
 have hp:= (p.hits i).2.2; have he:= (t.hits i).2.2; rw [tsum_fintype] at *; rw [Fintype.sum_sum_type]; exact add_le_add hp he
end bound
end YM.CF.BPress.Contour
