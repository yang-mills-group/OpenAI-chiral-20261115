import YM.CF.DPress.Rise.Tune
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open Cad Mercer Room Push.AbsoluteSums Larch Ione Trees Py Wray Kay DPress.Fees.Moral
variable {N:Side}{P:BudgetPoint}{h:ℝ}{D:Docket P}{I:blazeK N}{q:ℕ}{F:Cusp N}
variable {μ:Aura N→ℝ}{J:Rinse (Seat N) (Copy N)}{B:Orbit N→Aura N→FC (Dwell N)}
namespace Docket
variable (Y:D.Account I)(p:D.Chip μ)(t:1≤h) (f:bill P q h I F)(u:Stax.Pitch P h q J μ B)
local notation "ΦC"=> (RiseB P F J)
local notation "ΖC"=> (RemE P F J)
local notation "Se"=> EmptyD (RiseB P F J)
abbrev Colony (P:BudgetPoint) (F:Cusp N)(J:Rinse (Seat N) (Copy N))(Z:RegBudget N): Pax N:= Nu P (EmptyD (RiseB P F J)) (EmptyD F) Z
abbrev Xhat (D:Docket P)(I:blazeK N)(μ:Aura N→ℝ):= urnL I+urnL (Sco I μ)+D.z • (μ+urnL (ScoL I μ))
local notation "Ψ"=> D.Xhat I μ
include Y p t f u
lemma accepts (i:Aura N):0 ≤ Ψ i∧ I i ∅ ≤Ψ i ∧ (Sco I μ) i ∅ ≤ Ψ i ∧ μ i + ScoL I μ i ∅ ≤ D.z⁻¹ * Ψ i:=by
 obtain ⟨q,w⟩:= (ΨH Y p t f u).1 i ∅ (empty_subset _); have he:= Y.nn i ∅ (empty_subset _); have hg:= q.merit.wage (zero_le_one.trans t); have hi:= w.merit.wage (zero_le_one.trans t); have hd:0 ≤ D.z*(μ i+(ScoL I μ i ∅)):= mul_nonneg D.zpos.le (add_nonneg (p.1 i) hi)
 have ht : Ψ i = I i ∅+ Sco I μ i ∅+ D.z*(μ i+(ScoL I μ i ∅)):= rfl; rw [le_inv_mul_iff₀ D.zpos,ht]; constructor; linarith; constructor; linarith; constructor<;>linarith -- syntax conjunct
lemma things : Ready Palot.stern P.B Ψ (P.supportExponent+1+1) D.γ wΨ (degreePrice P.B D.γ wΨ):=by
 refine ready_T (P:=P) D.gpos uΨ D.qlimit (fun i=> (accepts Y p t f u i).1) fun i=>?_ ; rw [Xhat,tall_add,tall_add,tall_s,tall_add]; exact (add_le_add (add_le_add (D.ℓtime I Y i) (gas_h Y p t f u i).1) (mul_le_mul_of_nonneg_left (add_le_add ((tall_m _ p.1 (show ρL P ≤ wu P+2 from ℓε.trans (le_add_of_nonneg_right (by norm_num))) i).trans (p.2 i)) (coronaC Y p t f u i).1) D.zpos.le)).trans D.stint
lemma cloud(i:Aura N): Medal P i.val ∅ (F i ∅) h (Ψ i) ∧ Medal P i.val ∅ (ΦC i ∅) h (Ψ i) ∧ Medal P i.val ∅ (ΦC i ∅-F i ∅) h (D.z⁻¹*Ψ i):=by
 obtain ⟨_,Hk,uF,c⟩:= accepts Y p t f u i; obtain ⟨g,v⟩:= (ΨH Y p t f u).1 i ∅ (empty_subset _); refine ⟨(f i ∅ (empty_subset _)).merit.big Hk,g.merit.big uF,?_⟩; have hv:= (Stax.aptL F I f J μ u t i ∅ (empty_subset _)).merit; rw [δWeight,if_pos rfl] at hv; rw [show ΦC i ∅-F i ∅=birthL J i ∅+ΖC i ∅ from ?_ ]; exact (hv.plus v.merit).big c; unfold RiseB Stax.lamp RemE; abel
variable (Z:RegBudget N)(hz:∀ (i:Aura N)(p:Orbit N),birthL J i ∅ p= orbV Z i p)
include hz
lemma strongN : PactF P (P.supportExponent+1+1) h (Colony P F J Z) D.Nr:=by
 let Z1:=urnL (ScoL I μ); have k:= things Y p t f u; let f':Pax N:=EmptyD ΦC; let E:= EmptyD F; let Q0:= EmptyD ΖC
 have he(i:Aura N)(p:Orbit N): f' i p= E i p+orbV Z i p+ Q0 i p:=by rw [← hz]; rfl
 have hv(i:Aura N): Medal P i.val ∅ (Q0 i) h (Z1 i):= ((ΨH Y p t f u).1 i ∅ (empty_subset _)).2.merit
 have hp':= α_G Z D.z D.zpos k t (fun i=>(cloud Y p t f u i).2.1) (fun i=>(cloud Y p t f u i).1) (fun i=>(cloud Y p t f u i).2.2) hv he; exact ⟨rentD D.z Z1 Ψ,hp',fun i=> cost_p Z D.z D.zpos k t (fun i=>(cloud Y p t f u i).2.1) (fun i=>(cloud Y p t f u i).1) (fun i=>(cloud Y p t f u i).2.2) hv he i ((tall_m _ (fun i=>hv i|>.wage (zero_le_one.trans t)) (tiny2 (P:=P)) i).trans (coronaC Y p t f u i).1)⟩ -- tune.
end Docket
end YM.CF.Sour.Heath
