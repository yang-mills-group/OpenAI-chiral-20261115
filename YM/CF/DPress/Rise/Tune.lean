import YM.CF.DPress.Rise.Tapi
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
-- Receipt for B:Cusp; loaf.Gauge.Field
abbrev flame(P:BudgetPoint)(q:ℕ)(F:Cusp N):Prop:= ∀ X:Aura N,∀ D⊆X.val,Stax.Lives P q X D (F X D)
abbrev bill (P:BudgetPoint)(q:ℕ)(h:ℝ)(I:blazeK N)(F:Cusp N):Prop := ∀ X:Aura N,∀ D⊆X.val,Fray P h q X D (F X D) (I X D)
abbrev EmptyD(F:Cusp N):Pax N:=fun X=> F X ∅
lemma accountB0 (D:Docket P) (f: flame P q F)(v:1≤h)(u:PactF P (wu P) h (EmptyD F) D.Sh)(p:XL P h (wu P) F D.SF): ∃ I:blazeK N,D.Account I ∧ bill P q h I F:=by
 obtain ⟨F0,pA,w⟩:=u; obtain ⟨W,u,g⟩:= (vouchers P h _ v _).1 p; let U(X:Aura N)(C:Support (More N)):= if C.Nonempty then W X C else F0 X
 have hp(X:Aura N)(C:Support (More N))(q':C⊆X.val): Fray P h q X C (F X C) (U X C) :=by
    refine ⟨?_,f X C q'⟩; unfold U; split
    next q=> exact u _ _ (by simp [fullD,q,q'])
    next p=> rw [not_nonempty_iff_eq_empty.mp p]; exact pA _

 refine ⟨U,⟨fun X C t=> (hp X C t).merit.wage (zero_le_one.trans v),?_ , ?_⟩, hp⟩
 · intro o; rw [show urnL U=F0 from (funext fun i=> if_neg Finset.not_nonempty_empty)]; exact w _
 · intro o; rw [show Vow.hymn U=Vow.hymn W from (funext fun i=> sum_congr rfl fun j p=> if_pos (mem_filter.mp p).2.1)]; exact g _
structure AccountV (D:Docket P)(q:ℕ)(h:ℝ)(F:Cusp N) where
 I : blazeK N
 ctx : D.Account I
 cash : bill P q h I F
variable {μ:Aura N→ℝ}{J:Rinse (Seat N) (Copy N)}{B:Orbit N→Aura N→FC (Dwell N)}
namespace Docket
variable (Y:D.Account I)(p:D.Chip μ)(t:1≤h) (f:bill P q h I F)(u:Stax.Pitch P h q J μ B)
-- renter estimates on any kernel & parameters. no rotor description. Fit.W.Eco
abbrev RiseB(P:BudgetPoint)(F:Cusp N)(J:Rinse (Seat N) (Copy N)) : Cusp N:= Stax.lamp (P:=P) F J
abbrev RemE(P:BudgetPoint)(F:Cusp N)(J:Rinse (Seat N) (Copy N)): Cusp N:= rem_X (P:=P) F J
include Y p t f u
lemma ΨH : (∀ X:Aura N,∀ r⊆ X.val,Fray P h q X r (RiseB P F J X r) (Sco I μ X r)∧Fray P h q X r (RemE P F J X r) (ScoL I μ X r)) ∧ (∀ i:Seat N,nook (roofL (Sco I μ) D.κ *loom_v (wu P) wΨ (widthK N P.B) 1) i ≤ D.Γ) ∧ (∀ i:Seat N,nook (roofL (ScoL I μ) D.κ*loom_v (ρL P) 0 (widthK N P.B) 1) i ≤ D.Week):= rentK F I f J μ u (wu P) (spanV P.B) D.κ D.Γ wΨ D.d (spanV P.B*D.d) D.d wΨ (ρL P) (widthK N P.B) (D.earnB μ I p Y) uΨ ℓZ ℓP t
lemma gas_h (o:Seat N) : tallB (urnL (Sco I μ)) P.B (ρL P) o ≤ D.Γ ∧ tallB (Vow.hymn (Sco I μ)) P.B (ρL P) o ≤ D.κ⁻¹*D.Γ:=by
 let X:= Sco I μ
 have hv (Y':Aura N)(j:Support (More N))(q:j⊆Y'.val):0≤ X Y' j:= ((ΨH Y p t f u).1 Y' j q).1.merit.wage (zero_le_one.trans t)
 obtain ⟨a,b⟩:= lam_H (b:=D.Γ) X o D.κ P.B (wu P-wΨ*1) (zero_lt_one.trans_le D.unitK) hv (by rw [parse]; exact (ΨH Y p t f u).2.1 o); exact ⟨(tall_m _ (fun k=>hv k ∅ (empty_subset _)) ℓTop o).trans a,(tall_m _ (fun i=> sum_nonneg fun j s=>hv i j (mem_filter.mp s).2.2) ℓTop o).trans b⟩ -- tune
lemma coronaC (o:Seat N) : tallB (urnL (ScoL I μ)) P.B (ρL P) o ≤ D.Week∧ tallB (Vow.hymn (ScoL I μ)) P.B (ρL P) o ≤ D.κ⁻¹*D.Week:=by
 let F':= ScoL I μ; refine lam_H F' o D.κ P.B (ρL P) (zero_lt_one.trans_le D.unitK) (fun i j V=> (((ΨH Y p t f u).1 i j V).2.merit.wage (zero_le_one.trans t))) ?_; simpa only [zero_mul,sub_zero, ← parse] using (ΨH Y p t f u).2.2 o -- tune rw order
lemma growth : PactF P (ρL P) h (EmptyD (RiseB P F J)) D.Γ∧ XL P h (ρL P) (RiseB P F J) (D.κ⁻¹*D.Γ):= ⟨⟨urnL (Sco I μ),fun i=> ((ΨH Y p t f u).1 i ∅ (empty_subset _)).1.merit, fun i=>(gas_h Y p t f u i).1⟩,(vouchers P h _ t _).2 ⟨Sco I μ,fun i j v=> ((ΨH Y p t f u).1 i j (mem_filter.mp v).2.2).1.merit,fun i=>(gas_h Y p t f u i).2⟩⟩
end Docket
end YM.CF.Sour.Heath
