import GaugeFieldConstruction.RamseyTurnVU
import GaugeFieldConstruction.RevelatoryVU
import GaugeFieldConstruction.CassioCurrencyVU
/-!
NativeFaith visibility on ONE Base Poll Price.
Asserting root observation is not buried in disallowed/exotic distinctions at
high cutoffs even if singular-sector requests & calibration.
At all late cut: top observation is nonzero on positive measure sharp-admissible SU. At same cut its origin was already nonzero in physically consulted BOTH torus marks. For currency-weighted observations this is genuine interaction with gauge orbits already on such joint draws.
-/
set_option autoImplicit false
set_option maxHeartbeats 330000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Reconstruction Tapestry.Altitude Tapestry.Exhibition PhaseChoice
open _root_.YM.OS.Ground TopologicalSpace
namespace Spine
variable {P: Spine}{R:P.Register}{x:P.Spectrum0 3}{i k s:ℕ}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "K"=> tent P.run P.large
local notation "N"=> side Y i (P.run.uv k)
local notation "ν"=> prior SU.group (More N)
local notation "Ω" => side P.run i s
open Six
abbrev closePictureVU (P:Spine)(i k:ℕ)(a:P.Effect) : Prop:= ∃ᶠ U in ae (prior SU.group (More (side P.run i (P.run.uv k)))), flags (P.run.meter.a (P.run.uv k)).threshold U=∅ ∧ atCutoff P.run P.large i k a U≠0
abbrev widerAngleVU (P:Spine)(s i:ℕ)(a:P.Test) :Prop := ∃ᶠ x in ae (city (side P.run i s)), exhibit P.run P.large s i a.val (drawn ((P.run.voyage i).CapeT s) x)≠0
abbrev flashingVU (P:Spine)(s i:ℕ)(a:P.Test):Prop:=
 ∃ᶠ x in ae (city (side P.run i s)),
  let F:= exhibit P.run P.large s i a.val; let g:= fun y=>drawn ((P.run.voyage i).CapeT s) y
  F (g x)≠0 ∧ ∃ u:Skye.Seat (side P.run i s)→ SU.E, g (gird u x)=Buffered.simultaneous u (g x) ∧
    F (g (gird u x))= twist (quantU (tradew (side P.run i s) u)) (F (g x)) ∧ F (g (gird u x))≠F (g x)
private lemma zeroFrameVU {X:BillsSumVU P}{a:MeterPanelVU P}{U:Pane (side P.run i (P.run.uv k))}(h:a∈ X)(e:atCutoff P.run P.large i k a.1 U=0): witnessCutVU P i k X U=0:=by
 induction X with
 | nil=> simp at h
 | cons b X ih=>
    change (atCutoff P.run P.large i k b.1 U)*(witnessCutVU P i k X U)=0
    rcases List.mem_cons.mp h with h|h; rw [←h,e,zero_mul]; rw [ih h, mul_zero]
private lemma flashAtTopVU {U:Pane (side P.run i (P.run.uv k))} {A':Evaluation (side P.run i (P.run.uv k))}(w:bareAmplitude P.run i k A' U≠ 0): flags (P.run.meter.a (P.run.uv k)).threshold U=∅ ∧ A' U≠0:=by
 constructor
 · by_contra p; apply w; simp only [bareAmplitude, Vale.capP, Set.indicator_of_notMem (show U∉{v:Pane (side P.run i (P.run.uv k))| flags _ v=∅} from p),map_zero,inner_zero_right]
 intro u; apply w; rw [bareAmplitude, u,YM.CF.act_zero,inner_zero_right]
lemma frameSeenVU {A:BillsSumVU P}{r:ℕ}(v: AskingPriceVU P r A≠0)(a)(p:a∈A): closePictureVU P (P.diagonalᵢ r) (P.diagonalₖ r) a.1:=by
 let W:= bareAmplitude P.run (P.diagonalᵢ r) (P.diagonalₖ r) (witnessCutVU P (P.diagonalᵢ r) (P.diagonalₖ r) A)
 let μ:= prior SU.group (More (side P.run (P.diagonalᵢ r) (P.diagonalDepth r)))
 have he:(∫ x,W x ∂μ)≠0 := left_ne_zero_of_mul v -- division def?
 apply (frequently_ae_ne_zero_of_integral_ne_zero he).mono; intro U h; obtain ⟨b,z⟩:= flashAtTopVU (P:=P) h; exact ⟨b,fun g=> z (zeroFrameVU p g)⟩
lemma flashSeenVU {a:P.Test}(h: PairIdx P.run s i k)(v:closePictureVU P i k (P.slotHole s a)) : widerAngleVU P s i a:=by
 intro q
 obtain ⟨U,t,v⟩:= v.exists; apply v; have he:= awakeningRootVU Y H i k s h a (q.mono fun _=> not_not.mp); change diagMark (attire (breathing Y H (P.run.uv k) i k (pinhole _ _ _))) U=0; rw [he]; rfl
lemma flashingSeenVU {f:P.Test}(e:f∈enclave P.calibration)(v:f.val∈CurrencyVU P.calibration):∀ᶠ i in atTop,widerAngleVU P s i f → flashingVU P s i f:=by
 filter_upwards[(momentum P.run s).eventually (opDetectedVU e v)] with i p q
 apply q.mono; intro U t L' G
 obtain ⟨g,a,b⟩:= CastMovesVU (terrain Y H (P.run.ir i) s) _ p _ t
 have he: G (gird g U)= Buffered.simultaneous g (G U):= Prod.ext rfl (((P.run.voyage i).ownership s).paid.rev _ _ _)
 refine ⟨t,g,he,?_,?_⟩
 · rw[he]; exact a
 rw [he]; exact b
where CastMovesVU{n N':Side}(h:n=N')(A:Mark n)(v:∀ x,A x≠0→ ∃u:Skye.Seat n→SU.E,A (Buffered.simultaneous u x)=twist (quantU (tradew n u)) (A x)∧ A (Buffered.simultaneous u x)≠A x)(y:Fields N')(e: arrange n N' h A y≠0):∃ u:Skye.Seat N'→SU.E, arrange n N' h A (Buffered.simultaneous u y)=twist (quantU (tradew N' u)) (arrange n N' h A y)∧ arrange n N' h A (Buffered.simultaneous u y)≠arrange n N' h A y:=by subst N'; exact v y e
#print axioms flashSeenVU
#print axioms frameSeenVU
#print axioms flashingSeenVU
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
