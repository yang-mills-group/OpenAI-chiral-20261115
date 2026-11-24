import YM.CF.Sour.Fro
set_option quotPrecheck false
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Cube Lat Tulip Peaks Fock Jet Branch Urn Levier Drapes Tenant
attribute [local instance] opCStarAlgebra
variable {N:Side}
set_option synthInstance.maxSize 20000
open Sour Vow
local notation "SS"=> More N
open Pressure
-- uniform pays kernels.Heats. threshold eta.After.L. ε arbitr.
variable {U:Scree.Loom N}{e a:ℝ}{P:BudgetPoint}{n r:ℕ}{S X D Z:Support (More N)}(hp:0<e)(h:Roof N b e r U)(vb:P.threshold ≤ b)
include hp h
def roller(X:Orbit N): ↥(Openc (More N) e):=⟨profile (U X),U X,h.paid X, by simpa⟩
lemma roll_g(t:Seat N→ SU.E)(X:Orbit N): roller hp h (Lattice.gauge t X.1,threadG t X.2)=(forum N e).drive t (roller hp h X):=Subtype.ext (by unfold roller; dsimp only [forum,affair]; rw [h.rev X.1 X.2,profile_g])
local instance boreKSpace (X:Side) : MeasurableSpace (Tulip.Stem (More X)):=borel _
local instance boreXN(X:Side): BorelSpace (Tulip.Stem (More X)):=⟨rfl⟩
lemma roll_m : Measurable (roller hp h):= (((Dial.profile_c).measurable).comp h.bill).subtype_mk
variable {F:Toll (Single N)}{C: Raw (Openc (More N) e) (Single N)}(L:Suite (badge _) (bail N e) (bail N e) S F C)
lemma pact_p (L:Suite (badge _) (bail N e) (bail N e) S F C)(x y: Orbit N)(g:Agrees S (U x) (U y)):C (roller hp h x)= C (roller hp h y):=by
 ext i j; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; have he:= (L.expo i j).variation (roller hp h x) (roller hp h y); rw [show (forum N e).eval S (roller hp h x) (roller hp h y)=0 from ?_,mul_zero] at he; exact he
 change fare S (Tulip.profile _) (Tulip.profile _) / _=0; have hp: fare S (Tulip.profile (U x)) (Tulip.profile (U y))=0:=by unfold fare; apply sum_eq_zero; intro i p; rw [show profile (U x) i= _ from (show profile (U x) i=profile (U y) i from funext fun k=> by unfold Tulip.profile; rw [g i (mem_filter.mp p).2.1 (mem_filter.mp p).2.2]),sub_self,norm_zero]
 rw [hp,zero_div]
variable {m:ℝ}(G':HopeT e m a P.order)(x:Orbit N)(Y:Vow.Aura N)(pY:halo (r+10) S ⊆ Y.val) -- tune
variable (pz:P.threshold ≤ a)(hD:halo (cipherK r) D ⊆ Y.val)(hs:cipherK r≤5*P.B)(ht:3≤P.B)
include hD pY hs ht pz hp h G' vb L
lemma earn_b (p: x.1∈σX P Y D)(t:D⊆Z)(i j:Single N): Allows P.order (fun v:tangD N=> C (roller hp h ((pressQ P Z x.1 v,x.2):Orbit N)) i j) 0 (F i j):=by
 let A(v:tangD N):Orbit N:=(pressQ P Z x.1 v,x.2); have hv:A 0=x:=by change (pressQ P Z _ 0,_)=_; rw [pressQ,smul_zero,born]
 apply G'.warm C F L _ (fun v=>roller hp h (A v)) 0 (fun v=>U (A v)) (fun _=>rfl) (h.paid (A 0))
 exact fun i w=> earnR h vb G' x Y pY pz hD hs ht p t i w
end YM.CF.Rill
