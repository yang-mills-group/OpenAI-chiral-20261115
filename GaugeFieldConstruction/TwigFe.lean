import YM.SU5.FiniteGaugeData.Tower.Cloaks
import YM.SU5.FiniteGaugeData.Tower.Ink
import GaugeFieldConstruction.PavilionFe
import GaugeFieldConstruction.GladeFe
import GaugeFieldConstruction.TimorFe
import GaugeFieldConstruction.GaolFe
import GaugeFieldConstruction.TongaFe
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Native gauge holds also on the step lift (no Protected equality hypotheses).
-/
open Fock Laurent Bloch Next.Free Fir Branch Tap Tenant Precision Drapes Vault Tree
open Reed (Fine think)
open BrentFe
open YM.GaugeFieldConstruction (Flavor)
open YM.GaugeFieldConstruction.Flavor
open XGarden.MastTin.ArtCart
set_option maxHeartbeats 70000
variable {K: Calibration}
open XGarden.MastTin.ArtCart
namespace MatrixFe
variable (g:Flavor)
lemma shipFe {n k:Side}(X:Mark n)(h:n=k): ship h (latticeFφFe g n X)=latticeFφFe g k (ship h X):=by subst n; rfl
variable (S:Finset Cover)(F:Family (tent Y H))(κ n:ℕ)
lemma loftyFe (u:InTest (tent Y H) true S false F)(p:legalAt Y s κ n)(t:GenYearFe Y κ s n g)(v:Tivoli (wingspan Λ l S) ((tent Y H).c (momentm Y κ (s+1)))): block Y H s κ n S (RayPFe g F)=RayPFe g (block Y H s κ n S F):=by
 have h(k:ℕ)(A:Family (tent Y H)): distribute Y H k κ (RayPFe g A)= latticeFφFe g _ (distribute Y H k κ A):= shipFe ..
 apply stationary_ext Y H (s+1) _ κ v.hosp (booked ..) (axP g (booked Y H ..)); rw [reserved Y H s _ κ n p (axP g u) v,h,reserved Y H s _ κ n p u v]
 unfold aboveD; rw[h]; exact SharpGenFe _ _ _ _ _ _ (t.pφ p.2) _ _ _ _ _ _ (stationed Y H s _ κ u) -- tune
end MatrixFe
open MatrixFe
namespace VacuumSelection.Spine
open Tapestry
variable {P:Spine}
abbrev FrozenFe (P:Spine)(s:ℕ): Prop := ∀ᶠ i in atTop, legalAt P.run s (P.gatePeriod i) (P.gateCut i) ∧ ∀ g:Flavor,GenYearFe P.run (P.gatePeriod i) s (P.gateCut i) g
lemma aspenFe(P:Spine)(C:Clip→ℝ)(τ:ℝ)(O:Oath.BellPrice.PinRack→Badge)(Q:TintDemand)(N:ℕ)(H:Armature C τ O P Q N):∀ᶠ s in atTop,FrozenFe P s:=by
 obtain ⟨_,V,Pay,kC,Γ,Tξ,A,C',τ',v,Zκ,κ,L,Y,Nq,h1,h2,u,a,b,q,f,T'⟩:= H
 filter_upwards [genEraFe P.run _ _ _ _ _ _ T'] with s h
 filter_upwards [P.history.finance (s+1)] with i t; exact ⟨⟨t.depth,t.enters⟩, h _ _ (Nat.le_succ s |>.trans t.enters)⟩
def KinOpFe (g:Flavor)(X:P.Test):P.Test:=by
 refine ⟨RayPFe g X.val,aux_test (axP g ((show TestFamily (tent P.run P.large) true X.val from X.property).paid.choose_spec))⟩
variable (P) in
lemma KinHFe (s:ℕ)(h:P.FrozenFe s)(X:P.Test)(g:Flavor): P.conveying s 1 (KinOpFe g X)= KinOpFe g (P.conveying s 1 X):=by
 obtain ⟨S,p⟩:= Tapestry.findsBay P.calibration X; let A:= P.conveying s 1; let Z:= KinOpFe g X; have hp:Z∈ bay P.calibration S true:=axP g ((locates ..).mp p)
 have hr(W:P.Test)(t:W∈bay P.calibration S true) : LongQueue P (volumeAround P.par P.width 1 S) (fun k=> train P.run P.large s 1 (P.gatePeriod k) (P.gateCut k) S W.val) (A W):= SlabMark.train_queue P.run P.large s P.history W.val S (fun _=>W.val) (LongQueue.attain W t) _
 have hT: Tendsto P.gatePeriod atTop atTop:= P.law.pick.grow_i.tendsto_atTop.comp P.history.growsA.tendsto_atTop
 apply Subtype.ext; funext m i
 refine tendsto_nhds_unique_of_eventuallyEq (meetβ (hr Z hp) _ _) ((Fock.breeze (quantU (TVfe (P.calibration.c m) g))).continuousAt.tendsto.comp (meetβ (hr X p) m i)) ?_
 filter_upwards [h,hT.eventually (turning P.run P.large (s+1) (wingspan P.par P.width S))] with k v w; exact congrFun (congrFun (loftyFe P.run P.large s g S X.val _ _ ((locates ..).mp p) v.1 (v.2 g) w) m) i -- tune reorder
namespace SaberFe
variable (g:Flavor)(P:Spine)
lemma action (f F:P.Test): SaberFe P g f F ↔ F=KinOpFe g f:= ⟨fun p=>Subtype.ext (funext fun i=>funext (p i)),fun p=>by rw [p]; exact fun i j=>rfl⟩
variable {g P} {X Z:P.Test}
lemma flip (p:SaberFe P g X Z)(a:Axis) : SaberFe P g (P.reflectTest a X) (P.reflectTest a Z):=by
 obtain ⟨S,h⟩:= X.property.paid; rw [action] at p ⊢; subst Z; apply Subtype.ext; exact MatrixFe.flipFe g a _ h
lemma moving (p:SaberFe P g X Z)(a:Axis)(z:ℤ) : SaberFe P g (P.shifts a z X) (P.shifts a z Z):=by
 obtain ⟨S,h⟩:= X.property.paid; rw [action] at p ⊢; subst Z; apply Subtype.ext
 let W:=P.calibration; let x:= X.val
 change chime W a _ (RayPFe g x) = RayPFe g (chime W a _ x); unfold chime; rw [MatrixFe.flipFe g a _ h, MatrixFe.flipFe g a _ (axial _ a _ h)]
lemma allSh (p:SaberFe P g X Z)(v:Cover): SaberFe P g (P.chartAll v X) (P.chartAll v Z):=by
 unfold chartAll; generalize Vacancy.ordinate=l; induction l with
 | nil=> exact p
 | cons i l ih=> rw [P.cruise_step,AlgHom.comp_apply,AlgHom.comp_apply]; exact ih.moving i _
lemma makeFe (q:SaberFe P g X Z)(s:ℕ)(n:ℕ) (h:∀ i≥s,P.FrozenFe i): SaberFe P g (P.conveying s n X) (P.conveying s n Z):=by
 induction n with
 | zero=>exact q
 | succ i t=>
    have ht(Y:P.Test): P.conveying s (i+1) Y=P.conveying (s+i) 1 (P.conveying s i Y):= rfl -- maybe
    rw [ht,ht]; rw[action] at t ⊢; rw[t]; exact P.KinHFe _ (h _ (by omega)) _ g
#print axioms makeFe
end SaberFe
end VacuumSelection.Spine
end YM.CF.Buffered.Afterglow.Tower
