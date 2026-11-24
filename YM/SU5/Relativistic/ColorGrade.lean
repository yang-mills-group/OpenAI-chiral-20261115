import YM.SU5.Relativistic.FermiStep
/-! # Trace compatibility on all refined odd words. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
local notation "W"=>wingspan Λ l
variable (i' k':ℕ) (S : Finset Cover) {b c:Bool}
variable {f g: Family (tent Y H)}

open Tapestry
private lemma harmVest {n m:Side} (N:n=m) (w:Cover→SU.E) (S:Finset Cover)(u:Seat n→SU.E){f g:Mark n}(t:TraceGauge S w u)(h:∀ (v:Seat m→SU.E), TraceGauge S w v → Harmony v (ship N f) (ship N g)):Harmony u f g:=by subst N; exact h _ t
private lemma written {J:Calibration}{b:Bool}{S:Finset Cover}{w:Cover→SU.E}{f g:Family J} (x:InTest J true S b f)(p:InTest J true S b g){m:Side} (y:Hosp S (J.c m)) (u:Seat (J.c m)→ SU.E)(h:TraceGauge S w u)(a:Harmony u (f m) (g m)): Circular S w f g:=by
 obtain ⟨F,t,H⟩:=reColor w x
 have he (x:Fields (J.c m)):g m x=F m x:= (twist (quantU (tradew _ u))).injective ((a x).symm.trans (H m u h x))
 have hz:g=F:=by
    cases b; exact box_ext J S p t y (funext he); exact single_ext S J y p t (funext he)
 rwa [←hz] at H

lemma splash (p:legalAt Y s i' k')(q:Tivoli (wingspan Λ l S) ((K).c (momentm Y i' (s+1)))) (x:InTest K true S b f)(v:InTest K true S b g)
    (T:Cover→SU.E)(e:Circular S (parentGauge Λ T) f g): Circular (W S) T (moveUp Y H s i' k' S b f) (moveUp Y H s i' k' S b g):=by
 obtain ⟨u,t⟩:= scoreTrace T q.hosp
 let F:=moveUp Y H s i' k' S b f; let G:=moveUp Y H s i' k' S b g
 refine written (stay ..) (stay ..) q.hosp u t (harmVest (terrain Y H (Y.ir i') (s+1)) T (W S) u t (fun v' a=>?_))
 change Harmony v' (distribute Y H (s+1) i' F) (distribute Y H (s+1) i' G); unfold F G
 rw [rebased Y H s i' k' S p x q, rebased Y H s i' k' S p v q]
 apply ascendHarmony Y s i' k' p (parked Y H s i' _ v) v' (parked Y H s i' _ x).env
 have h:= truePrinting S _ Y H s i' e (hierarchyTrace S T Y s i' v' a)
 rw [present_send,present_send] at h; exact h
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
