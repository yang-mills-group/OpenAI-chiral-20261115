import Bay.C.Ferry
import Bay.C.Sliding
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks

set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
open Py Py.Rate Thera Dial Nacre Laic
open LocalLimit Preparation


open Salt SU Swell
open BProof Bide
open Buffered (modesIn AtSupport covariant toMark)
variable {N:Side}(s:Sweep N){T:footprint N}{d:ℝ}{f:Stencil N}{y:phy N}
local notation "XM"=> modesIn N
lemma roundModes (S:footprint N):XM S=modes S:= by ext;exact Iff.trans modes_ch (mem_modes .. |>.symm)
lemma slideM (S:footprint N):twist (socks s) (cutM (XM S))=cutM (XM (actY s S)):=by rw [roundModes,roundModes];exact eligible ..

lemma fits_move (t:Fits T d f):Fits (actY s T) d (move s f):=by
 let W:=toMark f
 let paste : Buffered.Fields N → Buffered.Fields N:=fun u=>(flashA s⁻¹ u.1,flashA s⁻¹ u.2)
 have m:Measurable paste:= ((revM s⁻¹).measurable.comp measurable_fst).prodMk ((revM s⁻¹).measurable.comp measurable_snd)
 refine ⟨⟨?_,?_,fun i=>
   fineTour _ _ _ (tickR (castX s) (xtra s.charge) _ (spinZ ..) _) (slideM s T)
     (t.basis.allV (paste i))⟩, ?_,fun i=>(normTour s.charge _ (socks s) _).trans_le (t.purse _)⟩
 · exact Girt.pole_w (X:=FC (Single N)) (W ∘ paste)
      (Hive.teen s) (tour_c ..) (Girt.snap (X:=paste) t.basis.env m)
 · intro x y a b
   have H (u v)(k:Agrees (↑(actY s T):Set _) u v):Agrees (↑T:Set _) (flashA s⁻¹ u) (flashA s⁻¹ v):=flashD _ _ _ T (by rwa [sitU s])
   exact congrArg (Hive.teen s) (t.basis.dep (paste x) (paste y) (H _ _ a) (H _ _ b))
 intro g u
 have k:Hive.Keys (W (paste u)):=Chord.keys_of_chord (Chord.full (t.basis.allV (paste u)).sector)
 have p:=Hive.yoT s (chosen s⁻¹ g) _ k
 change _ = Hive.Gaze (chosen s (chosen s⁻¹ g)) _ at p
 rw [boast_gg] at p
 have h:= t.paid (chosen s⁻¹ g) (paste u)
 change Hive.teen s (f (flashA s⁻¹ (Lattice.gauge g u.1))) =_
 have e: flashA s⁻¹ (Lattice.gauge g u.1)=Lattice.gauge (chosen s⁻¹ g) (paste u).1:=revG ..
 rw [e]
 exact (congrArg (Hive.teen s) h).trans p

lemma march_mates (A:Accompanies T d f y):
 Accompanies (actY s T) d (move s f) (clash s y):=by
 refine ⟨fits_move s A.pay,fun x=> sceneTour _ _ _ (slideM s T) (A.lives _),?_⟩
 intro i
 obtain ⟨i,rfl⟩:=surRaise s i
 rw[alight]
 have h: move s f (yellA s i).1=rawk s (f i.1):=congrArg (fun x=> rawk s (f x)) (revB ..)
 rw [h]
 let W:=mateK N
 let E:= arum (socks s) s.charge (detX s.s) W
 have u:E W=W:= arum_self _ _ _ (Tset _) (touchP _ ▸ tickB N)
    (tickR (castX s) (xtra s.charge) _ (spinZ ..) _)
 have he(R:FC (Single N)):E (acts (star R) W) = acts (star (rawk s R)) W:=by
   unfold E; rw [arum_act,starsTour];exact congrArg (acts _) u
 rw [←he,←he]
 exact congrArg E (A.mate i)
