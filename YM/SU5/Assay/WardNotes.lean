import YM.SU5.Assay.Parcel
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Six

variable {P:Spine}{f g:P.Test}{S T D:Finset Cover}{s t:ℕ}{W:Bool}
local notation "K"=> P.calibration
/-!
# Ward vouchers for beam consultations

`paperSplit`: use exactly the Dome comparison of SatinFixed, i.e. the product
of both actual pure marginals on the raw resolution test (possibly already
representing pose, smear, refinement). `PostAsk`: support plus ward statement,
including an actual charged component assignment with vanishing pure values,
also against any disjointly supported spectator. Covers single and all products
of disjoint marks with at least one beam mark, on their cost at price height.

`PriorSingle`, `PriorPair`: pre-refinement assignments kept, finer poses billed
on those pure inputs in separate gauge and matter consultations. Again costs
vanish, even termwise, including the pure prices themselves. Supports exactly
as for mixed positions, also here given by Bay certificates and pin budgets.
The survey only needs the prices of these pure tests; no convergence statement
as separate operator inserts is required for these marginal prescriptions.
-/
variable (P) (s) (x:P.Spectrum0 3)
noncomputable def paperSplit : P.Test →ₗ[ℂ]ℂ:= (P.comparator s x).choose
local notation "E"=> P.singleState 3 s x
local notation "Q"=> P.paperSplit s x
lemma paper_law: Comparison K E Q ∧ Q 1=1∧GaugeWard K Q∧MatterWard K Q:=(P.comparator ..).choose_spec
lemma paper_forced {X:P.Test →ₗ[ℂ]ℂ}(h: Comparison K E X): X=Q:= h.unique K E (P.paper_law ..).1

/-- Termwise actual ward extinguishing, including all pure prices paired
with pure prices of others on disjoint supports, e.g. terms at either gauge or
matter of two consultations with this qualification. -/
def Douse (f:P.Test)(Y:Set Vantage):Prop:= P.asked_at s f Y ∧ E f=0∧
    ∀ (Z:Set Vantage)(g:P.Test),P.asked_at s g Z→Disjoint Y Z→E (f*g)=0
variable {P s}{Y Z:Set Vantage}
lemma GFlame.douse (p:P.GFlame f)(q:P.asked_at s f Y): P.Douse s x f Y:=by
 refine ⟨q,p.value 3 s x,fun Z g u v=>?_⟩
 obtain ⟨S,t,h⟩:=q
 obtain ⟨T,w,e⟩:=u
 exact (p.beside t w (P.pin_disjoint _ _ _ (v.mono h e))).value 3 s x

variable (P s)
def PostAsk (f:P.Test)(Y:Set Vantage)(W:Bool):Prop:=∃ (D:Finset Cover) (l:List (P.Test × P.Test)), P.pinFoot s D ⊆ Y ∧
 f∈bay K D true∧Presented K W D f l∧(∀a∈l,P.Douse s x a.1 Y ∧ P.Douse s x a.2 Y) ∧
 (∀ X:P.Test →ₗ[ℂ]ℂ, Factors K X→MatterWard K X ∨GaugeWard K X→ X f=0) ∧ Q f=0
variable {P s}

lemma beamAsk.post (h:P.beamAsk s f Y W):P.PostAsk s x f Y W:=by
 have ht:=P.paper_law s x
 have he:Q f=0:= h.fee ht.1.factors (Or.inr ht.2.2.1)
 obtain ⟨D,p,z⟩:=h; obtain ⟨l,w⟩:=Beam.present p
 refine ⟨D,l,z,Beam.bay_le p,w,fun a i=>?_,fun X u v=>Beam.fee u v p,he⟩
 have u:=w.2 a i
 have k:=pure_flames u
 exact ⟨k.1.douse x ⟨_,u.2.2.1,z⟩,k.2.douse x ⟨_,u.2.2.2.1,z⟩⟩
lemma PostAsk.zero (p:P.PostAsk s x f Y W):Q f=0:=by obtain ⟨_,_,_,_,_,_,_,h⟩:=p;exact h

lemma Apron.Beams.native {B:P.Apron}(p:B.Beams W):P.PostAsk B.s x B.F (P.Aperture B 0) W:=
 beamAsk.post x ⟨B.S,p,P.aperture_licensed _⟩
lemma Apron.Beams.backdrop {B:P.Apron}(p:B.Beams W)(v:B.s≤t)(r:Cover):
    P.PostAsk t x (P.issuing t B r) (P.Aperture B (P.meshPose t r)) W:=
 beamAsk.post x ⟨_,p.issue v r,P.inside_now _ _ _ v⟩
lemma Apron.Beams.projection {B:P.Apron}(p:B.Beams W)(v:B.s≤t)(F:SampleDose):
    P.PostAsk t x (P.prepared t B F) (P.spacePrice B F) W:=
 (p.prepare v F).post x
lemma Apron.Beams.survey {B:P.Apron}(p:B.Beams W)(v:B.s≤t)(F:SampleDose){C:P.Apron}(w:C.s≤t)(G:SampleDose)(d:Disjoint (P.spacePrice B F) (P.spacePrice C G)):
   P.PostAsk t x (P.prepared t B F*P.prepared t C G) (P.spacePrice B F ∪ P.spacePrice C G) W:=
 ((p.prepare v F).visitor (P.prepared_at t C G w) d).post x

variable (P)
abbrev JointPiece:Type:=P.Test × P.Test
section
variable (t:ℕ)(B C:P.Apron)
local notation "It"=> P.sParcel t
local notation "E₁"=> P.singleState 3 t x
local notation "D₁"=> P.Douse t x
/-- Actual values on separate pure inputs, and the marginal product price
at finer pose, for a choice of original terms. No requirement that the pure
components after promotion are still pure inputs. -/
def PriorSingle (l:List P.JointPiece)(r:Cover):ℂ:= (l.map (fun a=> E₁ (It B a.1 r)*E₁ (It B a.2 r))).sum
def PriorPair (l n:List P.JointPiece)(r o:Cover):ℂ:=
    (l.map (fun a=> (n.map (fun b=> E₁ (It B a.1 r*It C b.1 o)*E₁ (It B a.2 r*It C b.2 o))).sum)).sum
def Offer (l:List P.JointPiece)(r:Cover):Prop:=∀a∈l,D₁ (It B a.1 r) (P.Aperture B (P.meshPose t r))∧D₁ (It B a.2 r) (P.Aperture B (P.meshPose t r))
variable {P}{l n:List P.JointPiece} {r o:Cover}
lemma sParcel.offer (p:Presented K W B.S B.F l) (v:B.s≤t)(r:Cover)(R:P.Register):P.Offer x t B l r:=by
 intro i u; have h:=p.2 i u; have k:=pure_flames h
 exact ⟨(flame B t k.1 r R).douse x ⟨_,atPlot B t h.2.2.1 r,P.inside_now _ _ _ v⟩,
 (flame B t k.2 r R).douse x ⟨_,atPlot B t h.2.2.2.1 r,P.inside_now _ _ _ v⟩⟩
variable {x B C t}
lemma Offer.zero (p:P.Offer x t B l r):P.PriorSingle x t B l r=0:=by
 unfold PriorSingle
 apply List.sum_eq_zero
 intro a h; obtain ⟨b,v,rfl⟩:= List.mem_map.mp h; exact mul_eq_zero_of_left ((p b v).1.2.1) _
lemma Offer.versus (p:P.Offer x t B l r)(q:P.Offer x t C n o)
 (d:Disjoint (P.Aperture B (P.meshPose t r)) (P.Aperture C (P.meshPose t o))):P.PriorPair x t B C l n r o=0:=by
 unfold PriorPair
 apply List.sum_eq_zero
 intro a h; obtain ⟨b,v,rfl⟩:=List.mem_map.mp h
 apply List.sum_eq_zero
 intro u h; obtain ⟨c,s,rfl⟩:=List.mem_map.mp h
 exact mul_eq_zero_of_left ((p b v).1.2.2 _ _ ((q c s).1.1) d) _
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
