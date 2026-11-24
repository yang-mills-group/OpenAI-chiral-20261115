import YM.SU5.Reconstruction.LinkMeasures.PointReads
import VerifiedSatinSelectedSectors
/-!
# Local link array (both!) and material measure.
Important no assertion absolutely continuous w.r.t. volume on that array.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
variable (S:Finset Cover)
noncomputable def LocalEdges : Finset (Edge Cover) := (S ×ˢ Finset.univ).filter (fun x=> x.1+step x.2∈ S)
lemma localEdges (e:Edge Cover): e∈ LocalEdges S ↔ e.1∈ S ∧ e.1+step e.2∈ S := by simp [LocalEdges, mem_filter]
abbrev Aerial := ↥(LocalEdges S)→ SU.E
abbrev ScoreBook := Aerial S × Aerial S
noncomputable def limitOne (U:LinksC) : Aerial S := fun e=> U e.val
noncomputable def recoverOne (U:Aerial S) : LinksC:= fun e=> if h:e∈ LocalEdges S then U ⟨e,h⟩ else 1
@[fun_prop] lemma limit_cont:Continuous (limitOne S):= continuous_pi fun e=> continuous_apply e.val
@[fun_prop] lemma recover_cont:Continuous (recoverOne S):= by refine continuous_pi fun e=>?_ ; unfold recoverOne; split; exact continuous_apply _; exact continuous_const
@[simp] lemma limit_recover (U:Aerial S): limitOne S (recoverOne S U)=U:= by ext e:1; simp [limitOne,recoverOne,e.property]
lemma limits (U V:LinksC): limitOne S U=limitOne S V ↔ Agrees S U V:= by
 constructor; intro h e a b; exact congrFun h (⟨e, (localEdges S e).mpr ⟨a,b⟩⟩ : LocalEdges S); intro h; exact funext fun e=> h _ ((localEdges S _).mp e.property).1 ((localEdges S _).mp e.property).2 -- syntax `intro h` same line? 
noncomputable def here: PairsC → ScoreBook S := Prod.map (limitOne S) (limitOne S)
@[fun_prop] lemma here_c:Continuous (here S):=(limit_cont S).prodMap (limit_cont S)
noncomputable def decode: ScoreBook S → PairsC:= Prod.map (recoverOne S) (recoverOne S)
@[fun_prop] lemma decode_c : Continuous (decode S):=(recover_cont S).prodMap (recover_cont S)
@[simp] lemma here_decode(v:ScoreBook S): here S (decode S v)=v:=Prod.ext (limit_recover ..) (limit_recover ..)

open PaymentCamera
abbrev Listener:=PaymentCamera.Test (ScoreBook S)
lemma feesHere (x:Listener S): Coeff true S (x.val ∘ here S):= by
 refine ⟨by simp,⟨x.meas.comp (here_c ..).measurable,?_⟩,fun a b u v=>?_⟩
 · obtain ⟨C,h⟩:=x.bounds; exact ⟨C,fun i=> h (here S i)⟩
 exact congrArg (x.val) (Prod.ext (y:=here S b) (x:=here S a) ((limits S ..).2 u) ((limits S ..).2 v)) -- Dot too many?
noncomputable def perform(x:Listener S): Pigment S := pigment S (feesHere S x)
lemma lyric(x:Listener S): daub S (perform S x)=x.val ∘ here S:=rfl
noncomputable def accession (t:Pigment S): Listener S:= ⟨daub S t ∘ decode S,(authentic S t).env.meas.comp (decode_c S).measurable,‖t‖,fun i=>daubLe ..⟩
lemma known (x:Pigment S): perform S (accession S x)=x:=by
 apply daub_inj S; funext a; change daub S x (decode S (here S a))=_; exact (authentic S x).locus _ _ ((limits S _ _).1 (congrArg Prod.fst (here_decode S (here S a)))) ((limits S _ _).1 (congrArg Prod.snd (here_decode S (here S a))))
noncomputable def seatFaith : Listener S ≃ₗ[ℂ] Pigment S where
 toFun := perform S
 invFun:= accession S
 left_inv x:= Subtype.ext (by funext i; change x.val (here S (decode S i))=_; rw [here_decode])
 right_inv:= known S
 map_add' x y:=daub_inj S rfl
 map_smul' z x:=daub_inj S rfl

variable (Λ:Preparation)(l:ℕ)
local notation "P₀" => plaza (Λ:=Λ) S
local notation "C" => (VolumeCape.Dream.plot l).C
local notation "Z" => (VolumeCape.Dream.plot l).K
noncomputable def pull (u:Courses (VolumeCape.Dream.plot l).C (plaza (Λ:=Λ) S)): Measure (ScoreBook S):= (Common.law C P₀).map (here S ∘ (pairs C Z P₀ u))
instance bill_finite (u:Courses C P₀):IsFiniteMeasure (pull S Λ l u):=by unfold pull; infer_instance
noncomputable def actual: Measure (ScoreBook S):= ∑ u:Common.Courses C P₀,pull S Λ l u
instance physically_finite:IsFiniteMeasure (actual S Λ l):=by unfold actual; infer_instance
lemma cost_eq (x:Listener S): PaymentCamera.bill (actual S Λ l) x = Satin.price Λ l S (daub S (perform S x)):=by
 rw [bill_eq,actual,integral_finsetSum_measure]; refine Finset.sum_congr rfl fun u _=>?_ ; swap; · exact fun u _=>(x.finances (pull S Λ l u)).norm
 rw [pull,integral_map]; rfl; exact ((here_c S).measurable.comp (pairs_m ..)).aemeasurable; exact x.meas.norm.aestronglyMeasurable
-- spelling step response next rung in terms of these measures
noncomputable def singer (w:Evens S): Listener S →ₗ[ℂ] Swatch S := (LinearMap.single ℂ (fun _:Evens S=> Pigment S) w).comp (seatFaith S).toLinearMap
lemma toneHere (w:Evens S)(x:Listener S): singer S w x= Tapestry.nuance S w (perform S x):= rfl
end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.cost_eq
#print axioms YM.CF.Buffered.Afterglow.Satori.seatFaith
