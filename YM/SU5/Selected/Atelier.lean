import YM.SU5.Selected.Awoken
import YM.SU5.FiniteGaugeData.Tapestry.Spring
import YM.SU5.Selected.Sealing
/-!
# Full resolution polynomial Algebra attached to this G

As in Tapestry `Spring`, all polynomials at resolution levels, support widths
and coherent advancement. Same step as `Fashion`. It is not a subalgebra of
an unbounded Minkowski operator space--multiplication is Euclidean. Measures at the
paying periods/cutoffs & polynomial realization read `taking`: actual coupling
of one SU(5) gauge trajectory with full chiral-car marks (traced normalized)
as checked in `SeasonCert`. `Attached` below specializes to phase resolution
on these same choices so mixing equality. Positivity in any chosen ground phase
(not a direct inheritance from probability of preexisting E). Higher resolution
compatibility by coherence of ALL tests in `Dome`. Locality in footprint
through `Tapestry.well`. No cross-motion continuous interpretation asserted.
Mirroring for arbitrary hinge Sunlight on authorized levels (even for mixed
polynomial contacts).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
open Set Theory MeshClock Tapestry Tapestry.Altitude Tapestry.Exhibition
variable {L:Rack Λ l}{B:Clay Λ l}(D:Exhibition Y H i k I E L B)
local notation "χ"=>Dome (tent Y H)
local notation "Cₚ"=>Cloud (Dome (tent Y H))
local notation "F₀"=>vistaDressing Y H D
local notation "P₀" n:max=>vistaFinish Y H n D
local notation "D₀" n:max=> Exhibition.liftD Y H n D
variable (d:Axis)(T:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
local notation "R"=>catalog Y H V G d false (T d)

include D V in
lemma lifecycle (S:Finset Cover)(s:ℕ): B S s=transfer Y H G S s:=by
  let C:ℕ→ WedgeStage := fun r=>⟨G.rows r,G.columns r,(D.status ..).mp (G.history.gate r)⟩
  have h: Tendsto C atTop followStage:= tendsto_comap_iff.mpr G.history.growsA.tendsto_atTop
  exact tendsto_nhds_unique ((D.coneAdvance Y H S s).comp h) (transfer_limit Y H V G S s)
include V in
lemma lifts_here (s:ℕ) (f:χ): ((D₀ s) f).val=G.refine s f.val:=by
  obtain ⟨S,h⟩:=findsBay (tent Y H) f; obtain ⟨a,rfl⟩:=accolade (tent Y H) S f h
  rw [fromLocal,lifecycle Y H V G D S]; exact (transferred ..).symm

variable (x:Resident (catalog Y H V G d false (T d)))
local notation "Mx"=>evaluate Y H V G d T x
noncomputable def audition (s:ℕ) : Dome (tent Y H) →ₗ[ℂ] ℂ where
 toFun f:= Mx s f.val
 map_add' p q:=by
   unfold evaluate; rw [dif_pos (show TestFamily K true _ from (p+q).property),dif_pos (show TestFamily K true _ from p.property),dif_pos (show TestFamily K true _ from q.property)]; exact addAt Y H V G false d (T d) x s rfl
 map_smul' z p := by
   change Mx s (z • p:χ).val=z • Mx s p.val; unfold evaluate; rw [dif_pos (show TestFamily K true _ from (z • p:χ).property),dif_pos (show TestFamily K true _ from p.property)]; exact scaleAt Y H V G false d (T d) x s z rfl
local notation "Ε"=>audition Y H V G d T x
lemma audition_lifts (s:ℕ) : (Ε (s+1)).comp ((F₀).surge s)=Ε s:=by
  ext1 f; change Mx (s+1) (((D₀ s) f).val)=_; rw [lifts_here Y H V]; exact elect_refine Y H V G d T x f.property s 1
lemma audition_1 (s:ℕ): Ε s 1=1:= (consistency Y H V G d T x ∅ s).unit -- tune
noncomputable def onDrawing : Cloud (Dome (tent Y H)) →ₗ[ℂ] ℂ :=
  Decking.fadeRead (F₀) (auxiliaryPad K) Ε (audition_lifts Y H V G D d T x)
local notation "Θ"=> onDrawing Y H V G D d T x
lemma drawAt {n:ℕ}{f:Cₚ}(p:f∈shorter χ n): Θ f= Ε n ((P₀ n) f):=Decking.fate (F₀) n f (auxiliaryPad K) (Ε) (audition_lifts Y H V G D d T x) p
lemma plugged (n:ℕ)(f:χ): Θ (pinhole χ n f)= Mx n f.val:=by rw [drawAt Y H V G D d T x (short_pinhole n f), vistaFinish, Decking.outcrop]; rfl
lemma umbrella (n:ℕ)(f:χ)(u:Cover→SU.E): Ε n (pennant K u f)=Ε n f:=by
  obtain ⟨S,t⟩:= findsBay (tent Y H) f
  exact ((consistency Y H V G d T x S n).gauge u _ _ t (pennantLocal K S u t) (pennantTrace K S u t)).symm
lemma normalized_draw : Θ 1=1:=Decking.fadeOne (F₀) _ (Ε) (audition_lifts Y H V G D d T x) (audition_1 Y H V G d T x 0) -- tune
lemma costume {f:Cₚ}(h:f∈FiniteGaugeDataPoly K)(u:GPhysical) : Θ (rainfall Λ K u f)=Θ f:=by
  obtain ⟨n,h⟩ := Altitude.curve.mp h
  rw [drawAt Y H V G D d T x (raining_height Λ K n u h),drawAt Y H V G D d T x h,vistaRain Y H n u D f h,umbrella]
lemma ensemble_fires {f:Cₚ} (p:f∈FiniteGaugeDataPoly K):
   (∫ x, onDrawing Y H V G D d T x f∂residents Y H V G false d (T d))=vistaTake Y H D f:=by
  obtain ⟨n,p⟩:=curve.mp p
  have q(x:Resident ↥(catalog Y H V G d false (T d))): onDrawing Y H V G D d T x f= evaluate Y H V G d T x n ((P₀ n) f).val := drawAt Y H V G D d T x p
  simp_rw [q,vistaCall Y H n f D p]
  let g : observable K false:= observe (show TestFamily K true ((P₀ n) f).val from ((P₀ n) f).property)
  change (∫ x,evaluate Y H V G d T x n g.val ∂_) = E n g.val
  simp_rw [evaluates]; exact residents_mean Y H V G false d (T d) n g
lemma cont_at_dome (n:ℕ)(f:Dome (tent Y H)):Continuous (fun y:Resident R=> evaluate Y H V G d T y n f.val):=by
  let h : TestFamily (tent Y H) true f.val:=((marque ..).1 f.property)
  change Continuous (fun x=>evaluate Y H V G d T x n (observe h).val)
  simp_rw [evaluates]; exact mean_admit Y H V G false d (T d) n (observe h)
lemma ensemble_cont {f: Tapestry.Altitude.Cloud (Dome (tent Y H))}(p:f∈FiniteGaugeDataPoly K): Continuous (fun y:Resident R=> onDrawing Y H V G D d T y f):=by
  let n:= (Tapestry.Altitude.curve.mp p).choose
  have ht:f∈shorter χ n:= (Tapestry.Altitude.curve.mp p).choose_spec
  have q(x:Resident R): onDrawing Y H V G D d T x f= evaluate Y H V G d T x n ((P₀ n) f).val := drawAt Y H V G D d T x ht
  have h:(fun y:Resident R=> onDrawing Y H V G D d T y f)= (fun y:Resident R=> evaluate Y H V G d T y n ((P₀ n) f).val):=funext q
  exact transport _ _ h (cont_at_dome Y H V G d T n ((P₀ n) f))
where transport {X:Type}[TopologicalSpace X] (f g:X→ℂ) (p:f=g)(q:Continuous g):Continuous f:=p.symm ▸ q


section mirror
variable (z:Sunlight Λ)
local notation "s₀"=>z.start
local notation "θ"=>z.oppose Λ j K
local notation "S₀"=>flank j (z.hinge Λ)
private lemma warmglass (n:ℕ)(p:z.start≤n) {f:χ}(h:f∈keep Λ l n K true (flank j (z.hinge Λ))) :
    0 ≤ Ε n (aureole K j (z.marks n) f*f):=by
  obtain ⟨S,h,t⟩:=h; have ht:Tower.region j (z.marks n) (K).ℓ S:= (z.rents Λ l j n p).mp t
  obtain ⟨w,h'⟩:= z.shifted n p; rw [h'] at ht ⊢; exact elect_plane Y H V G j d T x h ht n
lemma chamber {f:Cₚ}(h:f∈Sunlight.sanctum Λ l j z K): 0 ≤ Θ (z.oppose Λ j K f*f):=by
  obtain ⟨n,p,t⟩:= z.limitsArena Λ l j K h
  let u:= D.glass Y H j z
  rw [drawAt Y H V G D d T x ((shorter χ n).mul_mem (z.respectsCut Λ l j K t) (jettyBan Λ l K true _ _ n t)), vistaFinish, reflectionHat Λ l j z n (F₀) _ u p t t]
  exact warmglass Y H V G j d T x z n p (crownShelter Λ l n (F₀) _ u.lantern (flank j (z.hinge Λ)) u.onward t)
lemma chamber_all {I:Type*}[Fintype I](F:I→Cₚ)(p:∀ i,F i∈Sunlight.sanctum Λ l j z K):
    (Matrix.of (fun i t=> Θ (z.oppose Λ j K (F i)* F t))).PosSemidef:=
  let L:=Sunlight.sanctum Λ l j z K; let g:=lustre Θ θ L.val.toLinearMap; lustred g (fun x' : L=> chamber Y H V G j D d T x z x'.property) (fun i=>⟨F i,p i⟩)
-- general flip on polynomial supported on arena of z (even with crossing terms)
local notation "λᵣ" V:max n:max=> jetty Λ l K true V ((z.arena Λ) ∩ Set.Iic n)
lemma reflects_cloister {n:ℕ} (p:z.start≤n) {U:Set RSpace} {f:Cₚ} (t:f∈λᵣ U n) :
    (P₀ n) (θ f)=aureole K j (z.marks n) ((P₀ n) f):=by
  let S:=(z.arena Λ)∩ Set.Iic n
  apply boarded (P:={t| Officer ((z.arena Λ) ∩ Set.Iic n) (fun i=> keep Λ l i K true U) t}) (M:=fun x=>(P₀ n) (θ x)=aureole K j (z.marks n) ((P₀ n) x)) ?_ ?_ ?_ ?_ t
  · intro g (t : Officer S _ g)
    have ht := t.visible S _ Set.inter_subset_right
    change (P₀ n) (θ (pureShot K g))= _; rw [Sunlight.opposes, vistaFinish, Decking.reckon_paid _ _ _ ht, Decking.reckon_paid _ _ _ (z.opponentEnough Λ j n K ht)]; exact trail n p g (fun i hi=> t.forbids i (fun (p:i∈S)=> hi.not_ge p.1))
  · simp only [map_zero]
  · intro a b i j' q r; rw [map_add,map_add,map_add,map_add,q,r]
  intro a b r g; rw [LinearMap.map_smulₛₗ (f:=θ), map_smul (P₀ n), map_smul (P₀ n),LinearMap.map_smulₛₗ (f:=aureole K j _),g]
where
 trail(n:ℕ)(p:z.start≤n) (g:Tapestry.sequenceOf K)(h:∀ i< z.start,g i=1) :
    Decking.finish (F₀) n (Sunlight.opponent Λ j z K g) = aureole K j (z.marks n) (Decking.finish (F₀) n g):=by
   induction n,p using Nat.le_induction with
   | base=>
     rw [Decking.finish_alone (F₀) _ (Sunlight.opponent Λ j z K g) (fun i p=>show aureole K j (z.marks i) (g i)=1 from by rw [h i p,aureoleUnit]),Decking.finish_alone (F₀) _ _ h]; rfl
   | succ t v ih=>
     rw [Decking.finish, Decking.finish, aureoleProduct, ih]; change (D₀ t) (aureole K j (z.marks t) _)*aureole K j (z.marks (t+1)) (g (t+1)) = _
     rw [Breflect,z.aligned t v]; rfl
lemma reflect_draw {U:Set RSpace}{f:Cₚ}(h:f∈jetty Λ l K true U (z.arena Λ)): Θ (θ f)=star (Θ f):=by
  obtain ⟨n,t⟩:= entrusted Λ l K true U (z.arena Λ) h
  let m:= max z.start n; let p:z.start≤ m:=le_max_left ..; let S:=(z.arena Λ) ∩ Set.Iic m
  have hf:f ∈ jetty Λ l K true U S:=admits Λ l K true U U ((z.arena Λ)∩ Set.Iic n) S (fun _ q=>⟨q.1,le_trans q.2 (le_max_right z.start n)⟩) Set.Subset.rfl t -- stuck
  have ha:= jettyBan Λ l K true _ _ m (z.opposition Λ l j K (V:=U) (S:=S) Set.inter_subset_left true hf)
  rw [drawAt Y H V G D d T x ha, drawAt Y H V G D d T x (jettyBan Λ l K true U (z.arena Λ) m hf),reflects_cloister Y H j D z p hf]
  obtain ⟨w,u⟩:= z.shifted m p; rw [u]; exact elect_mirror Y H V G j d T x (((P₀ m) f).property) w m
end mirror
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.ensemble_fires
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.chamber_all
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.reflect_draw
