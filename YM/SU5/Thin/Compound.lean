import SatinFixedContrastNovember4
import YM.SU5.Thin.Reaches

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
/-!
# N-point ordered costs, including actual and split tests

Not asking for products in contact or same points. All supports separated
already along axis 3, which suffices even through those mixtures. Proof through
that same state's loose & compressed operators. Extend to n-point words to be
clear about pricing these as insertions of new fields, even when retainment
of the compared SIGNAL here doesn't require such a strong interpretation.
-/
open DoseBill Sifter VoucherOp
namespace Theatre
variable {α β:Type*}[Ring α][Algebra ℂ α][Ring β][Algebra ℂ β]
variable {I V:Type*}[Nonempty V]
abbrev word {X:Type*}[Monoid X] (u:I→X)(L:List I):X:=(L.map u).prod
private def prefixBill (X:α→ₗ[ℂ]ℂ)(x:α):α→ₗ[ℂ]ℂ:= X.comp (LinearMap.mulLeft ℂ x)
private lemma changeWord {α:Type*}[Monoid α](u v:I→α)(L:List I)(e:∀ i∈L,u i=v i): word u L= word v L:= congrArg List.prod (List.map_congr_left e)
-- crucial for order tests: replace each slot by its own vector sum of choices.
lemma intoContext (u:I→ V→α)(v:I→V→β) (r:I→ Finset V)(c:I→ V→ℂ) (X:α→ₗ[ℂ]ℂ)(Y:β→ₗ[ℂ]ℂ)
    (L:List I)(h:L.Nodup)(p:∀ f:I→V,(∀ i∈L,f i∈ r i)→ X (word (fun i=>u i (f i)) L)=Y (word (fun i=>v i (f i)) L)) :
    X (word (fun i=> ∑ x∈r i,c i x • u i x) L)=Y (word (fun i=>∑ x∈r i,c i x • v i x) L):=by
  classical
  induction L generalizing X Y with
  | nil=> exact p (fun _=> Classical.choice (inferInstance : Nonempty V)) (by simp)
  | cons i L ih=>
     simp only [word,List.map_cons,List.prod_cons,Finset.sum_mul,Algebra.smul_mul_assoc,map_sum,map_smul]
     apply Finset.sum_congr rfl; intro w hw
     obtain ⟨t,y⟩:= List.nodup_cons.mp h
     have h := ih (prefixBill X (u i w)) (prefixBill Y (v i w)) y (by
        intro f e
        let F (j:I):= update f i w j; have he(j:I)(p:j∈ L): F j=f j:= update_of_ne (show j≠i from fun h => t (h ▸ p)) w f
        have z: F i=w:= update_self ..
        have hv:=p F (by intro b hb; rcases List.mem_cons.mp hb with rfl | b; exact z.symm ▸ hw; exact (he _ b).symm ▸ (e _ b)) -- conflict b
        change X (u i w*_)= Y (v i w*_)
        change X (u i (F i)* word (fun i=>u i (F i)) L)=Y (v i (F i)*word (fun i=>v i (F i)) L) at hv; rw [z,changeWord _ (fun i=>u i (f i)) L (fun i w=>congrArg (u i) (he i w)),changeWord _ (fun i=>v i (f i)) L (fun i w=>congrArg (v i) (he i w))] at hv; exact hv)
     exact congrArg (c i w • ·) (show X (u i w* word _ L)= Y (v i w* word _ L) from h)

def markVoice (H:Hilbert)(v:H) : H.Op→ₗ[ℂ]ℂ where
  toFun A:= inner ℂ v (A v)
  map_add' x y:= inner_add_right ..
  map_smul' x y:= inner_smul_right ..

/-- Order in axis 3. Allows consecutive non-overlapping slots with slab
endpoints touching, widths and test clearance stated separately. Always price
neighboring slots touching (e.g. placing disjointly with margin in their
interior). So no missing vacuum propagation costs from gaps. -/
structure Ordered (L:List I)(lo hi:I→ℝ) : Prop where
  walk : L.Pairwise (fun i j=> hi i ≤ lo j)
  separate : L.Nodup
  edge : ∀ i j A D,L=A++i::j::D → hi i=lo j
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H'"=> P.ColorHil 3 ξ
local notation "ω"=> P.colorZero 3 ξ
variable (f:I→SampleDose)(lo hi:I→ℝ) (A:I→ P.Apron)(L:List I)(e:Ordered L lo hi)(s:ℕ)(h:∀ i∈L,(A i).s ≤ s)(g:∀ i∈L, RoomThin P (A i) (f i) (lo i) (hi i))
local notation "β" i:max=> hi i
local notation "O" i:max=> P.usedGrid s (f i)
local notation "δ" i:max=> P.activation s (f i)
local notation "α" i:max=> P.issuing s (A i)
local notation "σ"=> P.singleState 3 s x
include h e g
lemma space_hold_t :
  P.singleState 3 s x (word (fun i=>P.prepared s (A i) (f i)) L) = markVoice H' ω (word (fun i=> P.gridPage x s (f i) (A i) (lo i) (hi i)) L) := by
  let u(i:I):= α i; let v(i:I)(k:Cover):= P.raze 3 ξ (A i) (lo i) (hi i) (P.vtile s k)
  apply intoContext u v (fun i=>O i) (fun i=>δ i) (P.singleState 3 s x) (markVoice H' ω) L e.separate
  intro z hz
  let M:= P.vtile s ∘ z; let F:= P.laysM ∘ M
  have hp(i:I)(p:i∈L):= g i p (F i) ((P.usedPose s (f i) _).mp (hz i p))
  have ht: P.Turnstile 3 A L F:= e.walk.imp_of_mem (by intro i j u v d; exact ((hp i u).2.trans_le d).trans (hp j v).1)
  refine ((P.single_agrees 3 3 x s _).symm.trans (P.turn_purchase 3 ξ A z s L ht h).symm).trans (P.pill_preview 3 ξ A L M lo hi hp e.edge)
omit h e g
section compared
lemma apertureApart {A B:P.Apron}{F G:SampleDose}{c d a b:ℝ} (p:RoomThin P A F a c)(q:RoomThin P B G d b)(u:c≤ d) {i j:Cover} (t:i∈ P.usedGrid s F)(k:j∈ P.usedGrid s G) : Disjoint (P.Aperture A (P.meshPose s i)) (P.Aperture B (P.meshPose s j)):=
  let P₁:= P.test_apart A F c B G (fun i t=>(p i t).2) (fun i t=>by have h:= (q i t).1; linarith only [u,h])
  P₁.mono (Set.subset_iUnion₂_of_subset (P.meshPose s i) ((P.usedPose s F i).1 t) Set.Subset.rfl) (Set.subset_iUnion₂_of_subset (P.meshPose s j) ((P.usedPose s G j).1 k) Set.Subset.rfl)
private lemma zeroBillWord (u:I→ V→«α») (r:I→ Finset V)(c:I→V→ℂ) (X:«α»→ₗ[ℂ]ℂ)(L:List I) (h:L.Nodup)(p:∀ f:I→V,(∀ i∈ L,f i∈r i)→ X (word (fun i=>u i (f i)) L)=0) : X (word (fun i=>∑ x∈r i,c i x • u i x) L)=0:= intoContext u u r c X (0:«α»→ₗ[ℂ]ℂ) L h p
variable {X:P.Test →ₗ[ℂ]ℂ}(p:Factors P.calibration X)(u:MatterWard P.calibration X ∨ GaugeWard P.calibration X)
include h e g p u
-- disjoint and any one Sensor (use head) on every term; never claim raw
-- factor property on algebra with overlapping supports/restricted domain
lemma splitHoldList (hL:L≠[])(t:∀ i∈L,∃ w:Bool,P.Sensor (A i) w):
    X (word (fun i=>P.prepared s (A i) (f i)) L)=0:= by
  apply zeroBillWord («α»:=P.Test) (fun i=>α i) (fun i=> O i) (fun i=>δ i) X L e.separate -- alpha name quoted
  intro z hz
  cases L with
  | nil=>contradiction
  | cons i L=>
    obtain ⟨w,v⟩:=t i List.mem_cons_self
    let U(i:I):=(A i,z i)
    let F:= L.map U
    let C (x:P.Apron × Cover):=P.issuing s x.1 x.2
    have he: word C F=word (fun i=>P.issuing s (A i) (z i)) L:= congrArg List.prod (List.map_map ..)
    change X (P.issuing s (A i) (z i)*word (fun i=>P.issuing s (A i) (z i)) L)=0; rw [←he]
    refine P.msplit w s p u (A i) (z i) v (h _ List.mem_cons_self) F ?_
    rintro w' g'; obtain ⟨j,q,rfl⟩:= List.mem_map.mp g'; let t':= List.mem_cons_of_mem i q
    exact ⟨h j t',apertureApart P s (g i List.mem_cons_self) (g j t') ((List.pairwise_cons.mp e.walk).1 j q) (hz i List.mem_cons_self) (hz j t')⟩
end compared
end Theatre
open Theatre
namespace VoucherOp
section parcels
variable {P:Spine}{n:ℕ}{b:ℕ→ℕ}{x:P.Spectrum0 3}{Z:Lead.Clan}(Q:P.VoucherOp x Z n b)(a:Bool)(s t:ℕ)
local notation "Ω"=> P.calibration
local notation "B" i:max=>P.cardSchedule Z n (b (s+i)) a
abbrev activeLevel (i:ℕ):= b (s+i)
def eligible : Prop:=∀ i∈(Q.cost s).take, b (s+i) ≤ t
lemma alwaysLater : ∀ᶠ t in atTop,Q.eligible s t:= (Filter.eventually_all_finset (Q.cost s).take).2 (fun i _=> eventually_ge_atTop (b (s+i)))
/-- ACTUAL resolution-$t$ mark, using the whole oriented mixtures. At same
window height `s`, and with endpoint coordinates posed independently on use.
For t-operators and questions on this need `eligible s t`. Geometry before
and through its formation will be costed as well. -/
def formMark (i : Cover) : P.Test := (Q.cost s).recipe fun k=> P.issuing t (B k) i
def markField (F:SampleDose) : P.Test:= (Q.cost s).recipe fun k=>P.prepared t (B k) F
lemma paintedField (F:SampleDose): Q.markField a s t F=∑ i∈P.usedGrid t F,P.activation t F i • Q.formMark a s t i:= by
  let h(y:ℕ):= (Q.cost s).weight y
  change ∑ j∈(Q.cost s).take, (h j:ℂ) • (∑ i∈ P.usedGrid t F, P.activation t F i • P.issuing t (B j) i) = ∑ i∈ _,_ • (∑ j∈_, _ • _)
  simp_rw [Finset.smul_sum]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i l=> Finset.sum_congr rfl fun j h=> smul_comm .. -- keep h name clash?
lemma literal_test (F:SampleDose): Q.markField a s t F=(Q.cost s).recipe fun k=> P.paintMark (B k) t F.val:= congrArg (Q.cost s).recipe (funext fun k=> P.reviewWardPaint _ _ _)
end parcels
end VoucherOp
namespace Theatre
section timing
variable {P:Spine}(x:P.Spectrum0 3){b:ℕ→ℕ}{n:ℕ}{I:Type*}(Z:I→Lead.Clan)(D:∀ i:I,P.VoucherOp x (Z i) n b)(w:I→Bool)(s:I→ℕ)(f:I→SampleDose)(lo hi:I→ℝ)(L:List I) (e:Ordered L lo hi)
variable (t:ℕ)
local notation "ξ"=> P.advocate 3 x 3
local notation "κ"=> P.enter 3 ξ
local notation "σ"=> P.singleState 3 t x
local notation "η"=> P.colorZero 3 ξ
local notation "H'"=> P.ColorHil 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "ν"=> P.heaven 3 ξ
local notation "W" i:max=> (D i).cost (s i)
local notation "V" k:max i:max=> P.cardSchedule (Z i) n (b (s i+k)) (w i)
def SureFoot : Prop:=∀ i∈L,∀ k∈ ((D i).cost (s i)).take, RoomThin P (V k i) (f i) (lo i) (hi i)
abbrev qualifiedLevel : Prop:=∀ i∈L,(D i).eligible (s i) t
local notation "Y" i:max=> (D i).markField (w i) (s i) t (f i)
local notation "B" i:max=> (D i).mixedGrid (w i) (s i) t (f i) (lo i) (hi i)
def measuredPrice : ℂ:= P.singleState 3 t x (word (fun i=>Y i) L)
variable (p:qualifiedLevel x Z D s L t) (u:SureFoot x Z D w s f lo hi L)
include p u e
theorem live : measuredPrice x Z D w s f L t = markVoice H' η (word (fun i=> B i) L):=
  intoContext (fun i k=>P.prepared t (V k i) (f i)) (fun i k=>P.gridPage x t (f i) (V k i) (lo i) (hi i))
    (fun i=> (W i).take) (fun i k=> ((W i).weight k:ℂ)) σ (markVoice H' η) L e.separate fun y v=>
    space_hold_t P x f lo hi (fun i=> V (y i) i) L e t (fun i t=> (P.schedule_height ..).trans_le (p _ t _ (v i t))) (fun i t=>u i t _ (v i t))
lemma losesPrediction {X:P.Test →ₗ[ℂ] ℂ}(F':Factors P.calibration X)(e':MatterWard P.calibration X ∨ GaugeWard P.calibration X) (y:L≠[])(m:P.calibration.ℓ<n): X (word (fun i=> Y i) L)=0:=
    zeroBillWord (fun i k=>P.prepared t (V k i) (f i)) (fun i=>(W i).take) (fun i k=> ((W i).weight k:ℂ)) X L e.separate fun g z=>
      splitHoldList P f lo hi (fun i=>V (g i) i) L e t (fun i h=> (P.schedule_height ..).trans_le (p _ h _ (z i h))) (fun i h=>u _ h _ (z i h)) F' e' y fun i _=>
        ⟨(Z i).2,by cases w i; exact P.thinString_reflect_senses (Z i) (b (s i+g i)) n m; exact P.thinString_senses (Z i) (b (s i+g i)) n m⟩
omit e p u
lemma apricot : ∀ᶠ t:ℕ in atTop,qualifiedLevel x Z D s L t:=by
  classical
  apply ((Filter.eventually_all_finset L.toFinset).2 (fun i _=> (D i).alwaysLater (s i))).mono ; intro t p i h; exact p i (List.mem_toFinset.mpr h)
end timing
end Theatre
#print axioms Theatre.live
#print axioms Theatre.losesPrediction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
