import Gingham.Farthing
import Gingham.Grotto
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)

open Heat
variable (x : P.Spectrum0 3)
variable {I:Type*} [Finite I]
local notation "K"=> P.calibration
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "Λ"=> P.par
local notation "Q"=> P.history
local notation "M"=> timeMesh P.par
local notation "Θ"=> P.reflectTest 3
local notation "T"=> P.shifts 3
local notation "τ"=> P.singleState 3
open Set Diary
variable (s:ℕ)
lemma sym_homes (f:P.Test):∀ᶠ n:ℕ in atTop,
   ∃ c:P.Card 3 s (n+n),P.entryTest 3 s c=T n f := by
 obtain ⟨D,h⟩:=findsBay _ f
 suffices e: ∀ᶠ n:ℕ in atTop, Between K 3 0 (ruler (Λ).block*(n+n:ℕ))
      (plow K 3 n D) by
   filter_upwards [P.supports_future 3 D, e] with n p q
   let w:= P.positiveVox 3 s _ _ (P.shifts_support 3 n D h) p
   exact ⟨⟨w,_,(Tapestry.locates ..).mp (P.shifts_support 3 n D h),q⟩,rfl⟩
 have r:= ruler_gene (Λ).block
 let Z:=ruler (Λ).block
 have per(i:Cover): ∀ᶠ n:ℕ in atTop,
      - (Z*n) + (K).ℓ ≤ i 3 ∧ i 3+(K).ℓ ≤ (Z*n) := by
   filter_upwards [eventually_ge_atTop ((i 3).natAbs+(K).ℓ)] with n a
   have k : (n:ℤ) ≤ Z*n:= le_mul_of_one_le_left (by positivity) r
   omega
 filter_upwards [(D.eventually_all).mpr fun i _=>per i] with n a i h
 obtain ⟨u,b,rfl⟩:=plow_stays K 3 n D h
 specialize a u b
 rw [moves,if_pos rfl]
 push_cast
 rw [show (K).B=(Λ).block from rfl]
 unfold Z at a
 constructor <;> linarith


omit [Finite I] in
abbrev gapL (s n t:ℕ):ℤ:= castor M s t (n:ℤ)
def chargeB (s n t:ℕ)(v:P.Vox 3 t):P.Test:= P.shifts 3 (gapL P s n t) (P.voxTest 3 t v)
def magnet(u f:P.Test):P.Test:= Θ u * (f*u)


lemma shift_mirror (u:P.Test)(d:ℤ) : T d (Θ (T d u))=Θ u:=by
 have h: TestFamily K true u.val:=(marque _).mp u.property
 obtain ⟨L,a⟩:= h.paid
 -- chime_diag : chime j k (mirror j m x)= mirror j m (chime j (-k)x)
 apply Subtype.ext
 change chime _ _ _ (mirror _ _ _ (chime _ _ _ _))=_
 rw [chime_diag K 3 _ 0 (flow_port K 3 _ a),
     Tower.bumps K 3 _ _ a,neg_add_cancel,Tower.wake K 3 a]
 rfl

variable (n t:ℕ)(p:s≤t)
include p in
lemma shift_bill (hw:0<n+n)(g:P.Test)(c:P.Card 3 s (n+n))
    (h:P.entryTest 3 s c=T n g) (v:P.Vox 3 t):
    inner ℂ (P.piece 3 t v)
      (P.Box 3 s _ hw c (P.piece 3 t v))=
    P.E t (magnet P (chargeB P s n t v) (P.conveying s (t-s) g)).val:=by
 let l:=gapL P s n t; let k:= (Λ).R.L.val^(t-s)*(n+n)
 let z:= P.voxTest 3 t v
 let u:= chargeB P s n t v
 let b:=P.conveying s (t-s) g
 let E:=magnet P u b
 suffices h₂: inner ℂ (P.piece 3 t v) (P.Box 3 s _ hw c (P.piece 3 t v))
    =P.E t (T l E).val from h₂.trans
    (SWay Y H P.law t 3 (2*l) ((marque _).mp E.property))

 have l2:l+l=(k:ℤ):=by
    unfold l k gapL castor; push_cast; change (((Λ).R.L.val:ℤ)^(t-s)*n)+(((Λ).R.L.val:ℤ)^(t-s)*n)=_; ring
 have hx:T l E= Θ z * (T l b * T (k:ℤ) z) :=by
    unfold E u magnet chargeB
    rw [map_mul,map_mul,P.shifts_sum,
      show T l (Θ (T l z))=Θ z from shift_mirror P z l,l2]
    -- tune l
 rw [hx]
 let d:=furnished Y H s Q 3 false (n+n) c t p
 have hd:P.entryTest 3 t d=T l b:=by
    have hu:P.voxTest 3 s c.val=T n g:=h
    rw [← P.convey_vox 3 c p,hu,P.walk_rig]
 let i:=slabT Y H t 3 false k d v
 have hm : P.Box 3 s _ hw c (P.piece 3 t v)=P.piece 3 t i:=
    snatch Y H P.law s Q P.projection.clipped 3 false (P.room 3) _ c hw p v
 rw [hm,P.seed_pairing,← hd]
 unfold i; rw [slab_eq]
 rfl


open Set
lemma sees_bills (F:I→P.Test){U:Set (I→ℂ)} (op:IsOpen U)
    (e:(fun i=>τ s x (F i))∈U) :
    ∀ᶠ n:ℕ in atTop, ∃ (t:ℕ) (_:s≤t) (v:P.Vox 3 t),
    (fun i=>P.E t (magnet P (chargeB P s n t v)
      (P.conveying s (t-s) (F i))).val) ∈U := by
 filter_upwards [eventually_gt_atTop 0,
    eventually_all.mpr (fun i=>sym_homes P s (F i))]
    with n nn h
 choose c hc using h
 have hn: 0<n+n:= by omega
 have hv:(fun i=>τ s x (P.entryTest 3 s (c i)))∈U:=by
    simpa only [hc,P.slide_single] using e
 obtain ⟨t,tt,v,hv⟩:=crying_cards P x hn c op hv
 refine ⟨t,tt,v,?_⟩
 simp_rw [fun i=>shift_bill P s n t tt hn (F i) (c i) (hc i) v] at hv
 exact hv

def coin(t:ℕ)(u:P.Test)(a:P.Test→ℂ)(f:P.Test):ℂ:= a (magnet P u (P.conveying s (t-s) f)) 
  / a (magnet P u 1)

lemma ratio_mean (F:I→P.Test){U:Set (I→ℂ)} (op:IsOpen U)
    (e:(fun i=>τ s x (F i))∈U) :
    ∀ᶠ n:ℕ in atTop,∃ (t:ℕ) (_:s≤t) (v:P.Vox 3 t),
    let m:=chargeB P s n t v
    let E : P.Test→ℂ:=fun h=>P.E t h.val
    E (magnet P m 1)≠0 ∧ (fun i=>coin P s t m E (F i))∈U := by
 let J:=Option I → ℂ
 let G:Option I→P.Test :=fun i=>match i with | none=>1 | some y=>F y
 let V : Set J :={y| y none≠0∧(fun i=>y (some i)/y none)∈U}
 have ge:(fun i=>τ s x (G i))∈V:=by
   have q:τ s x (G none)=1:=(P.common_reading s x 1 3).2.2.2
   change τ s x (G none)≠0 ∧ (fun i=>τ s x (F i) / τ s x (G none))∈U
   simp only [q,div_one]
   exact ⟨one_ne_zero,e⟩

 have vO:IsOpen V:=by
   rw [isOpen_iff_mem_nhds]
   rintro y ⟨h,q⟩
   have hs: ContinuousAt (fun z:J=> fun i=> z (some (i:I)) / z none) y:=by
     refine continuousAt_pi.mpr fun i=> (continuous_apply _).continuousAt.div
        (continuous_apply _).continuousAt h
   exact (inter_mem ((continuous_apply none).continuousAt.eventually (isOpen_ne.mem_nhds h)) (hs.eventually (op.mem_nhds q)))
 filter_upwards [sees_bills P x s G vO ge] with n a
 obtain ⟨t,u,v,p⟩:=a
 refine ⟨t,u,v,?_⟩
 have r : P.conveying s (t-s) (G none)=1:= Subtype.ext (woven_one Y H (Q).circuit s (t-s))
 let l:=chargeB P s n t v
 change P.E t (magnet P l (P.conveying s (t-s) (G none))).val≠0 ∧
   (fun i=>P.E t (magnet P l (P.conveying s (t-s) (F i))).val /
      P.E t (magnet P l (P.conveying s (t-s) (G none))).val) ∈U at p
 rw [r] at p
 exact p

/-- AFTER election. For every finite query, arbitrary open accuracy demands,
    paid by one pair of Mark charges, held fixed at a single enlarged
    consultation height, eventually even at the same regulated price along
    joint path. -/
lemma ratio_sharp (F:I→P.Test){U:Set (I→ℂ)} (op:IsOpen U)
    (e:(fun i=>τ s x (F i))∈U) :
    ∀ᶠ n:ℕ in atTop, ∃ (t:ℕ) (_:s≤t) (v:P.Vox 3 t),
     let m:=chargeB P s n t v
     ∀ᶠ j in atTop, Ferry P.run t (irr P j) (uvv P j) ∧
      rawE P t j (magnet P m 1)≠0 ∧
       (fun i=>coin P s t m (rawE P t j) (F i))∈U :=by
 filter_upwards [ratio_mean P x s F op e] with n h
 obtain ⟨t,u,v,p,q⟩:=h
 refine ⟨t,u,v,?_⟩
 intro m
 let E:P.Test→ℂ:=fun g=>P.E t g.val
 have he:Tendsto (fun j i=>coin P s t m (rawE P t j) (F i)) atTop
    (𝓝 (fun i=>coin P s t m E (F i))) :=
   tendsto_pi_nhds.mpr fun i=> (rawE_joint P t _).div (rawE_joint P t (magnet P m 1)) p
 exact (atHeight P t).and ((((rawE_joint P t (magnet P m 1)).eventually
    (isOpen_ne.mem_nhds p))).and (he.eventually (op.mem_nhds q)))


