import Gingham.Banding
import Gingham.Eaves
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe

namespace Spine.Gingham

open SatinRegistration YM.Velour
variable (a:Weave)
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω₁"=> P.heaven 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "𝓢"=> P.seasons 3 ξ
local notation "T"=> (𝓢).E
local notation "V"=> P.cartage 3 ξ
local notation "D"=> (𝓢).muslin
local notation "Ω"=> P.firstTulle 3 ξ


open Diary
open Tower.Reconstruction
open Set

def magnet0 (u:P.Test):P.Test:=P.reflectTest 3 u * u
lemma caseUnit (u:P.Test) : magnet P u 1 = magnet0 P u:= by simp [magnet,magnet0]
variable (t:ℕ)(u:P.Test)
lemma joint_pay (f g:P.Test)(B C:Set Vantage)
    (h:P.asked_at t f B)(k:P.asked_at t g C):
    P.asked_at t (f*g) (B∪C):=by
 obtain ⟨S,w,h⟩:=h
 obtain ⟨Z,z,k⟩:=k
 have v:InTest P.calibration true (S∪Z) false (f*g).val:=
    ((show InTest P.calibration true S false f.val from w).mono Finset.subset_union_left).mul
       ((show InTest P.calibration true Z false g.val from z).mono Finset.subset_union_right)
 refine ⟨_,v,?_⟩
 rw [P.pin_union]; exact Set.union_subset_union h k

variable (j:ℕ)(q:Ferry P.run t (irr P j) (uvv P j))
local notation "Launch"=> finTor P t j q
variable (f g:P.Test)
local notation "Mₐ"=> Launch (P.reflectTest 3 u)
local notation "Mᵦ"=> Launch u
local notation "reg"=> rawE P t j

def sunward (N:ℝ):Set Vantage:={z|z 3 ≤ -N}
def away (N:ℝ):Set Vantage:={z|N ≤ z 3}
variable (N:ℝ)
def bareTile (B:Mount P j) := Mₐ * (B * Mᵦ) 
def bareCoin (B:Mount P j) :ℂ:=
  bareRead P j (bareTile P t u j q B) /
    bareRead P j (Mₐ*Mᵦ)
def soleil (B C:Mount P j):Parts:=
  let h:=bareCoin P t u j q
  (h (B*C),h B,h C)

structure Papers :Prop where
   unit: bare_equate P j (Mₐ*Mᵦ) (reg (magnet P u 1))
   singL: bare_equate P j (bareTile P t u j q (Launch f)) (reg (magnet P u f))
   singR: bare_equate P j (bareTile P t u j q (Launch g)) (reg (magnet P u g))
   both: bare_equate P j (bareTile P t u j q (Launch f * Launch g)) (reg (magnet P u (f*g)))

lemma incoming (e:Papers P t u j q f g):
    soleil P t u j q (Launch f) (Launch g)=
   (tariff P t u j (f*g),tariff P t u j f,tariff P t u j g):=by
 simp only [soleil,bareCoin,tariff,
   e.unit.price,e.singL.price,e.singR.price,e.both.price]

-- specialization after J large.
lemma bows (h:Lodgment P t N u)(n:0<N)
  (X:Set Vantage)(l:P.asked_at t f X)(d:∀x∈X,|x (3:Axis)|<N):
  ∀ᶠ j in atTop,∀ q,
   finTor P t j q (magnet P u f)=
     bareTile P t u j q (finTor P t j q f):=by
 let B:=sunward N; let C:=away N
 have e : Disjoint X C:=Set.disjoint_left.mpr fun z v k=>
    (lt_of_le_of_lt (le_abs_self _) (d z v)).not_ge k

 have v : Disjoint B (X∪C):= by
    refine Set.disjoint_left.mpr fun z b y=>?_
    have hz:z 3 ≤ -N:=b
    obtain i|i:=y
    · have hw:=abs_lt.mp (d z i); linarith
    · have hw:N ≤ z 3:=i; linarith
 filter_upwards [
   Diary.through_product P t f u X C l h.owner e,
   Diary.through_product P t _ (f*u) B (X∪C) h.reflect
     (joint_pay P t _ _ _ _ l h.owner) v]
   with j b w q
 rw [magnet,w q,b q]; rfl

lemma bows_unit (h:Lodgment P t N u)(n:0<N):
   ∀ᶠ j in atTop,∀ q,
   finTor P t j q (magnet P u 1)=
     finTor P t j q (P.reflectTest 3 u) * finTor P t j q u :=by
 have e:Disjoint (sunward N) (away N):=by
   refine Set.disjoint_left.mpr fun z v w=>?_
   linarith only [n,show z 3 ≤ -N from v,show N ≤ z 3 from w]
 filter_upwards [Diary.through_product P t _ u _ _ h.reflect h.owner e] with j b q
 rw [caseUnit,magnet0];exact b q


lemma lifelike (h:Lodgment P t N u)(n:0<N)(J K:Set Vantage)
    (hf:P.asked_at t f J)(hg:P.asked_at t g K)(d:Disjoint J K)
    (p:∀v∈J∪K,|v (3:Axis)|<N):
    ∀ᶠ j in atTop,∀ q,Papers P t u j q f g :=by
 filter_upwards [bows_unit P t u N h n, bows P t u f N h n J hf (fun v e=>p v (Or.inl e)),
    bows P t u g N h n K hg (fun v e=>p v (Or.inr e)),
    bows P t u (f*g) N h n _ (joint_pay P t _ _ _ _ hf hg) p,
    Diary.through_product P t _ _ _ _ hf hg d] with j hu e b c w q
 have h₀:=bare_equates P t j q (magnet P u 1)
 have h₁:=bare_equates P t j q (magnet P u f)
 have h₂:=bare_equates P t j q (magnet P u g)
 have h₃:=bare_equates P t j q (magnet P u (f*g))
 rw [hu q] at h₀; rw [e q] at h₁;rw [b q] at h₂
 rw [c q,w q] at h₃
 exact ⟨h₀,h₁,h₂,h₃⟩


/-- The quartet of stencil launches: first both width stencils, with
  the inspector-pair last in list. Multiplication price below of course
  arranges the inspector-pair on opposite ends. -/
def desk {α:Type*}(f g z u:α): Bool × Bool → α
  | (false,false)=>f
  | (false,true)=>g
  | (true,false)=>z
  | (true,true)=>u

abbrev plate (f g:P.Test) : Bool × Bool → Mount P j:=
   fun i=> Launch (desk f g (P.reflectTest 3 u) u i)

lemma plated (h:Lodgment P t N u)(J K:Set Vantage)
    (hf:P.asked_at t f J)(hg:P.asked_at t g K):
    ∀ᶠ j in atTop,∀ q,
    Secure P t j (desk J K (sunward N) (away N))
       (plate P t u j q f g) := by
    apply secures
    rintro ⟨(_|_),(_|_)⟩
    · exact hf
    · exact hg
    · exact h.reflect
    · exact h.owner

variable (α β:Hook P x) (s i k:ℕ) (δ:ℝ)
local notation "Lᵘ"=> CarrierB P s t (BlotAt a P x α i s)
local notation "Rᵘ"=> CarrierB P s t (WellAt a P x β k s)
open Tower


structure Served : Prop where
  carries: Secure P t j (desk a.ra a.rb (sunward N) (away N)) 
                (plate P t u j q Lᵘ Rᵘ)
  colors₁: covariant (toMark (Launch Lᵘ))
  colors₂: covariant (toMark (Launch Rᵘ))
  furnished: Papers P t u j q Lᵘ Rᵘ
  divides: bareRead P j (Mₐ*Mᵦ) ≠0
  agrees: soleil P t u j q (Launch Lᵘ) (Launch Rᵘ) = SharpEu a P x s t α β i k u j
  strict_cost: Topaz (soleil P t u j q (Launch Lᵘ) (Launch Rᵘ)) (AudEu a P x α β) δ


lemma banquet (A:ℝ) (d:RadiusAudit a A) (h:Lodgment P t (A+1) u)
     (r:SharpBill a P x s t α β i k δ u):
    ∀ᶠ j in atTop,∃ q, Served a P x t u j q (A+1) α β s i k δ:=by
 have b:= r.inquiry.holdsL
 have c:= r.inquiry.holdsW
 have hR:∀v∈a.ra∪a.rb, |v (3:Axis)|<A+1:= fun v p=>
      (d.bev v p).trans (lt_add_of_pos_right _ zero_lt_one)
 have hh:Disjoint a.ra a.rb:= Set.disjoint_left.mpr fun z h k=>lt_irrefl _ (a.stagger _ h _ k).2.1
 filter_upwards [
     plated P t u _ _ _ h _ _ b c,
     lifelike P t u _ _ _ h (add_pos d.pos one_pos) _ _ b c hh hR, r.scan]
    with j a₀ w x₀
 obtain ⟨q,z,top⟩:=x₀
 have aq:=a₀ q
 have bq:=w q
 have al:soleil P t u j q (finTor P t j q Lᵘ) (finTor P t j q Rᵘ)=
     SharpEu a P x s t α β i k u j:=
   incoming P t u j q _ _ bq
 exact ⟨q,aq,cProof P t j q r.inquiry.a_color,
    cProof P t j q r.inquiry.b_color,bq,bq.unit.price ▸ z,
    al,al.symm ▸ top⟩

def BareLedger : Prop :=
    ∃ A:ℝ, RadiusAudit a A ∧
     ∃ n,∀ i k s:ℕ, n ≤ i → n ≤ k → n ≤ s → Height P x α β i k s →
       InBuoy a P x α β i k s ∧
       ∃ t, s≤t ∧ ∃ u:P.Test, Lodgment P t (A+1) u ∧
          SharpBill a P x s t α β i k δ u ∧
          ∀ᶠ j in atTop,∃ q, Served a P x t u j q (A+1) α β s i k δ

/-- Any measurements funded by Glory (i.e. δ>0 strictly protected through
the full consultation and registration schedule) in fact buy the strict
budget on the bare path (common beta by cutoff, etc., unconditioned bare
law paying for a literal inspector-stencil pair as spec'd; see Banquette).
No claim off-path. -/
theorem glamour (h:Glory a P x α β δ):BareLedger a P x α β δ :=by
 obtain ⟨A,d,n,e⟩:=veiled a P x α β h
 refine ⟨A,d,n, fun i k s a₀ b c v =>?_⟩
 obtain ⟨r,t,l,u,g,w⟩:=e i k s a₀ b c v
 exact ⟨r,t,l,u,g,w,banquet a P x t u α β s i k δ A d g w⟩
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Gingham.glamour

