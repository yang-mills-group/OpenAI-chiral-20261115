import Gingham.Grotto
import YM.SU5.Relativistic.Footprints
import YM.SU5.Reconstruct.Bare
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

open Tower.Reconstruction
open Tower.PhaseChoice
open Dial Reed Pastry
namespace Diary
variable (t j:ℕ)
local notation "i₀"=>irr P j
local notation "k₀"=>uvv P j
local notation "σ"=>side Y i₀
local notation "nₖ"=>nn P j

def roof (f:P.Test): (d:ℕ)→Mark (side Y (irr P j) (t+d))
 | 0=> exhibit Y H t i₀ f.val
 | d+1=> ascender Y (t+d) i₀ k₀ (roof f d)



variable {f g:P.Test}{S Z :Finset Cover} (p:(P.run.voyage (irr P j)).kick ≤ uvv P j)
include p
lemma loft (a:f∈bay K S true)(d:ℕ)(h:t+d≤nₖ) :
   AtSupport false (Satin.region (volumeAround Λ P.width d S) (σ (t+d)))
      (roof P t j f d) ∧
    rawE P t j f=Journey.compass Y i₀ k₀ (t+d) (roof P t j f d):=by
 have hS:InTest K true S false f.val:=a
 induction d with
 | zero=> exact ⟨exhibited Y H t i₀ S hS,actualRead ..⟩
 | succ d ih=>
    have hp:Satin.PairIdx Y (t+d) i₀ k₀:= ⟨p,h⟩
    obtain ⟨x,y⟩:= ih (Nat.le_of_lt hp.2)
    exact ⟨ascendSupport Y (t+d) i₀ k₀ _ hp x,y.trans (Tapestry.partake Y (t+d) i₀ k₀ hp (x.mono (subset_univ _)))⟩


lemma loft2 (a:f∈bay K S true)(b:g∈bay K Z true) 
    (e:Detached Λ P.width S Z)(o:Host Y H i₀ t (S∪Z))
    (d:ℕ)(h:t+d≤nₖ):
    roof P t j (f*g) d=roof P t j f d * roof P t j g d:= by
 induction d with
 | zero=> exact Tapestry.actual_product ..
 | succ d ih=>
    have hp:Satin.PairIdx Y (t+d) i₀ k₀:= ⟨p,h⟩
    rw [roof,roof,roof,ih (Nat.le_of_lt hp.2)]
    exact ascendSep Y _ _ _ hp (loft P t j p a d hp.2.le).1
         (loft P t j p b d hp.2.le).1 (Host.far Y H e o d)

lemma lofted (a:f∈bay K S true)(b:f∈enclave K)
    (d:ℕ)(h:t+d≤nₖ): covariant (roof P t j f d):=by
 induction d with
 | zero=>
    have e:= (enclave_spec _).mp b
    rw [roof]
    have hu {m n:Side} (p:m=n) (F: Mark m)(w:covariant F):covariant (arrange m n p F):=by subst n;rw [arranged];exact w
    exact hu (terrain Y H ((Y).ir i₀) t) _ (e _)
 | succ d ih=>
    have hp:Satin.PairIdx Y (t+d) i₀ k₀:= ⟨p,h⟩
    exact ascendGauge Y _ _ _ hp (loft P t j p a d hp.2.le).1 (ih hp.2.le)



omit p
def steeple (r:ℕ)(h:t≤r)(f:P.Test):Mark (σ r):=
    ((Nat.add_sub_of_le h) ▸ roof P t j f (r-t))

/-- transport without recursion through equality/subtraction. -/
lemma atSteeple (d:ℕ)(f:P.Test):
    steeple P t j (t+d) (by omega) f=roof P t j f d := by
  have h {r e:ℕ} (p:t≤r)(u:r-t=e)(z:r=t+e):
      steeple P t j r p f=z.symm ▸ roof P t j f e:=by
    subst e; rfl
  have hu:=h (r:=t+d) (e:=d) (by omega) (by omega) rfl
  exact hu

variable (q:Ferry P.run t (irr P j) (uvv P j))
abbrev trek (f:P.Test) := steeple P t j (nn P j) q.enters f -- auto include q ?
include q
lemma steepleCov (s:f∈bay K S true)(a:f∈enclave K):
    covariant (trek P t j q f) :=by
 suffices h:∀r (u:t≤r),r=nₖ→covariant (steeple P t j r u f) from h _ q.enters rfl
 intro r u
 obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le u
 rw [atSteeple]; intro e
 exact lofted P t j q.depth s a d e.le



lemma steeplePair (a:f∈bay K S true)(b:g∈bay K Z true)
   (e:Detached Λ P.width S Z)(o:Host Y H i₀ t (S∪ Z)) :
    trek P t j q (f*g) = trek P t j q f * trek P t j q g :=by
 suffices h:∀ r (u:t≤r),r=nₖ→steeple P t j r u (f*g)= steeple P t j r u f*steeple P t j r u g from h _ q.enters rfl
 intro r u
 obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le u
 rw [atSteeple,atSteeple,atSteeple]; intro x
 exact loft2 P t j q.depth a b e o d x.le

lemma steepleA (s:f∈bay K S true):
   AtSupport false (Satin.region (volumeAround Λ P.width (nₖ-t) S) (σ nₖ))
     (trek P t j q f) ∧
    rawE P t j f=Journey.compass Y i₀ k₀ nₖ (trek P t j q f):=by
 suffices h:∀r(u:t≤r), r=nₖ→AtSupport false (Satin.region (volumeAround Λ P.width (r-t) S) (σ r)) (steeple P t j r u f) ∧
    rawE P t j f=Journey.compass Y i₀ k₀ r (steeple P t j r u f) from h _ q.enters rfl
 intro r u
 obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le u
 rw [atSteeple,Nat.add_sub_cancel_left]; intro e
 exact loft P t j q.depth s d e.le


omit q
/-- Pure launch operand on one Pane only. -/
abbrev Mount := Evaluation ((side Y i₀) nₖ)
/-- Common regulator prescription at any m period side, one link,
terminal Beta option. -/
def launchAmp (P:Spine)(n:ℕ)(m:Side) (A:Evaluation (P.par.Ctor m n))(U:Pane (P.par.Ctor m n)):
    ℂ:= inner ℂ (Dial.mateK _) (acts (A U) (uniformDen P n m U))

abbrev gaugeμ := prior SU.group (More ((side Y i₀) nₖ))
abbrev bareA (A: Mount P j) := launchAmp P (nn P j) (mm P j) A
def num (A: Mount P j) :ℂ:= ∫z,bareA P j A z ∂ gaugeμ P j
def bareRead (A:Mount P j) := num P j A / num P j 1

lemma equation (A:Mount P j):
   bareA P j A = bareAmplitude Y i₀ k₀ A :=by
 unfold bareA launchAmp uniformDen
 ext
 rw [pivots];rfl

abbrev finTor(f:P.Test) : Mount P j:= diagMark (trek P t j q f)
def fits_at (B:Set Vantage)(X: Mount P j) :Prop :=
   ∃ S:Finset Cover, P.pinFoot (nn P j) S ⊆ B ∧
   AtSupport false (Satin.region S (σ nₖ)) (toMark X)


structure bare_equate (A:Mount P j)(v:ℂ) :Prop where
  norm_unit: num P j 1 ≠0
  integrable: Integrable (bareA P j A) (gaugeμ P j)
  price: v = bareRead P j A

include q
lemma bare_equates (f:P.Test):
    bare_equate P j (finTor P t j q f) (rawE P t j f):=by
 obtain ⟨L,w⟩:=findsBay _ f
 obtain ⟨a,b⟩:=steepleA P t j q w
 obtain ⟨c,u,x⟩:=compassIncome Y i₀ k₀ a.env q.depth
 refine ⟨?_,?_,?_⟩
 · unfold num; rw [equation]; exact u
 · rw [equation]; exact c
 · rw [b,x]; unfold bareRead num; rw [equation,equation]

lemma cProof (a:f∈enclave K):
   covariant (toMark (finTor P t j q f)):=by
 obtain ⟨L,w⟩:=findsBay _ f
 exact diag_cov (steepleCov P t j q w a)


lemma supports_f (s:f∈bay K S true):
   AtSupport false (Satin.region (volumeAround Λ P.width (nₖ-t) S)
     ((side Y i₀) nₖ)) (toMark (finTor P t j q f)) := diagAt (steepleA P t j q s).1

omit q
lemma through_product (t:ℕ)(f g:P.Test) (B C:Set Vantage)
    (a: ∃ S:Finset Cover,f∈bay K S true∧P.pinFoot t S⊆B)
    (b: ∃ S:Finset Cover,g∈bay K S true∧P.pinFoot t S⊆C)
    (d:Disjoint B C): 
    ∀ᶠ j in atTop, ∀q,finTor P t j q (f*g)
        = finTor P t j q f * finTor P t j q g :=by
 obtain ⟨S,a,c⟩:=a; obtain ⟨Z,b,l⟩:=b
 rw [P.usual_footprint] at c l
 have e:Detached Λ P.width S Z:=
    PhaseChoice.separatedPhys (show printedHere P.par P.width t S (handstamp _) from has_footprint P.par P.width t S)
    (show printedHere P.par P.width t Z (handstamp _) from has_footprint P.par P.width t Z)
    (Disjoint.preimage _ (d.mono c l))
 filter_upwards [(rising_i P).tendsto_atTop.eventually (eventually_host Y H t (S∪Z))] with j hj q
 unfold finTor
 rw [steeplePair P t j q a b e hj]; rfl


/-- Full billed physical footprints and a common nonalias certificate
for all the instruments at once at the top. -/
def Secure (t j:ℕ){ι:Type*}(B :ι→Set Vantage) (F:ι→Mount P j) :Prop:=
    ∃ R:Finset Cover,Host Y H (irr P j) t R ∧
      ∀ i,∃ S:Finset Cover, S ⊆ volumeAround Λ P.width (nn P j-t) R ∧
        P.pinFoot (nn P j) S ⊆ B i ∧
        AtSupport false (Satin.region S ((side Y (irr P j)) (nn P j)))
           (toMark (F i))

lemma secures (t:ℕ){ι:Type*} [Finite ι](B:ι→Set Vantage) (f:ι→P.Test)
   (h:∀i,∃S:Finset Cover,f i∈bay K S true∧P.pinFoot t S⊆B i):
    ∀ᶠ j in atTop,∀ q:Ferry P.run t (irr P j) (uvv P j),
     Secure P t j B (fun i=>finTor P t j q (f i)):=by
 choose S hs hf using h
 letI:=Fintype.ofFinite ι
 let R:= (Finset.univ:Finset ι).biUnion S
 filter_upwards [(rising_i P).tendsto_atTop.eventually (eventually_host Y H t R)] with j hj q
 exact ⟨R,hj,fun i=>⟨_,around_mono Λ P.width
    (show S i⊆R from fun x h=>mem_biUnion.mpr ⟨i,Finset.mem_univ _,h⟩) _,
    (P.pin_onward _ _ _ q.enters).trans (hf i),
    supports_f P t j q (hs i)⟩⟩

