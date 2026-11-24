import ZecaBlaze
import SatinThinResponse
set_option autoImplicit false
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn

namespace Spine

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid  Set




open scoped TensorProduct
variable (P:Spine)(x:P.Spectrum0 3)

local notation "κ"=>P.calibration
local notation "ℋ"=> P.PortionHil 3 x
local notation "ω"=> P.emptyV 3 x
local notation "T"=> P.Test
local notation "M"=> P.chairs 3 x
local notation "B"=> P.pith 3 x
local notation "S"=> P.straight 3
local notation "σ"=> P.shifts 3
local notation "U"=> P.TwinPort 3 x
local notation "V"=> P.Pome 3 x
local notation "µ"=> P.thinSplit x
local notation:max "ν" t:max=> P.singleState 3 t x

/-- Same x product price. All billing is at each consultation, never moving
 sector splits through the promotion of *prices*. -/
structure Lemon:Prop where
 history(t q:ℕ)(d:0<q)(f:P.Card 3 t q):
    M t q d (P.entryTest 3 t f) = P.stateSpace 3 x (P.atSide 3 t q d f)
 factors(t q:ℕ)(d:0<q)(f g:T)(h:S t q f)(p:S t q g)(e:PureGauge κ f)(v:PureMatter κ g):
    B t q d (f*g) = TensorProduct.mapL (M t q d f) (M t q d g)

 concat (t q n:ℕ)(d:0<q)(b:0<n)(f g:T)(h:S t q f)(p:S t n g):
    S t (q+n) (f*σ q g) ∧
    M t (q+n) (add_pos d b) (f*σ q g) = M t q d f * M t n b g ∧
    B t (q+n) (add_pos d b) (f*σ q g) = B t q d f * B t n b g
 reversal (t q:ℕ)(d:0<q)(f:T)(h:S t q f):
    let v:= aureole κ 3 (gaugeT κ q) f
    S t q v ∧ M t q d v= star (M t q d f) ∧
     ∀y z:U, inner ℂ (B t q d v y) z= inner ℂ y (B t q d f z)
 pearl (t q:ℕ)(d:0<q)(f:T)(h:S t q f):
    inner ℂ ω (M t q d f ω)=ν t f ∧
    inner ℂ V (B t q d f V)=µ t f

lemma lemon:P.Lemon x:=
 ⟨P.chairs_card 3 x,fun _ _ d f g _ _=>P.pithFactors _ x _ _ d f g,
  fun _ _ _ _ _ _ _ h k=>
   ⟨P.straight_cat _ _ _ _ _ _ h k,P.chairs_cat _ x _ _ _ _ _ _ _ h k,
     P.pith_cat _ x _ _ _ _ _ _ _ h k⟩,
  fun _ _ d _ p=> ⟨P.straight_ref _ _ _ _ p,P.chairs_adj _ x _ _ d _ p,P.pith_adj _ x _ _ d _ p⟩,

  fun t _ d f h=> ⟨P.chairs_pearl _ x _ _ d f h,P.shell_brief _ x _ _ d _
     (P.thin_comparator_LocalFieldBounds x t).1 f h⟩⟩

/-- decoupled column p-card price retains shifted actual as well. -/
def Rubs (t q:ℕ)(d:0<q)(u:ℤ)(f:T):Prop:=
  S t q (σ (-u) f) ∧
  inner ℂ ω (M t q d (σ (-u) f) ω)=ν t f ∧
  B t q d (σ (-u) f) = 0 ∧ µ t f=0
-- thinSplit is shift invariant? prove or μ t f zero separately via msplit. easier via general shift using Fubini. Prove shift via global illumined
lemma salt_invar (t:ℕ)(u:ℤ) : (µ t).comp (σ u).toLinearMap=µ t:=by
  have hp (f:T) (h:PureGauge κ f):PureGauge κ (σ u f) :=by rw [facade]; exact P.glowPure _ _ (P.glowPure _ _ h)
  have hm (f:T) (h:PureMatter κ f):PureMatter κ (σ u f) :=by rw [facade]; exact P.beamPure _ _ (P.beamPure _ _ h)
  apply P.thin_comparator_only
  have q:= (P.thin_comparator_LocalFieldBounds x t).1
  exact ⟨fun f g h v=>show µ t (σ u (f*g))=_ from by rw [map_mul,q.factors _ _ (hp f h) (hm g v)];rfl,
     fun f e=> (q.link _ (hp _ e)).trans (P.slide_single ..),
     fun f e=> (q.matter _ (hm _ e)).trans (P.slide_single ..)⟩

lemma rub (t q:ℕ)(d:0<q)(u:ℤ)(f:T)
   (h:S t q (σ (-u) f) ∧ B t q d (σ (-u) f)=0): P.Rubs x t q d u f:=by
 have v:µ t (σ (-u) f)=µ t f:=LinearMap.congr_fun (P.salt_invar x t (-u)) _
 have e: inner ℂ V ((0:P.PomeOp 3 x) V)=0:=by change inner ℂ V 0=0;exact inner_zero_right _
 have p:=(P.lemon x).pearl t q d _ h.1
 rw [h.2,e,v,P.slide_single] at p
 exact ⟨h.1,p.1,h.2,p.2.symm⟩


/-- Comparison license for a body at its buying pitch and every finer consultation.
All physically affordable windows, whole Point stamp on any positioned test at this
currency, thus buying the spacetime **zero field**, with no difficulties with
charges/amplification or unpadding. -/
structure Lull (t:ℕ)(D:P.Apron):Prop where
 calls (q:ℕ)(d:0<q)(u:ℤ)(k:Cover)(p:P.Lunette 3 t q u D (P.meshPose t k)):
    P.Rubs x t q d u (P.issuing t D k)
 smears (q:ℕ)(d:0<q)(u:ℤ)(F:SampleDose)
    (p:∀y∈tsupport F.val,P.Lunette 3 t q u D y):
    P.Rubs x t q d u (P.prepared t D F)
lemma luv (t:ℕ)(D:P.Apron){Q:Bool}(h:P.Sensor D Q)(d:D.s ≤ t): P.Lull x t D:=
 ⟨fun _ v u k p=> P.rub _ _ _ v u _ (P.shell_issued _ _ _ _ v u D Q h d k p),
  fun _ v u k p=> P.rub _ _ _ v u _ (P.shell_smear _ _ _ _ v u D Q h d k p)⟩

-- concat pair
variable (t q:ℕ)(d:0<q)(a b:P.Test)
local notation "Q"=> P.pith 3 x t q d
local notation "I"=> P.chairs 3 x t q d


def SoftRead :Prop:=
 P.Rubs x t q d (-(q:ℤ)) a ∧ P.Rubs x t q d 0 b ∧
 inner ℂ ω ((I (σ q a)* I b) ω) = ν t (a*b) ∧
 Q (σ q a) = 0 ∧ Q b=0 ∧
 inner ℂ V ((Q (σ q a)*Q b) V)=µ t (a*b) ∧ µ t (a*b)=0

lemma softRead (p:P.Rubs x t q d (-(q:ℤ)) a)(h:P.Rubs x t q d 0 b):
 P.SoftRead x t q d a b:=by
 refine ⟨p,h,?_⟩
 rw [Rubs,neg_neg] at p
 rw [Rubs,neg_zero,P.shifts_zero] at h
 obtain ⟨v,g,m⟩:= (P.lemon x).concat t q q d d _ _ p.1 h.1
 obtain ⟨c,l⟩:= (P.lemon x).pearl _ _ (add_pos d d) _ v
 have u:µ t (σ q (a*b))=µ t (a*b):=LinearMap.congr_fun (P.salt_invar x t q) _
 
 have cm:=c.trans ((congrArg (ν t) (map_mul (σ q) a b).symm).trans (P.slide_single 3 x t _ _))
 have lm:=l.trans ((congrArg (µ t) (map_mul (σ q) a b).symm).trans u)
 rw [m] at lm; rw [g] at cm
 refine ⟨cm,p.2.2.1,h.2.2.1,lm,?_⟩
 rw [←lm,h.2.2.1]
 have zero:Q (σ q a)*0=0:=mul_zero _
 rw [zero]; change inner ℂ V 0=0
 exact inner_zero_right _

