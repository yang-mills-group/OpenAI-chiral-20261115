import YM.SU5.Assay.StockFolio
import YM.SU5.Assay.WrapMix
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
variable {c:Option Bool}{a b x y:P.Test}
/-! The *prior* gauge/matter consultation now with narrow native formulas; see
`Reel.literal` for mark, `twistFolio` for component assignments. Entries
can be `0`, not testing pointwise nondegeneracy before billing. Positive joint
results require other tests/estimates. -/

variable (P)
def FirstDress (A:P.Apron)(W:Bool)(l:P.Folio):Prop:= A.Beams W∧P.Wove (some W) A.S A.F l
variable {P}
lemma FirstDress.kiss {l:P.Folio}{A:P.Apron}(u:P.FirstDress A W l)(j:Axis):P.FirstDress (A.kiss P j) W (l.transcribe (P.reflectTest j)):=
 ⟨u.1.kiss j,u.2.left j⟩
lemma FirstDress.call {l:P.Folio}{A:P.Apron}(J:P.Register)(u:P.FirstDress A W l)(x:P.Spectrum0 3):P.DressCall x A W l:=
 dressSpecific x _ _ u.1 (u.2.prepared') J

variable {j:Axis}{Z:Lead.Clan}
namespace Reel
variable (R:P.Reel j Z)(B:P.Glaze)(l:P.Folio)
local notation "Y"=>R.pressRoll
local notation "σ"=>P.shifts j
local notation "φ"=>P.defaultR Z R.n
local notation "aℓ"=>((P.defaultFolio Z R.n).ink R.a)
local notation "D₀" m:max => R.dusk B m

def rollFolio : P.Folio:= [(1,1)] ++ (aℓ).ink (-1)
def duskFolio : ℕ → P.Folio
 | 0=> l
 | m+1=>Folio.crossPrint (duskFolio m) (R.rollFolio.transcribe (σ ((D₀ m).bridge Y)))
def twistFolio : ℕ → P.Folio
 | 0=> []
 | m+1=>twistFolio m ++ ((aℓ).transcribe (σ ((D₀ m).bridge Y))).crossPrint (R.duskFolio B l m)

lemma tag_prices :P.Wove (some Z.2) (Y).S (R.a•φ) aℓ:= Wove.smul (P.flash_prices Z R.gap) _
lemma roll_prices :P.Wove none (Y).S (Y).F (R.rollFolio):=by
 change P.Wove _ _ (1-R.a•φ) _
 rw [show 1-R.a•φ=1+(-1:ℂ)•(R.a•φ) by rw [neg_one_smul,←sub_eq_add_neg]]
 exact Wove.staple (Wove.tuft Yarn.unit') ((tag_prices R).void'.smul _)

lemma dusk_prices (p:P.Wove none B.S B.F l)(m:ℕ) :P.Wove none (D₀ m).S (D₀ m).F (R.duskFolio B l m):=by
 induction m with
 | zero=>exact p
 | succ m h=> exact h.joint ((roll_prices R).slide j ((D₀ m).bridge Y)) (P.pin_disjoint _ _ _ ((D₀ m).distancePin Y j 0))
lemma twist_prices (p:P.Wove none B.S B.F l)(m:ℕ) :P.Wove (some Z.2) (R.twist B m).S (R.twist B m).F (R.twistFolio B l m):=by
 induction m with
 | zero=> change P.Wove _ B.S (B.F-B.F) [];rw [sub_self];exact Wove.zilch
 | succ m h=>
    let V:=D₀ m; let d:=V.bridge Y; let S:=plow K j d (Y).S; let n:=(aℓ).transcribe (σ d)
    have e:=R.dusk_prices B l p m
    have k:P.Wove (some Z.2) (V.S∪S) ((σ d (R.a•φ)) * V.F) (n.crossPrint (R.duskFolio B l m)):= by
       rw [Finset.union_comm]
       exact ((tag_prices R).slide j d).joint e (P.pin_disjoint _ _ _ ((D₀ m).distancePin Y j 0)).symm
    change P.Wove _ (V.S∪S) (B.F - V.F * σ d (1-R.a•φ)) _
    have hx:B.F - V.F * σ d (1-R.a•φ)=(B.F-V.F)+ (σ d (R.a•φ))*V.F:=by
       rw [map_sub,map_one,mul_sub,mul_one,mul_comm]; abel
    rw [hx]
    exact Wove.staple (h.mono Finset.subset_union_left) k
lemma twist_first (p:P.Wove none B.S B.F l)(s m:ℕ):P.FirstDress ((R.twist B m).apron s) Z.2 (R.twistFolio B l m):=
 ⟨R.dressed B s m,R.twist_prices B l p m⟩
end Reel
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
