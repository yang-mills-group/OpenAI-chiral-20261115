import SU5SatinVerifiedNovember6
import ZecaPromise
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
open MacroGrid SatinNucleus SatinJets

variable (P:Spine){K:P.Register}{c r:ℕ→ℕ}(x:P.Spectrum0 3){R:P.Ellis 3 x}{i₀:ℕ}{F U:SampleDose}
 {A:ℕ→P.Apron}{n:ℕ→ℕ}{w:Lead.Clan→Prism}
 {V:∀ j:Axis,List Axis→ℝ→P.ColorHil j (P.advocate 3 x j)}
 {g h:ℕ}{X:P.HandleWith x c r A n}{D:P.Cilium x}



local notation "ξ"=>P.advocate 3 x 3
local notation "S"=>P.seasons 3 ξ
local notation "G"=>P.ManyF 3 ξ
local notation "ε"=>P.physicalEnergy 3 ξ
local notation "Ω"=>P.heaven 3 ξ
local notation "ν"=>P.nv 3 ξ
local notation "E"=>(P.seasons 3 ξ).E
open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola M)

open DoseTravel Set

local notation "MH"=> Hierarchy.Seld.Zeca.Moment

open Hierarchy.Seld.Poin Hierarchy.Seld.Zeca.Monument
open Boundary

/--
WHAT ONE VACUUM AND ONE THIN EXPERIMENT PAY after REMOVING padding.
Respect the CP18 split-by-species prescription (including inside the local
measurements); no claim against arbitrary in-theory redictionary or
coincidence counterterms. Includes BOTH Wick price and Mink W-product
contrast (never assuming they coincide, both stay nonzero). Builds actual
point fields, translation-covariant cyclic Mink reconstruction, G,H
estimates inc. spatial-copy (UV elections), etc. BEFORE rotations. Only
'countIf' and 'beamIf' are conditional, NOT a claim to have achieved
spacelike locality/relativity.
-/
structure Priced
 (P:Spine)(K:P.Register)(c r:ℕ→ℕ)
   (x:P.Spectrum0 3) (R : P.Ellis 3 x) (i₀:ℕ)(F U:SampleDose)
   (A:ℕ→P.Apron) (n:ℕ→ℕ)(w:Lead.Clan→Prism)
   (V : ∀j:Axis,List Axis→ℝ→P.ColorHil j (P.advocate 3 x j))
   (g h:ℕ)(X : P.HandleWith x c r A n)(D:P.Cilium x):Prop where
 signals: P.Shell K c r x R i₀ F U A n w V g h X D
 resolve:P.Honey x D F U (P.soldTrumpet A c r n w)
 comparing:P.Zest c r x F U A n w
 extension:∃B Z seq sc, P.Origin x c r F U A n w g h D B Z seq sc
 -- Counting criterion (angular W-quality estimate on all strict config prices)

 countIf:∀(ι:Type)(N:P.Tent x ι)(a:N.Chip),
    N.Tile (P.seasons 3 (P.advocate 3 x 3)) (P.nv 3 (P.advocate 3 x 3)) →
    (∀ t:N.Chip,∃Y,P.Bought 3 (P.advocate 3 x 3) (letter N t) Y) →
    P.Bought 3 (P.advocate 3 x 3) (letter N a) A →
    ∃ V d,P.Board x N D F U V d
 -- Archon application (estimate on raw charges)
 beamIf:∀ (ι:Type)(N:P.Tent x ι)(T:P.Shiver x N)
           (Y:N.Chip→ℕ→P.Apron)(a:N.Chip)(b:Gilt.Regime),
    P.Coronation x N T Y a b A →
    ∃ V d,P.Board x N D F U V d

lemma concurrent
 (p:P.Shell K c r x R i₀ F U A n w V g h X D)
 {W:P.Flotsam}(e:P.Custard W)(q:P.Froth x g h A W):
 P.Priced K c r x R i₀ F U A n w V g h X D:=by
 refine ⟨p,
        framed_LocalFieldBounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p,
        zest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p,
        P.orchard x e p q,
        fun _ N a d=>P.Peg x N p d a,
        fun _ N T Y a b=> P.ruby_claim x N T Y a b p⟩
#print Priced
#print axioms concurrent

/--
Main unconditional partial result. See 'Priced'.
Includes the **entire type** of exists_disclosed_satin_native_contrast
(on the displayed witnesses: see signals.scores.native).
This strengthens the election proof; need not hold for arbitrary witnesses
satisfying that type.
-/
theorem exists_satin_priced :
 ∃ (P:Spine) (K:P.Register) (c r:ℕ→ℕ)
   (x:P.Spectrum0 3) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose)
   (A:ℕ→P.Apron) (n:ℕ→ℕ) (w:Lead.Clan→Prism)
   (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
   (g h : ℕ) (X : P.HandleWith x c r A n)(D:P.Cilium x),
    P.Priced K c r x R i₀ F U A n w V g h X D:=by
 obtain ⟨P,K,c,r,x,R,i,F,U,A,n,w,V,g,h,X,D,s,_,p,t⟩:=exists_satin_puffin
 exact ⟨P,K,c,r,x,R,i,F,U,A,n,w,V,g,h,X,D,P.concurrent x s p t⟩

-- applies to points of the unconditional conclusions
#print axioms bare_chiral
#print axioms bare_density
#print axioms six_families
#print axioms any_quote
#print axioms fullPrism_azure_common_boxes
#check @exists_satin_priced
#print axioms exists_satin_priced
