import SU5SatinVerifiedNovember6
import YM.SatinExist.Canope
import YM.SatinExist.Excelsior
import YM.SatinExist.Loure
import YM.SatinExist.Split
/-! # Unpad actual 36 readings. SOT operator fields and comparison price. 
Include $E4bridge$ now with exactly this operator algebra bought. NOT claiming
rotations or localization or that the proposed split pays on the fields (instead give ambiguity result).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 460000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry TopologicalSpace
namespace Spine
open Aria Casting
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld LineDeriv
open _root_.YM.Boundary Spectral Poin
local notation "j"=> (3:Axis)
open SatinTails SatinJets Ballad
variable (P:Spine) (x:P.Spectrum0 3) (A:ℕ→P.Apron) (N:P.PowerNames x A)
local notation "ξ"=>P.advocate 3 x j
local notation "CX"=> P.ManyF j (P.advocate 3 x j)
local notation "ν"=> P.seasons j (P.advocate 3 x j)
local notation "λ'"=> P.ColorHil j (P.advocate 3 x j)
local notation "ω"=> P.heaven j (P.advocate 3 x j)
local notation "Φ"=> Bench (P.seasons j (P.advocate 3 x j))
variable (c r n:ℕ→ℕ)(w:Lead.Clan→Prism)
inductive OperaK
 | mid (l: List Axis)
 | probe (z:Lead.Clan) (flip:Bool)
 deriving Inhabited
abbrev heightX : OperaK → ℕ
 | .mid l=> N.rate 3 l
 | .probe z _=> P.heightPA x A N w z
def operaAt(b:Bool) (i:ℕ) : OperaK→ P.Apron
 | .mid l => (A i).pivot P l
 | .probe z v=> let f:= if b then P.bareTwin A w z i else P.soldTrumpet A c r n w z i; if v then (f.kiss P j) else f
noncomputable def eP : OperaK → (CX).Op
 | .mid l => N.fields 3 l
 | .probe z v=> if v then star (P.legR x A N z w) else P.legR x A N z w
local notation "r'"=>P.heightX x A N w
local notation "D" =>P.eP x A N w
abbrev ΩBills (k:OperaK)(f:Test4): Φ →ₗ[ℂ] Φ:=ℑ (ν) (P.eP x A N w k) f (P.heightX x A N w k)
local notation "W"=> P.ΩBills x A N w
lemma postcards (g:P.LargeM c r)(T:P.Snapdragon x c r A n)(u:StrictMono c) (b:Bool) (k:OperaK): P.Concerto x (fun i=> P.operaAt A c r n w b i k) (r' k) (D k):=by
 cases k with
 | mid l=>
   let t:= N.price j l
   let C (i:ℕ):= (A i).pivot P l
   have h:Tendsto (fun i=>P.zt (C i)) atTop (𝓝 0):=by apply NNReal.tendsto_coe.mp; simp_rw [P.bookRig]; exact t.prices.thin
   refine ⟨h,P.height_of_width C 3 t.prices.thin,fun i hi=>?_⟩
   have hv:=t.prices.paid i hi; rw [N.paid j l i hi] at hv; simp_rw [one_smul] at hv; unfold plated; rw [Real.toNNReal_coe]; exact hv
 | probe z p=>
   have he:= P.rotorPrice x A N z c r n w T g u
   have ht:= P.twin_alias x A N z w
   cases b <;> cases p
   exact he
   exact (Concerto.kissPrice P x _ _ _ he)
   exact ht
   exact (Concerto.kissPrice P x _ _ _ ht)
-- notably P independent audience-mix scheduled before width; records both price exact and $ℱ_alias$.
abbrev venueLeg (k:Lead.Clan)(f:Test4):=∑ i∈(w k).support,(w k i) • ℑ (ν) (P.weightL x A N k) (((-(εpref (3:Axis)): Test4→L[ℂ] Test4)^[i+1]) f) (N.rate 3 [])
variable (H: P.HandleWith x c r A n)(F G:SampleDose) (V':∀ i:Axis,List Axis→ℝ→ P.ColorHil i (P.advocate 3 x i))
variable {f s κ ℓ:ℕ}{R:P.Register} (Q:P.FullPrismLab x A c r n w V' f s H 1 F G reviewEarlierBox reviewLaterBox κ ℓ R)
variable (Y':Lead.Clan→ VacuumVector (P.ManyF 3 (P.advocate 3 x 3)))
structure PriceCert (J:P.Ellis 3 x) (Q:P.FullPrismLab x A c r n w V' f s H 1 F G reviewEarlierBox reviewLaterBox κ ℓ R):Prop where
 bridge : P.E4bridge F G x V' w A c r n H Y'
 pinned(z:Lead.Clan)(f:Test4) : Y' z f= (P.ΩBills x A N w (.probe z false) f (P.Asp x j)).val
 axis(f:Test4)(k:OperaK)(v:E4)(y:Bench (P.seasons j (P.advocate 3 x j))) :
   CF.Buffered.Afterglow.Hierarchy.Seld.usher (ν) v (W k f y)= W k (Probe.ahead v f) (CF.Buffered.Afterglow.Hierarchy.Seld.usher (ν) v y)
 pays (k:OperaK)(y:Bench (P.seasons j (P.advocate 3 x j))): Continuous (fun f:Test4=> (P.ΩBills x A N w k f y).val)
 localOrder (k:Lead.Clan)(f:Test4): P.ΩBills x A N w (.probe k false) f=P.venueLeg x A N w k f
 stampGoal (b:Bool)(k:OperaK) : Concerto P x (fun i=> P.operaAt A c r n w b i k) (P.heightX x A N w k) (P.eP x A N w k)
 moments (b:ℕ)(f:Fin b→OperaK)(T:Fin b→Bool) : P.Origami x (fun i k=> P.operaAt A c r n w (T k) i (f k)) ((P.eP x A N w)∘ f) ((P.heightX x A N w)∘f) (P.juryW x ((P.eP x A N w)∘f) ((P.heightX x A N w)∘ f)) J
 obstruction : P.TwinSensitivity x A c r n w V' f s H F G Q
-- includes the two contrasting outcomes of the product calculation: exactly this height proof uses the previous.CP.
lemma earns_prizes (J:P.Ellis 3 x) (g:P.LargeM c r)(T:P.Snapdragon x c r A n)(u:StrictMono c)(p:∀ i,Six.PureGauge P.calibration (A i).F)(h:P.PolynomialControl w (V:=V')) :
    ∃ Y',P.PriceCert x A N c r n w H F G V' Y' J Q:=by
 obtain ⟨Y',b⟩:= P.bridge_from_costs F G x V' w h Q
 let C:= P.postcards x A N c r n w g T u
 refine ⟨Y',b,fun z f=> P.groundRender x A N z c r n w T Q b g u f, fun f k v y=> CF.Buffered.Afterglow.Hierarchy.Seld.attends .., fun k y=> singular (ν) (D k) y (r' k),fun k f=> P.conduit_rule x _ _ _ f,C,fun B f t=> P.bound_jury x (fun i k=> P.operaAt A c r n w (t k) i (f k)) _ _ (fun i=> C (t i) (f i)) J, priceTwinSensitivity P x A c r n w V' f s H F G J p Q⟩
end Spine
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six Ballad DoseTravel Set Prototype
open Regis.Head Regis.Head.Brecht
open SatinJets
-- public
theorem vacuum_probe_reading :
    let Ω':Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
    ∃ (P:Spine) (K:P.Register), uniform P K Ω' 1 1 ∧ EpochPair P ∧ Defer P.par ∧ P.Roster ∧
    (∀ i k:ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta=P.par.x) ∧
    ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3)(R:P.Ellis 3 x), id ≤ r ∧ Experiment P K c r x R ∧
    P.Transmission x c r ∧
    (∀ (U V:Doorway)(order:Orders),U.Later V order 0 →∀ᶠ i:ℕ in atTop,∃ (a:ℝ)(F G:SampleDose),F.Normalized∧G.Normalized ∧ tsupport F.val⊆ U.invites ∧ tsupport G.val⊆ V.invites ∧
        P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G) ∧
    ∃ (i₀:ℕ)(F G:SampleDose), F.Normalized∧G.Normalized ∧ tsupport F.val⊆ reviewEarlierBox.invites ∧ tsupport G.val⊆ reviewLaterBox.invites ∧
        P.ReturnsSix x (c i₀) (r i₀) 0 F G ∧ P.FixedSatinReadings K x (c i₀) (r i₀) 0 F G ∧
    ∃ (f s:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x f s v a q u) n) (p:Lead.Clan→ SatinJets.Prism),
       ∃ T:P.FullPrismLab x (P.cinema x f s v a q u) c r n p V f s X 1 F G reviewEarlierBox reviewLaterBox (c i₀) (r i₀) K,
       (∃ A'∈reviewEarlierBox.invites, ∃ B'∈ reviewLaterBox.invites,P.UsesReproof x (P.cinema x f s v a q u) c r n p V f s X F G (c i₀) (r i₀) K A' B') ∧
       P.PolynomialControl p (V:=V) ∧ P.ThermalBid x f s v a ∧
       (∀ᶠ i:ℕ in atTop,∀ t:ℕ, c (n i) ≤ t→ P.SimultaneousDisclosure x (P.cinema x f s v a q u) c r n p F G i t) ∧
       let A:= P.cinema x f s v a q u
       ∃ N:P.PowerNames x A,(∀ j',(N.Costs P x A j') ∧ ∃ W',MomentWhere P x A j' N W') ∧ ∃ Y', P.PriceCert x A N c r n p X F G V Y' R T := by
 intro Ω'
 obtain ⟨P,K,p,h,k,m,q,c,r,x,R,z,g,C,V,hg,i,F,G,A,B,l,d,b,e,f,s,v,a,u,X₁,W,n,X,w,t,t₁,h1,h2,h3,U,D⟩:=diva_pricedSnap
 let A':=P.cinema x f s v a X₁ u
 obtain ⟨N⟩:= P.naming x A' U
 exact ⟨P,K,p,h,k,m,q,c,r,x,R,z,C,V,hg,i,F,G,A,B,l,d,b,e,f,s,v,a,u,X₁,W,n,X,w,t₁,h1,h2,h3,D,N,(fun j=>⟨N.kudos P x _ j,N.named P x _ j⟩),P.earns_prizes x A' N c r n w X F G W t₁ R g t C.launch.smaller (fun i=> P.cinema_pure ..) h2⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.vacuum_probe_reading
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.vacuum_probe_reading
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.postcards
