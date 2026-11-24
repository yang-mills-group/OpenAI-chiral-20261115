import GaugeFieldConstruction.Balala
import GaugeFieldConstruction.Minoa
import GaugeFieldConstruction.Canna
import GaugeFieldConstruction.Virago
import GaugeFieldConstruction.Esther
import GaugeFieldConstruction.Polder
import GaugeFieldConstruction.Sotto
import GaugeFieldConstruction.Soapstone
set_option autoImplicit false
set_option maxRecDepth 1300
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 180000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {k:Side}{d:ℕ}{x y:Cover}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h r:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
-- θ.Ship manifestation $pR`. Tick frame transport from **fixed** Reifier to any actual $l$.
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts YM.GaugeFieldConstruction
local notation "Sp"=>Cauchy.Spin
open scoped Kronecker
namespace Violets
open ArtCart Simmer Py.Rate.LocalLimit.Papal.FrameP
open ArtCart Simmer Py.Rate.LocalLimit.Papal.FrameP
open Spectrix Gleam.Guide.Prims -- namespace tune
variable {O: Type} [NormedAddCommGroup O][InnerProductSpace ℝ O][MeasurableSpace O][BorelSpace O][FiniteDimensional ℝ O]
abbrev Seco (n k: Side)(x:Cover)(f:StampSet n x→ O)(M: Male)(F:Paper n)(U:Genre): O→ FC (Single k):= match U with
| .pure=> WinF n k x M F
| .gauge=> WinG n k x f F
| .mixed=> WinX n k x M f F
abbrev debris (n k:Side)(x:Cover)(f:StampSet n x→ O)(M:Male)(F:Paper n)(U:Genre):ℂ := match U with
| .pure=>Ffee n k x M F
| .gauge=>gFee n x f F
| .mixed=>0
variable (f: StampSet n x→ O) (U:Genre)
lemma spore (p:F∈Glamor (Θk n x) U r)(w:300<n.val)(hK:Kea.Pad 4 k): Wraw n k x f U F = Seco n k x f M F U + debris n k x f M F U • (1:O→FC (Single k)):=by cases U; exact P2U n k x M f F p w; simp only [Seco,debris,zero_smul,add_zero]; exact P3U n k x M f F p w hK; exact P1U n k x f F p w
local notation "P"=>boardC k 4 M
local notation "A"=>pinShift k 4 M
local notation "B"=>pinBack k 4 M
local notation "Lʰ"=> Wraw n k x f U F
local notation "Oκ"=>Seco n k x f M F U
variable {u:Wave (Single k)}
lemma octα (U:Genre): Solid (Single k) O (Seco n k x f M F U):=by cases U; exact WF_cap ..; exact WX_cap ..; exact WG_cap ..
lemma octβ (U:Genre)(g:Kea.Pad 4 k)(v:Sea P u): Panel P A B u (Seco n k x f M F U)=0:=by cases U; exact FKω _ k _ M g v F; exact XKω n k _ M _ g v F; exact GKω n k x M _ g v F
lemma treα (g:Kea.Pad 4 k)(v:Sea P u)(p:F∈Glamor (Θk n x) U r)(w:300<n.val): Solid (Single k) O (Wraw n k x f U F) ∧ Panel P A B u (Wraw n k x f U F)=debris n k x f M F U:=by
 let S:= Seco n k x f M F U; let c:=debris n k x f M F U; let G:= (1:O→ FC (Single k)); have hf:Solid (Single k) O G:=Solid.major _; have hv:= octα (k:=k) (F:=F) M f U
 rw [spore M f U p w g]; refine ⟨hv.double (hf.scaler _),?_⟩ -- order M then f
 rw [spine_c hv (hf.scaler _),octβ M f U g v,spine_s]; change 0 + c*Panel P A B u G=c
 rw [show Panel P A B u G=1 from ?_,zero_add,mul_one]; unfold Panel; simp_rw [show ∀ x:O,Worthy P A B u (G x)=1 from fun _=>cΩ (token_V g (by decide) _) (baseP g _) v]; simp
-- Tags absolute gauges are face sites (ordinary); tβ orientation Eu.Second. price tables separate slots cross.
abbrev Wα :Type:= Cover × PlaqAxes × SU.group.ColorIndex
abbrev Wφ :Type:= Cover × Sp ×SU.Slot
def Wasp (n:Side)(x:Cover)(t:StampSet n x): Wα:= (LiftSeat (cT:=n) x t,t.1.val.2,t.2)
def Wry (x:Cover)(i:ArcK x):Wφ:= (i.1.val,i.2)
-- simpler G:G2 stored pair via function Shx
abbrev ShapeZ (n:Side)(x:Cover)(U:Genre):Type:= match U with
| .gauge=> Shx n x
| .pure=> ArcK x × ArcK x
| .mixed=> (ArcK x × (ArcK x × StampSet n x))
instance (n:Side)(x:Cover)(U:Genre):Fintype (ShapeZ n x U):=match U with
| .gauge=> inferInstanceAs (Fintype (Shx n x))
| .pure=> by unfold ShapeZ; infer_instance
| .mixed=> by unfold ShapeZ; infer_instance -- non-instance tuning
-- expression
inductive Chip
| litt (i j:Wα)
| cuff (i j:Wφ)
| creel (f:Wα)(i j:Wφ)
def Chip.nox : Chip→ Bool
| .creel ..=>false
| _=> true
def CrispC (F:Paper n)(x:Cover)(G:Genre): ShapeZ n x G →ℂ:=match G with
| .gauge=> guc n x F
| .pure=>fun ⟨i,j⟩=> SipF n x F i j
| .mixed=>fun ⟨i,j,k⟩=> SipeQ n x F k i j

def ChipUp (n:Side)(x:Cover)(G:Genre): ShapeZ n x G → Chip := match G with
| .gauge=> fun i=>Chip.litt (Wasp n x (i 0)) (Wasp n x (i 1))
| .pure=> fun ⟨i,j⟩=>Chip.cuff (Wry x i) (Wry x j)
| .mixed=> fun ⟨i,j,k⟩=>Chip.creel (Wasp n x k) (Wry x i) (Wry x j)

def SellChip (f:StampSet n x→ O)(G:Genre): ShapeZ n x G → (O→ FC (Single k)):= match G with
| .gauge=>fun z=> Gn (f (z 0)) (f (z 1))
| .pure=>fun ⟨i,j⟩=> Fta k x M i j
| .mixed=>fun ⟨i,j,t⟩=> Xta n k x M f t i j
-- M auto k implicit? check
lemma solidChip (G:Genre)(z:ShapeZ n x G) : Solid (Single k) O (SellChip M f G z):=by cases G; exact (FN_S ..).scaler _; exact (XN_S ..).scaler _; exact Gn_S ..
lemma summary (G:Genre):Seco n k x f M F G=(∑ i:ShapeZ n x G,CrispC F x G i • SellChip M f G i):=by
 cases G with
 | gauge=> rfl
 | pure=>
    unfold CrispC SellChip; change _= ∑ i:ArcK x × ArcK x,SipF _ _ F i.1 i.2 • Fta _ x M i.1 i.2; rw [Fintype.sum_prod_type]; rfl -- tune universe
 | mixed=>
    unfold CrispC SellChip; change _=∑ i:ArcK x × ArcK x × StampSet n x, SipeQ _ _ F i.2.2 i.1 i.2.1 • Xta n k x M f i.2.2 i.1 i.2.1; simp_rw [Fintype.sum_prod_type (α₁:=ArcK x)]; try rfl
-- absolute realization.loop
variable (k)
def sewC (i j:Wφ): Seated (Tset k):= by
 let x:=κR k false i.2.1 i.2.2 i.1; let y:=κR k true j.2.1 j.2.2 j.1; exact ⟨x,y, (κv x).2 (slotA _|>.1), fun u=> (slotA j.2.1).2 ((κv y).1 u) ⟩
def seamK (i j:Wφ) := tagR k i.1 * tagR k j.1
def HotG (f:Wα→O) : Chip → (O→ FC (Single k))
| .litt i j=>Gn (f i) (f j)
| .cuff i j=> seamK k i j • FN O P A B (sewC k i j)
| .creel g i j=> seamK k i j • XN P A B (f g) (sewC k i j)
lemma ascentC (f:Wα→ O)(G:Genre)(i:ShapeZ n x G): SellChip (k:=k) M (f ∘ Wasp n x) G i=HotG k M f (ChipUp n x G i):=by cases G <;> rfl
abbrev Pcω (i j:Wφ):ℂ:= seamK k i j * Pacts.QueenP P A B (sewC k i j) (sewC k i j) -- M notation? binder hygiene tune
lemma Pc_one (i j s t:Wφ): Pacts.QueenP P A B (sewC k i j) (sewC k s t)= Pacts.QueenP P A B (sewC k i t) (sewC k i t):=rfl
-- bills standard orientation first
variable (κ:Wα→Wα→ℂ)(μ:Wφ→Wφ→ℂ)
def Chip.budget2 : Chip→ Chip→ℂ
| .litt i j,.litt a b => P2Γ κ i j a b
| .cuff i j,.cuff a b => -(μ i b * μ a j)
| .creel f i j,.creel g a b => -(μ i b * μ a j)* κ f g
| _,_=>0
abbrev Δρ (i j a b r t:Wφ):ℂ:= μ i b*μ a t*μ r j+ μ i t*μ r b*μ a j
def Chip.budget3: Chip→Chip→Chip→ℂ
| .litt i j,.litt a b,.litt c d=> T2Γ κ i j a b c d
| .cuff i j,.cuff a b,.cuff r t=> Δρ μ i j a b r t
| .litt i j,.creel k a b,.creel m c d=> -(μ a d * μ c b)* P2Γ κ i j k m
| .cuff i j,.creel k a b,.creel m r t=>Δρ μ i j a b r t * κ k m
| _,_,_=>0
-- pay expansion with signs moved. specialize rewrite lemmas
lemma ωSpin (r:ℂ)(A2 B2:O→FC (Single k)): A2*(r • B2)= r •(A2*B2):=by ext1 i; change A2 i*(r • B2 i)=r • (A2 i* B2 i); rw [Matrix.mul_smul]
lemma ωCast (r:ℂ)(A2 B2:O→ FC (Single k)):(r • A2)*B2=r •(A2*B2):=by ext1 i; change (r • A2 i)*B2 i=r • (A2 i*B2 i); rw [Matrix.smul_mul]
lemma piΩ (k:Side)(M:Male)(i j s t:Wφ): Pacts.QueenP (boardC k 4 M) (pinShift k 4 M) (pinBack k 4 M) (sewC k i j) (sewC k s t)= (pinT k M) (κR k true t.2.1 t.2.2 t.1) (κR k false i.2.1 i.2.2 i.1):=rfl
lemma due2 (f:Wα→ O)(g:Kea.Pad 4 k)(v:Sea P u)(i j:Chip): Panel P A B u (HotG k M f i * HotG k M f j)= Chip.budget2 (fun i j=> papaya (f i) (f j)) (Pcω k M) i j:=by
 have h0:=token_V g (by decide) M; have h1:=baseP g M
 cases i <;>cases j <;>simp only [HotG, Chip.budget2, ωSpin, ωCast, spine_s,AversGG h0 h1 v,AversGF h0 h1 v, AversGX h0 h1 v,AversFG h0 h1 v,AversFF h0 h1 v,AversFX h0 h1 v,AversXG h0 h1 v,AversXF h0 h1 v,AversXX h0 h1 v,mul_zero, P2Γ] <;> try (simp only [Pcω,seamK, piΩ]; ring) -- tune noProgress
-- generated
lemma due3 (f:Wα→ O)(g: Kea.Pad 4 k)(v:Sea P u)(i j w:Chip)(p:i.nox=true): Panel P A B u (HotG k M f i *HotG k M f j * HotG k M f w) = Chip.budget3 (fun i j=> papaya (f i) (f j)) (Pcω k M) i j w:=by
 have h0:=token_V g (by decide) M; have h1:=baseP g M
 cases i<;> cases j <;>cases w <;> (first|contradiction| (solve | simp [Chip.nox] at p) | (simp only [HotG,Chip.budget3, ωSpin,ωCast,spine_s, AversGGG h0 h1 v, AversGGF h0 h1 v, AversGGX h0 h1 v, AversGFG h0 h1 v, AversGFF h0 h1 v, AversGFX h0 h1 v, AversGXG h0 h1 v, AversGXF h0 h1 v, AversGXX h0 h1 v, AversFGG h0 h1 v, AversFGF h0 h1 v, AversFGX h0 h1 v, AversFFG h0 h1 v, AversFFF h0 h1 v, AversFFX h0 h1 v, AversFXG h0 h1 v, AversFXF h0 h1 v, AversFXX h0 h1 v, mul_zero,T2Γ,P2Γ] <;> try (simp only [Δρ,Pcω,seamK,piΩ]; ring)))
#print axioms due3
end Violets
end ArtCart
end MastTin
end YM.CF.XGarden
end
