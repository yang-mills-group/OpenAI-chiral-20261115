import YM.CF.DPress.Yarn.Retention
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Thrift RoomF
variable {F: RoomF J Λ M Δ}(D:Crib F n)
namespace Crib
open Silo
local notation "jS" j:max=> Dh V M B (n-1-j) j
local notation "jA" j:max=> cell M B R.L j
local notation "jO" j:max=> Λ.O (hat R.L x j)
local notation "jC" j:max=> Tew.tiny R (hat R.L x j)
local notation "Xt" j:max=> venue D j
open Chaff Gloss Maize Tye RP RP.Str Brace
open Source
variable {T : Source P_ J}{Jp:ℕ→ℝ→ℝ}
open Cap
local notation "hx'"=> hat R.L x
local notation "U♥"=> StarPS n
variable (Y:StarPS n)(hk:Beacon T F n Jp k)
local notation "β0" j:max=> BQ (k:=k) D Y j
local notation "Q1" => Jp
local notation "r_K"=> D.radiusX hk
local notation "GN" j:max=> apt M B R.L j
local notation "NeedY"=> need (k:=k) (Jp:=Jp) D
local instance : Nonempty (StarPS n):=⟨⟨0,by rw [norm_zero]; exact zero_le_one⟩⟩
-- n≥ k. Seal.Aux FP
local notation "heightK" c:max=>δv (x:=x) (R:=R) c
lemma Nomination (X:LogH (cell M B R.L n))(t: NeedY n X):∃ (Z:StarPS n)(Y':VestM M B R),Y' n=X ∧(∀ i,k ≤ i→ i ≤ n→ NeedY i (Y' i)) ∧(∀ i,k ≤ i → i<n → Contract D i (D.radiusX hk i) (BQ (k:=k) D Y (i+1) Z) (Y' (i+1)) (Y' i) (True) ∧ BQ (k:=k) D Y (i+1) Z+D.toll i-(Y' i).δ = BQ (k:=k) D Y i Z):=by
 let P(i:ℕ)(y:StarPS n→LogH (cell M B R.L i)):Prop:= Coast y ∧∀ z:U♥, NeedY i (y z)
 let Q(i:ℕ)(X':StarPS n→LogH (cell M B R.L (i+1)))(Y':StarPS n→LogH (cell M B R.L i)): Prop:=∀ c:U♥, Contract D i (D.radiusX hk i) (BQ (k:=k) D Y (i+1) c) (X' c) (Y' c) ((Y' c).r=OrbT D hk i c)
 let τ:StarPS n→LogH (cell M B R.L n):=fun _=> X
 have h:= hk.h; obtain ⟨y,s,q,o⟩:= LogH.book _ k n (by omega) P Q τ (show P n τ from ⟨coast_const _,fun _=> t⟩) (fun i r p v (g:P (i+1) v)=> by obtain ⟨y,h,u⟩:= curtain D Y hk v g.1 ⟨r,p⟩ g.2; exact ⟨y,⟨h,fun j=>(u j).1⟩,fun j=>(u j).2⟩ ); let K0(c:U♥)(i:ℕ):= (y i c).δ; let Ra(c:U♥)(i:ℕ):=(y i c).r
 have g: Cap.Clk (σmove (R:=R) (x:=x)) (D.radiusX hk) K0 Ra (fun i=> k≤ i):= ⟨fun i t g=>⟨D.σcoin _,(q i g t.le).1.β,fun j=>(o i g t j).rent⟩,fun i v p=>⟨D.borrow_r hk,(q i p v.le).1.sig,fun j=>(o i p v j).rank⟩⟩ -- implicit i/j
 obtain ⟨c,t'⟩:= Cap.sit _ _ _ _ g; refine ⟨c,fun i=> y i c,congrFun s c, fun i t p=>(q i t p).2 c,?_⟩; intro i p g; let t:=o i p g c; have hw:(y i c).r=OrbT D hk i c:=(t' i p g).2.symm
 refine ⟨⟨t.rent,t.rank,fun i _=>t.pay i hw⟩,?_⟩; change _-(y i c).δ=_; rw [← (show (heightK c) i=(y i c).δ from (t' i p g).1),D.grow Y c p,add_sub_cancel_right] -- syntax `.grow` arg order
-- scope. for Chess up.Zloc. summary
abbrev bent (X: StarPS n) (L:VestM M B R) (i:ℕ) :=render D i (L i) (BQ (k:=k) D Y i X)
structure Campaign (X: StarPS n)(Q: VestM M B R) :Prop where
 fire : ∃ (v:RegBudget (cell M B R.L n))(z:ℝ), Q n=νhead (n:=n) (M:=M) (B:=B) (R:=R) v z∧ Lendc (F:=F) (n:=n) T v z
 ware : ∀ i,k ≤ i→ i ≤ n→ NeedY i (Q i)
 stairs : ∀ i,k ≤ i → i<n→ Contract D i (D.radiusX hk i) (BQ (k:=k) D Y (i+1) X) (Q (i+1)) (Q i) True
 harmony : ∀ i,k ≤ i → i<n→ BQ (k:=k) D Y (i+1) X+D.toll i-(Q i).δ=BQ (k:=k) D Y i X
lemma explore : ∃ X:StarPS n, ∃ Z, Campaign D Y hk X Z:=by
 obtain ⟨v,z,b,c⟩:= urn D hk; obtain ⟨X,Z,a,u,g⟩:= Nomination D Y hk _ c; exact ⟨X,Z, ⟨⟨v,z,a,b⟩,u,fun i h p=>(g i h p).1,fun i h p=>(g i h p).2⟩⟩
namespace Campaign
variable {X: StarPS n}{Q: VestM M B R}(Qπ:Campaign D Y hk X Q)
include Qπ
local notation "bentH" i:max=> bent (k:=k) D Y X Q i
lemma rent (v:k ≤ i)(h:i≤ n): Provides R.L K.j (bentH i) C.h (Jp (i-k) (hat R.L x i)) (Source.rank (i-k)):= (D.essentially ..).2 (Qπ.ware i v h)
lemma pay (v:k ≤ i)(h:i<n)(m:Orbit (cell M B R.L i))(p: Rue.FleetS (Δ.a i).threshold m.1): denZ (bent (k:=k) D Y X Q i) U (F.Y i) m=stove U (F.Y i) (bent (k:=k) D Y X Q (i+1)) (F.Y (i+1)) (GN i) (jS i) C.q' J.d (Q i).r.val m:= by unfold bent; rw [←Qπ.harmony i v h]; exact (Qπ.stairs i v h).pay m trivial p
lemma top : ∃ (v:RegBudget (cell M B R.L n))(z:ℝ), (bent (k:=k) D Y X Q n)=Chaff.fulvia v z (Vale.launch V.L (BQ (k:=k) D Y n X) (Δ.a n) (cell M B R.L n)) ∧ Lendc (F:=F) (n:=n) T v z :=by obtain ⟨v,p,h,t⟩:= Qπ.fire; exact ⟨v,p,by unfold bent; rw [h,D.χtop],t⟩ -- proof after commas syntax
end Campaign
end Crib
end FitD
end YM.CF.Py.Kay
