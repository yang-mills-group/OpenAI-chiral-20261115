import YM.SatinExist.RivetX
import YM.SU5.FiniteGaugeData.Indigo.Ultrav
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower Py Py.Rate Py.Rate.LocalLimit Preparation Journey
variable {P: Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))(H:Real.exp 1≤P.x)
local notation "W"=> tent Y H
variable (S T:Finset Cover)(s i k:ℕ) (E:Dome (tent Y H)→ₗ[ℂ]ℂ)
namespace Xara
local notation "X"=> side Y i s
local notation "Γ"=> side Y i (s+1)
local notation "Q"=> FC (Single Γ)
local notation "ν" F:max=> OneCup.slice W E F
local notation "π" F:max => aboveD Y H s i k F
local notation "U!" S:max=> wingspan P ℓ S
open Preparation
open Hierarchy
open Hierarchy.Navy
variable (o:Ferry Y (s+1) i k)(C x:Cover)(f A:GemUT)(B:ℝ)(b:0 ≤ B)(j:nodeC C∈ S)(u:nodeC x∈T) (d:Sizing P s)(z:2*aliasLaw P < (side Y i s).val)(I:FC (Single (side Y i (s+1)))→ₗ[ℂ]ℂ)
lemma aboveCastle (a:SU.F): aboveD Y H s i k (clone (tent Y H) C C f a a).val = ascender Y s i k (chapX (side Y i s) f C a):=by
 have h: distribute Y H s i (clone W C C f a a).val=chapX X f C a:=funext (fun V=>dish Y H s i C C f a a V); unfold aboveD; rw [h]
include j u d z o b
lemma highIn (g:Wing (Satin.region (U! S) Γ) (Satin.region (U! T) Γ) I B)(a h:SU.F)(w:Fields (side Y i (s+1))): ‖I (aboveD Y H s i k (clone (tent Y H) C C f a a).val w * aboveD Y H s i k (clone (tent Y H) x x A h h).val w)‖ ≤ DiamondX*B:=by
 rw [aboveCastle,aboveCastle]; let L:= Vale.apt (Y.ir i) P.block P.R.L s; have v:Satin.PairIdx Y s i k:= ⟨o.depth,o.enters⟩; let T':=(fullness Y i k v.1).cap_grant
 exact braidX L P.K.j (by rw [P.kJ]) P.R.odd_side P.R.coarse (patternQ Y s i k) ((((Y.voyage i).X (Y.uv k)).gram (s+1))).J.M ((betaQ_ranges Y s i k v).2.trans d) (Journey.legal P) z (patternA Y s i k) Chi.canonical P.J.d (patternβ Y s i k) ((Y.voyage i).CapeT s) (T'.branch s v.2) (Tapestry.threshold Y).1 (Tapestry.threshold Y).2 ((Y.voyage i).ownership s).paid.bill C x a h f A S (U! S) T (U! T) I B g j u (footprint_step Y s i S) (footprint_step Y s i T) b w w
omit b j u d z
include o
lemma whole_bill (w:Fields (side Y i (s+1))) : aboveD Y H s i k (sheen (tent Y H) C f).val w = ∑ a:SU.F, aboveD Y H s i k (clone (tent Y H) C C f a a).val w:=by
 let S':Finset Cover:= {nodeC C}; have hz(a:SU.F): InTest W true S' false (clone W C C f a a).val:= bum_bay _ S' _ _ _ _ _ _ _ _ (by simp [S']) (by simp [S'])
 have hv:Satin.PairIdx Y s i k:=⟨o.depth,o.enters⟩
 have hp (a:Finset SU.F): InTest W true S' false ((∑ i∈a, clone W C C f i i):Dome W).val:=(bay W S' true).toSubmodule.sum_mem (fun i _=> (locates W _ _ (f:=clone W C C f i i)).2 (hz i))
 suffices h:∀ a:Finset SU.F, aboveD Y H s i k ((∑ i∈a,clone W C C f i i):Dome W).val w=∑ x∈a, aboveD Y H s i k (clone W C C f x x).val w from h _
 intro a; induction a using Finset.induction_on with
 | empty=>
    let V:= distribute Y H s i; have he: V (0:Dome W).val=0:=by have hz:= (distribute_arith Y H s i 0 0 0).2.2.1; simp at hz; exact hz
    have he':= ascendScale Y s i k hv (distribute Y H s i (clone W C C f 0 0).val) (stationed Y H s S' i (hz 0)).env 0; simp only [zero_smul] at he'
    simp only [sum_empty]; change ascender Y s i k (V ((0:Dome W).val)) w=0; rw [he,he']; rfl
 | @insert a A d ih=>
    simp_rw [sum_insert d]; let Z:= (clone W C C f a a); let Q':= ∑ i∈ A,clone W C C f i i
    let T':=distribute Y H s i Z.val; let G:=distribute Y H s i Q'.val; change ascender Y s i k (distribute Y H s i (Z.val+Q'.val)) w= _; rw [(distribute_arith Y H s i _ _ 0).1]; rw [ascendPlus Y s i k hv _ _ (stationed Y H s S' i (hz a)).env (stationed Y H s S' i (hp A)).env]; rw [←ih]; rfl
omit o
end Xara
end YM.CF.Buffered.Afterglow.Six
