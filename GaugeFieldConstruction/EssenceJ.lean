import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.Passport
import GaugeFieldConstruction.QuerentJ
import SatinThinCarry
import SatinThinConvoy
import SatinThinGutter
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
namespace Promena
open Tapestry Advance CoeffArc Frugal Directory Ing
set_option autoImplicit false
set_option maxHeartbeats 72000
variable (i k:ℕ) {P' V: Side} {f r t v :ℕ}
local notation "B"=> P.block
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
local notation "X_" s:max=> RootBook Y i k s

local notation "µ" s:max=> city (Ω s)
variable {I J G:Type} [Fintype I] [Fintype J][LinearOrder I][LinearOrder J] [LinearOrder G]
variable (p:(Y.voyage i).kick≤ k)
local notation "ν"=> Y.uv k
local notation "θ"=> P.R.L
abbrev HousingJ (G:Type):=∀ s:ℕ,G→Support (More (side Y i s))
variable (O: HousingJ Y i G)(C:Finset G)
abbrev Tiling (s:ℕ):Support (More (side Y i s)):= C.biUnion (O s)
structure Montana (O: HousingJ Y i G)(f:ℕ) :Prop where -- tune
   grow :∀ s:ℕ,f ≤ s→ s <Y.uv k →∀ a,framesM Y s i (O s a) ⊆ O (s+1) a
   gap :∀ s:ℕ,f ≤ s →  s ≤ Y.uv k → ∀ a b:G,a≠b → WardEnd Y s i (O s a) (O s b)
variable (τ:Montana Y i k O f)(U:Mark (side Y i f))(h:AtSupport false (Tiling Y i O C f) U)
include τ
lemma plaza (g:f≤r): Montana Y i k O r:= ⟨fun s q=>τ.grow s (g.trans q),fun s q=> τ.gap s (g.trans q)⟩
lemma Hankwood (a:f ≤ r)(u:r<ν): framesM Y r i (Tiling Y i O C r)⊆ Tiling Y i O C (r+1) :=by
 intro x t; obtain ⟨j,v,e⟩:=halo_spec.mp t; obtain ⟨z,p,rfl⟩:=mem_image.mp v; obtain ⟨m,b,k'⟩:=mem_biUnion.mp p; exact mem_biUnion.mpr ⟨m,b,τ.grow r a u m (halo_spec.mpr ⟨_,mem_image_of_mem _ k', e⟩)⟩
variable (pC:f≤v)(tC:v≤Y.uv k)
local notation "Pϕ"=>AtSupport false
include p h tC
lemma courier : AtSupport false (Tiling Y i O C v) (convoy Y i k pC U):=by
 induction pC with
 | refl=>rw [convoy,climbing_refl]; exact h
 | @step v pC ih=> rw [convoy,climbing_succ _ _ pC]; exact (Hank Y v i k ⟨p,tC⟩ (ih (by omega))).mono (Hankwood Y i k O C τ pC tC)
omit p h tC
lemma Land_gap (D:Finset G)(e:Disjoint C D)(S0:f≤v)(V0:v≤ν): WardEnd Y v i (Tiling Y i O C v) (Tiling Y i O D v):=by -- trim
 intro x hx y hy; obtain ⟨j,a,b⟩:=mem_biUnion.mp hx; obtain ⟨k,c,d⟩:=mem_biUnion.mp hy; exact τ.gap v S0 V0 j k (fun v' =>disjoint_left.mp e (v' ▸ a) c) x b y d -- k shadow
include p h tC
lemma turnU (D:Finset G)(u:Mark (side Y i f))(e:Disjoint C D)(g:AtSupport false (Tiling Y i O D f) u): convoy Y i k pC (U*u)=convoy Y i k pC U *convoy Y i k pC u:=by
 induction pC with
 | refl=> simp only [convoy,climbing_refl]
 | @step s q ih=>
    simp_rw [convoy,climbing_succ _ _ q]; unfold convoy at ih; rw [ih (by omega)]; exact AirMag Y s i k ⟨p,tC⟩ (courier Y i k p O C τ U h q (by omega)) (courier Y i k p O D τ u g q (by omega)) (Land_gap Y i k O C τ D e q (by omega)) -- tune order
#print axioms turnU
omit τ h p tC
section roll
abbrev galaJ (f:I→G)(L:List I):Prop:= (L.map f).Pairwise (·<·)
abbrev nearJ (w:I→G)(X: HousingJ Y i G)(C: Finset G)(s:ℕ)(l:List I)(A:Mark (side Y i s)):Prop:=Disjoint C (l.map w).toFinset∧AtSupport false (Tiling Y i X C s) A
-- type of outputs from top back. support qualifications.G variants $only earlier-than-Later$; full in regular layouts.
abbrev FarLedge (H:G→Prop)(w:I→G):Prop:=∀ i j:I, w i < w j → H (w i)
abbrev RevenueT (A:Mark (side Y i (Y.uv k))) :ℂ:=markedRead A ((Y.voyage i).CapeT (Y.uv k)) (Scree.denZ (RootBook Y i k (Y.uv k)) P.U ((Y.voyage i).CapeT (Y.uv k)))
-- Version stable city; eager pointwise when wanted via generated Mark.Old.
variable (w:I→G)(X: HousingJ Y i G)(K:G→Prop)(t:f ≤Y.uv k)(E: List I→Orbit (side Y i f)→ Phys (side Y i f))(A:I→Mark (side Y i (Y.uv k)))
abbrev κStory (s:ℕ):=Orbit (side Y i s)→Phys (side Y i s)
-- no macro capture. p.K proof separate.
section
variable {M:Side}
-- Top estimates only. Fine not needed at top, sector suffice. preserve dependence for optionally touching.K.
structure PostSupport (b: Bool)(St:Support (More M))(U:Mark M) :Prop where
  env:Envelope U
  dep(x y:Fields M): Agrees St x.1 y.1→ Agrees St x.2 y.2→ U x=U y
  trade(x:Fields M):Fock.Sector (modesIn M St) b (U x)
variable {F U:Mark M}{Z T:Support (More M)}{b c:Bool}
lemma PostSupport.of (p:AtSupport b Z F):PostSupport b Z F:=⟨p.env,p.dep,fun x=> (p.allV x).sector⟩
lemma PostSupport.addM(p:PostSupport b Z F)(q:PostSupport b Z U):PostSupport b Z (F+U):=⟨Girt.kitE _ _ (·+·) (by fun_prop) p.env q.env,fun x y u v=>congrArg₂ (fun x y:FC (Single M)=>x+y) (p.dep _ _ u v) (q.dep _ _ u v), fun i=> (p.trade i).add (q.trade i)⟩
lemma PostSupport.smulM(p:PostSupport b Z F)(z:ℂ):PostSupport b Z (z • F):=⟨Girt.kitE (fun _ : Fields M=>z) F (fun a b=> a • b) (by fun_prop) (Girt.rite_c _) p.env,fun x y u v=>congrArg (fun x:FC (Single M)=>z • x) (p.dep _ _ u v),fun x=> (p.trade x).scale z⟩
lemma PostSupport.mulM(p:PostSupport b Z F)(q:PostSupport c Z U):PostSupport (b.xor c) Z (F*U):=⟨env_mult p.env q.env,fun x y u v=>congrArg₂ (fun x y:FC (Single M)=> x*y) (p.dep _ _ u v) (q.dep _ _ u v),fun i=> (p.trade i).mul (q.trade i)⟩
lemma PostSupport.zeroM:PostSupport b Z (0:Mark M):=PostSupport.of AtSupport.zeroM
end
structure Listos (f:I→G)(X:HousingJ Y i G)(A:G→Prop)(s:ℕ)(W:I→Mark (side Y i s)):Prop where
 owns (j:I): PostSupport false univ (W j)
 slit(j:I): A (f j) → PostSupport false (X s (f j)) (W j)
structure Entourage (x0:List I→ Orbit (side Y i f)→Phys (side Y i f))(V:I→Mark (side Y i (Y.uv k))) :Prop where
   stamped: Listos Y i w X K (Y.uv k) V
   lease (l:List I)(u:galaJ w l): Version (city (side Y i f)) (x0 l)
   fare (l:List I)(u:galaJ w l)(C:Finset G)(W:Mark (side Y i f))(p:nearJ Y i w X C f l W): markedRead W ((Y.voyage i).CapeT f) (x0 l)= RevenueT Y i k (convoy Y i k t W * (l.map V).prod)
#print axioms Entourage
end roll
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
