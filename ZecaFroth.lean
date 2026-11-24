import ZecaSteam
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
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
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option maxRecDepth 8000



local instance(i R:ℕ):Nonempty (Parts i R):=by
  let g:Fin 0→Twah := fun x=> x.elim0
  refine ⟨⟨0,by omega⟩,⟨g, ⟨?_, (fun n=> Fin.elim0 n)⟩⟩,fun n=> Fin.elim0 n⟩
  exact ⟨fun n=> Fin.elim0 n.1, fun n=>Fin.elim0 n.1⟩

variable (w:ℕ) (f:Fin w→Lead.Clan)
 (D:Cellz (Fin w)→Gaia) (V:Fin w→DirSpin)
variable (r:ℕ→ℕ)
local notation "HT"=> Twah.homestead
def homeT (n:ℕ) := fun i=> HT D (r n) i V

def kettle (n:ℕ): Parts n (r n):=
 if g:w≤n∧ Outfit n (r n) (homeT w D V r n) then
  ⟨⟨w,Nat.lt_succ_of_le g.1⟩,⟨homeT w D V r n,g.2⟩,f⟩
 else Classical.choice (inferInstance : Nonempty _)
local notation "v"=>Twah.witness f (Twah.letters w) D V

lemma whistle (h:StrictMono r):
 Tendsto (fun i=>(kettle w f D V r i).depiction) atTop (𝓝 v):=by
 let F:=homeT w D V r
 have a:= Twah.witnessFlows f F (Twah.letters w) r D V
    (Twah.riseHome r D h V) (Twah.homeHave r D V)
 refine a.congr' ?_
 filter_upwards [Twah.cottage r D h V,eventually_ge_atTop w] with i y t
 unfold kettle; rw [dif_pos (show w ≤ i ∧ Outfit i (r i) (homeT w D V r i) from ⟨t,y⟩)]
 rfl

-- smul scaling
open Hierarchy.Seld Hierarchy.Seld.Zeca
open Poin Boundary
variable (P:Spine)(x:P.Spectrum0 3) (a:ℂ)
local notation "G"=>P.ManyF 3 x
local notation "S"=>P.seasons 3 x
local notation "Mm"=>Hierarchy.Seld.Zeca.Moment

def essence (M:Mm G) : Mm G := ⟨M.n, a • M.op⟩
lemma essence_op (M:Mm G)(g:Test4) :
 (P.essence x a M).field S g = a • M.field S g :=by
 change ℑ S (a • M.op) g M.n = _
 rw [anyC]; rfl

variable (M:Mm (P.ManyF 3 x)) {F:P.Nib 3 x}
lemma True_essence (d:P.Truth 3 x F M):
 P.Truth 3 x (fun u b=>a • F u b) (P.essence x a M):=by
 refine ⟨?_⟩
 intro t s p q
 rw [d.translation _ _ p q]
 unfold Zeca.Moment.cost essence
 change _ = parabola S M.n _ * (a • M.op) * _
 rw [mul_smul_comm,smul_mul_assoc]

variable (c m:ℕ→ℕ)(h:P.Bean c r m)(Y:ℕ→P.Apron)
 (p:ℕ→ℕ)(t:P.Spoon x c Y p)
local notation "z" => P.essence x v M
def espuma := P.flavor c r m h Y p
   (fun i=>kettle w f D V r (p i))
#check @espuma
local notation "Z"=> espuma w f D V r P c m h Y p

variable (e:P.Iguana 3 x F Y)
include t e
lemma espuma_buy (q:P.Truth 3 x F M):
 (P.Iguana 3 x (fun a b=> v • F a b) Z) ∧ P.Lustre 3 x z Z ∧
   ∀j,Tendsto (fun i=>(Y i).realWidth P j) atTop (𝓝 0) →
        Tendsto (fun i=>(Z i).realWidth P j) atTop (𝓝 0):=by
 let L:∀i, Parts (p i) (r (p i)):= fun i=>kettle w f D V r (p i)
 let g:=P.flavored x c r m h Y p L t F e v ((whistle w f D V r h.eager).comp t.new.tendsto_atTop)
 exact ⟨g,⟨⟨_,g.nib,P.True_essence x v M q⟩,⟨_,g.twin,(P.True_essence x v M q).twin⟩⟩,
      P.flavor_thin x c r m h Y p L t F e⟩
#print axioms espuma_buy
#check @espuma_buy