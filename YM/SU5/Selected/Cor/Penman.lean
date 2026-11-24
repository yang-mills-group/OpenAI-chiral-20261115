import YM.SU5.Selected.Cor.Allot
import YM.SU5.Selected.Cor.Amont
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
open Stencil (pulseNode pval)
open Rubric
open Afterglow Afterglow.Tapestry
attribute [local instance] opCStarAlgebra
-- narrow neutral algebra including products. Need separate ambient eval & comm proof. keep support. Compare Nation.
namespace Commission
set_option synthInstance.maxSize 24000
variable {K:Calibration}{S:Finset Cover}{f g:Buffered.Family K}
lemma holdsL (S:Finset Cover)(u:Neutral K f)(p:Neutral K g):Neutral K (f+g):=(harmonicHere (S:=S)).2 fun T=> Circular.add T S ((harmonicHere (S:=S)).1 u T) ((harmonicHere (S:=S)).1 p T)
lemma holdsM (u:Neutral K f)(p:Neutral K g):Neutral K (f*g):=fun m w z=> by change f m _* g m _= twist _ (f m _ *g m _); rw [map_mul,u m,p m]
lemma holdsC (c:ℂ) (u:Neutral K f):Neutral K (c • f):= fun m w z=> by rw [Pi.smul_apply, Pi.smul_apply,Pi.smul_apply,Fock.twist_scalar,u m w] -- #
noncomputable def Cliff (K:Calibration)(S:Finset Cover): Subalgebra ℂ (Buffered.Family K) where
 carrier:= {f| InTest K false S false f ∧ Neutral K f}
 add_mem' x y := ⟨InTest.add x.1 y.1,holdsL S x.2 y.2⟩
 mul_mem' x y := ⟨InTest.mul x.1 y.1,holdsM x.2 y.2⟩
 algebraMap_mem' z:= by rw [Algebra.algebraMap_eq_smul_one]; exact ⟨InTest.smul z (.one),holdsC z (fun _ _ _=> (map_one _).symm)⟩
abbrev Prize (K:Calibration)(S : Finset Cover):= ↥(Cliff K S)
instance Cliff_comm (K:Calibration) (S:Finset Cover): CommRing (Prize K S) where
 mul_comm x y:= Subtype.ext (funext (fun m=> show x.val m*y.val m = y.val m*x.val m from funext (fun i=> fineWise ( Window.fine_enlarge (subset_univ _) (((x.property: InTest K false S false _ ∧ _ ).1.support m).allV i)) (Window.fine_enlarge (subset_univ _) (((y.property: InTest K false S false _ ∧ _).1.support m).allV i))))) -- lean syntax

variable (v:Prize K S)
lemma blush : InTest K false S false v.val:= v.property.1
lemma grown : Neutral K v.val:= v.property.2
open Bulb.Mezz
noncomputable def poll (K:Calibration)(S:Finset Cover)(m:Side): Prize K S →ₐ[ℂ] Floor (park (K.c m) S) where
 toFun x:= ⟨x.val m,(blush x).support m⟩
 map_zero':=rfl
 map_one':=rfl
 map_add' _ _:=rfl
 map_mul' _ _:=rfl
 commutes' _:= rfl
lemma virtue {m:Side}(x:Fields (K.c m)): flickH (park (K.c m) S) x (poll K S m v)= v.val m x:=rfl
lemma mapB {κ R T: Type} [Fintype κ][DecidableEq κ][CommRing R][CommRing T][Algebra ℂ R][Algebra ℂ T](L:R→ₐ[ℂ] T)(f:κ→R)(r:ℕ): L (Stencil.ballet r univ f)= Stencil.ballet r univ (L ∘ f):=by unfold Stencil.ballet; simp only [map_sub,map_sum,map_smul,map_one,_root_.map_prod, Function.comp_apply]
end Commission

open Commission
namespace Mezz
set_option synthInstance.maxSize 24000
attribute [local instance] opCStarAlgebra
open Tender
variable {N:Side} {T:Type}[Fintype T][DecidableEq T]
variable (A:Mezz)(P:Society T)(b:Bool)(i:A.Lot)(X Z:Coast→ Wq A.marks)(C:ℝ) (K:Calibration)(e:A.Legate)
variable {M:Tulip.Male}{w:ℕ}
-- scaled Spry future body. exact determinant with minus sign recorded (at M/h). scalar.
lemma Spry.scale {i:A.Lot}(c:ℂ){F:Buffered.Family K}(p:Spry A P K b i F): Spry A P K b i (c • F):=
 ⟨Submodule.smul_mem _ _ p.marb, holdsC _ p.keeps,by rw [Tower.mirror_scale,Tower.mirror_scale,star_star,p.admire,smul_neg]⟩
local notation "ρ"=> A.Zumba
structure Sermon (W:Window.Family) where
 lamp : Bool→ A.Lot → Buffered.Family K
 tone (b:Bool)(i:A.Lot): lamp b i∈ Marble K W A.Zumba (A.coast_b true) (A.coast_b false) (A.yard i.1 b) (lv_one b) (lv_one (!b)) (priorityR b)
 neutral (b:Bool)(i:A.Lot): Neutral K (lamp b i)
 admire (b:Bool)(i:A.Lot): Tower.mirror K 0 0 (Tower.mirror K 1 0 (lamp b i))= -(lamp b i)
#print Sermon.mk
local notation "Ω"=> Prize K A.Broad
local notation "μ"=> (-(10:ℂ)⁻¹)
variable {W:Window.Family} (F:Sermon A K W)
lemma Sermon.serves : InTest K false (A.yard i.1 b) false (F.lamp b i):=(show cameo (lv_one b) (lv_one (!b))=false from (by cases b <;> decide)) ▸ Marble.assign (F.tone b i)
include e
noncomputable def Sermon.arm : Ω := ⟨F.lamp b i, (F.serves A b i K).mono ((A.yard_core i.1 b e).trans A.Core_subset), F.neutral b i⟩ -- include e parameter? defs include? need mention e in RHS. method `.plant.ard` later
noncomputable def Sermon.summit (i:A.Lot): Ω := F.arm A true i K e * F.arm A false i K e -- param order print
abbrev Storm := A.vowP -- may conflict
local notation "σ" => Stencil.polar Stencil.rho
local notation "ς"=> (F.summit A K e)
-- gala_r
noncomputable def Sermon.solitude : Ω := Stencil.ballet A.vowP Finset.univ (F.summit A K e)
#print Sermon.summit
omit e
noncomputable def Sermon.cert (U: Bool→A.Lot→Buffered.Family K)(u:∀ b (i:A.Lot),Spry A P K b i (U b i)): Sermon A K P.qu.kin:= ⟨U,fun b i=>(u b i).marb,fun b i=>(u b i).keeps,fun b i=>(u b i).admire⟩
local notation "PV"=> P.qu.kin
variable (N':Side) (c:A.Caste (N:=K.c N') M C (tightH A.D (billR C)) w X Z)
local notation "Π'"=> triumph A P X Z C c
open Tapestry Tapestry.Roomy
include c
lemma blast (t:∀ b (i:A.Lot),Roomy (A.yard i.1 b) (K.c N')) : ∃ F:Sermon A K PV, (F.solitude A K c.value).val N'=(Π').frame:=by
 choose U p h using (fun b i=> sprightly A P b i X Z C K N' c (t b i)); let G:=fun (b) (i:A.Lot)=> (if b then μ else 1) • U b i; let F : Sermon A K PV := Sermon.cert A P K G (fun b i=> Spry.scale A P b K _ (p b i)); let L:= poll K A.Broad N'; let S:=park (K.c N') A.Broad; let v:=A.maturing P X Z C c; refine ⟨F,?_⟩
 have he(i):L (F.summit A K c.value i)= σ (Station.roster v) i:=by
    apply Subtype.ext; funext x; let X':=F.lamp true i; let W':=F.lamp false i; change X' N' x*W' N' x=flickH S x (Stencil.tonality Stencil.rho (Station.roster v i)); rw [Station.pore v i P.club_card x]; unfold X' W'
    change (μ • U true i N' x)* (G false i N' x)= -(_ * _); rw [show G false i=(1:ℂ) • U false i from rfl]; rw [one_smul, h,h]; rw [neg_smul, neg_mul]; rfl -- µ syntax & binder one defaults?
 change (L (Stencil.ballet A.vowP Finset.univ (F.summit A K c.value))).val =_; rw [mapB,show L ∘ (F.summit A K c.value)=_ from (show L ∘ (F.summit A K c.value)=σ (Station.roster v) from funext he)]; rfl

end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms blast
