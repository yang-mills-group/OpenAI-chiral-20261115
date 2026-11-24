import YM.SU5.Assay.Reel
import YM.SU5.Assay.PriorTithe
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
/-!
# Narrow native pure assignments for `PriorTithe`.

We'll keep a list honestly printed from the formulas. This supplements
canonical comparison at the actual finer pose/smear height (where *both*
panes count for pure gauge prices). Coeff false: first link only, continuous.
-/
def Yarn (P:Spine)(D:Finset Cover)(x:P.Test) : Prop:= ∃ f:PairsC→ℂ,Coeff false D f ∧ x.val=scalar P.calibration f
namespace Yarn
lemma part (q:P.Yarn D x) : x∈bay K D false:=by
 obtain ⟨f,h,e⟩:=q;rw [Tapestry.locates,e];exact InTest.seed h
lemma pure (q:P.Yarn D x):PureGauge K x:=by
 obtain ⟨f,h,e⟩:=q; exact ⟨D,f,⟨by simp,h.env,h.locus⟩,e⟩
lemma mono (p:D⊆S)(q:P.Yarn D x):P.Yarn S x:=by obtain ⟨f,h,e⟩:=q; exact ⟨_,h.mono p,e⟩
lemma unit' : P.Yarn D 1:= ⟨1,Coeff.fromC _ _ (f:=1) continuous_const (fun _ _ _=>rfl),unitLink.symm⟩
lemma smul (z:ℂ)(q:P.Yarn D x):P.Yarn D (z•x):= by
 obtain ⟨f,h,e⟩:=q
 refine ⟨z•f,⟨?_,pole_w f (fun y:ℂ=>z•y) (by fun_prop) h.env,fun _ _ a b=>congrArg (fun y:ℂ=>z•y) (h.locus _ _ a b)⟩,?_⟩
 · intro n; obtain ⟨u,w,rfl⟩:=h.narrow n; exact ⟨z•u,w.const_smul z,rfl⟩
 change z•x.val=_; rw [e]; funext i t
 change z • (f _ • (1 : FC _)) = (z • f _) • _; exact smul_smul z _ _
lemma mul (h:P.Yarn D x)(p:P.Yarn D y):P.Yarn D (x*y):= by
 obtain ⟨f,h,r⟩:=h; obtain ⟨g,p,q⟩:=p
 refine ⟨f*g,⟨?_,kitE _ _ (·*·) (by fun_prop) h.env p.env,fun _ _ a b=>congrArg₂ (α:=ℂ) (β:=ℂ) (·*·) (h.locus _ _ a b) (p.locus _ _ a b)⟩,?_⟩
 · intro n; obtain ⟨u,w,rfl⟩:=h.narrow n; obtain ⟨v,k,rfl⟩:=p.narrow n
   exact ⟨_,w.mul k,rfl⟩
 change x.val * y.val = _; rw [r,q]
 funext m z; simp only [Pi.mul_apply,scalar,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,one_mul,smul_smul]; rw [mul_comm]
end Yarn

/-- `some W`: record physical center test (or a gauge witness of same
charges) W, opposite phase in first factor. `none`: no charge required. -/
structure Fibre (P:Spine)(c:Option Bool)(D:Finset Cover)(a b:P.Test): Prop where
 glass: P.Yarn D a
 letter:PureMatter P.calibration b
 park:b∈bay P.calibration D false
 couples:∀W,c=some W→∃g:Cover→SU.E,pennant P.calibration g a=(phaseName W)⁻¹•a∧ pennant P.calibration g b=phaseName W•b

namespace Fibre
lemma prior (p:P.Fibre (some W) D a b): PureSplit K W D a b:=
 ⟨p.glass.pure,p.letter,widerBay _ _ _ p.glass.part,widerBay _ _ _ p.park,p.couples W rfl⟩
lemma tuft (h:P.Yarn D a): P.Fibre none D a 1:=
 ⟨h,(pure_unit K).2,(bay ..).one_mem,fun _=>by simp⟩
lemma void' (p:P.Fibre c D a b): P.Fibre none D a b:=⟨p.glass,p.letter,p.park,fun _=>by simp⟩
lemma mono (q:D⊆T)(p:P.Fibre c D a b):P.Fibre c T a b:= ⟨p.glass.mono q,p.letter,tallerBay _ _ _ q p.park,p.couples⟩
lemma smul (z:ℂ)(p:P.Fibre c D a b):P.Fibre c D (z•a) b:=by
 refine ⟨p.glass.smul _,p.letter,p.park,fun W v=>?_⟩
 obtain ⟨g,w,k⟩:=p.couples W v; exact ⟨g,by rw[map_smul,w,smul_comm],k⟩
lemma joint (h:P.Fibre c S a b)(p:P.Fibre none T x y)(d:Disjoint S T):P.Fibre c (S∪T) (a*x) (b*y):= by
 have i:=h.mono (show S⊆S∪T from subset_union_left); have j:=p.mono (show T⊆S∪T from subset_union_right)
 refine ⟨i.glass.mul j.glass,matterPure_mul K i.letter j.letter,(bay ..).mul_mem i.park j.park,fun W u=>?_⟩
 obtain ⟨r,z,w⟩:=h.couples W u
 let l:GVertex:=fun i=> if i∈S then r i else 1
 have hp(v:P.Test)(g:v∈bay K S false):pennant K l v=pennant K r v:=P.local_recolor S (widerBay _ _ _ g) l r (fun _ h=>if_pos h)
 have hu(v:P.Test)(g:v∈bay K T false):pennant K l v=v:= fixed_local K T l (fun i v=> if_neg fun a=>Finset.disjoint_left.mp d a v) (widerBay _ _ _ g)
 exact ⟨l,by rw [map_mul,hp _ h.glass.part,z,hu _ p.glass.part,smul_mul_assoc],by rw [map_mul,hp _ h.park,w,hu _ p.park,smul_mul_assoc]⟩
end Fibre
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
