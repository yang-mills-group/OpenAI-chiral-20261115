import YM.SU5.FiniteGaugeData.Marked.Journey.Outpost
import YM.SU5.FiniteGaugeData.Marked.Studio

/-!
# Binding the buffered types in the direct construction. On every period
financed by the other assignment on this very course, `score` is exactly
the direct level-zero expression. Thus can choose E even before knowing the
all-period calibration. Marks commute with the necessary casts.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Burn
variable {Λ:Preparation}{l:ℕ}{Y:Course Λ (VolumeCape.Dream.Nimbus l)}(h:Real.exp 1 ≤ Λ.x)
local notation "K₀"=>tent Y h
open Coupling
variable {K:Calibration} {C:Conveyor K}{J:Tiling K}{V:SpanCal K}(W:Printed K C J V)
variable {u π:ℕ→ℕ}(S:Coupling.Schedule K C Λ Y u π)
include S
lemma tandem (m : Side) : K.c m= (K₀).c m:=by
  have he:= S.scale 0
  have h:K.B=(K₀).B:=by
    apply Subtype.ext
    let k:= Y.ir (u 0); apply mul_left_cancel₀ (M₀:=ℕ) (show k.val*2≠0 by have hp:0<k.val:=k.property; omega)
    exact (csize K (m:=k)).symm.trans ((congrArg (fun x:Side=> x.val) he).trans (csize K₀ (m:=k)))
  apply Subtype.ext; exact (csize _).trans ((congrArg (fun x:Side=>m.val*2*x.val) h).trans (csize _).symm)

def adopt (f:Family K) : Family (tent Y h) := fun m=> (tandem h S m) ▸ f m

lemma brought {x:Finset Cover}{f:Family K}{b:Bool}(p:InTest K true x b f): InTest (tent Y h) true x b (adopt h S f):=by
  induction p with
  | @seed f t=>
    rw [show adopt h S (scalar K f)=scalar (tent Y h) f from funext fun m=> @rs _ _ (tandem h S m) f]; exact .seed t
  | @creator x i b a v=> rw [show adopt h S (creation K x i b)= _ from funext fun m=> @rc _ _ (tandem h S m) i x b]; exact .creator b a v
  | @remover x i b a v=> rw [show adopt h S (removal K x i b)= _ from funext fun m=> @rr _ _ (tandem h S m) i x b]; exact .remover b a v
  | zero=> rw [show adopt h S 0=0 from funext fun m=> @rz _ _ (tandem h S m)]; exact .zero
  | one=> rw [show adopt h S 1=1 from funext fun m=> @ro _ _ (tandem h S m)]; exact .one
  | @add f g _ _ _ a b=> rw [show adopt h S (f+g)=adopt h S f + adopt h S g from funext fun m=> @ra _ _ (tandem h S m) (f m) (g m)]; exact .add a b
  | @smul f _ z _ e=> rw [show adopt h S (z • f)=z • adopt h S f from funext fun m=>@rm _ _ (tandem h S m) z (f m)]; exact .smul z e
  | @mul f g _ _ _ _ a b=> rw [show adopt h S (f*g)=adopt h S f*adopt h S g from funext fun m=> @rwμ _ _ (tandem h S m) (f m) (g m)]; exact .mul a b
where
 rs{n k:Side}(h:n=k)(f:PairsC→ℂ): (show Mark k from h ▸ (fun t:Fields n=> f (onC n t.1,onC n t.2) • (1:Fock.FC (Single n))))=fun t:Fields k=> f (onC k t.1,onC k t.2) • (1:Fock.FC (Single k)):=by subst n; rfl
 rc{n k:Side}(h:n=k)(i:SpinIdx)(x:Cover)(b:SU.Slot):(show Mark k from h ▸ fun _:Fields n=>Fock.create (basisC n x i b))=fun _:Fields k=>Fock.create (basisC k x i b):=by subst n; rfl
 rr{n k:Side}(h:n=k)(i:SpinIdx)(x:Cover)(b:SU.Slot):(show Mark k from h ▸ fun _:Fields n=>Fock.remove (basisC n x i b))=fun _:Fields k=>Fock.remove (basisC k x i b):=by subst n; rfl
 rz{n k:Side}(h:n=k):(show Mark k from h ▸ (0:Mark n))=0:=by subst n; rfl
 ro{n k:Side}(h:n=k):(show Mark k from h ▸ (1:Mark n))=1:=by subst n; rfl
 ra{n k:Side}(h:n=k)(f g:Mark n):(show Mark k from h ▸ (f+g))=(show Mark k from h ▸ f)+(show Mark k from h ▸ g):=by subst n; rfl
 rm{n k:Side}(h:n=k)(a:ℂ)(f:Mark n): (show Mark k from h ▸ (a • f))=a • (show Mark k from h ▸ f):=by subst n; rfl
 rwμ{n k:Side}(h:n=k)(f g:Mark n):(show Mark k from h ▸ (f*g))=(show Mark k from h ▸ f)*(show Mark k from h ▸ g):=by subst n; rfl
lemma broad {f:Family K}(p:TestFamily K true f): TestFamily (tent Y h) true (adopt h S f):=⟨⟨_,brought h S p.paid.choose_spec⟩,fun h=>by contradiction⟩

lemma home_score (i k:ℕ)(f:Family K) : score Y u π S i k f=sharp Y h 0 (u i) (π k) (adopt h S f):=by
  unfold Coupling.score sharp listen compass markedRead letterRead adopt send
  have hh:=S.scale i
  suffices e:(show Mark (Λ.Ctor (Y.ir (u i)) 0) from (S.scale i) ▸ f (Y.ir (u i)))= (show Mark (Λ.Ctor (Y.ir (u i)) 0) from (terrain Y h (Y.ir (u i)) 0) ▸ ((tandem h S (momentm Y (u i) 0)) ▸ f (momentm Y (u i) 0):Mark ((K₀).c (momentm Y (u i) 0)))) by
    exact congrArg (compass Y (u i) (π k) 0) e
  let m:=Y.ir (u i); exact @same m (momentm Y (u i) 0) (Λ.Ctor m 0) _ _ f (by unfold momentm Vale.mesh; rw [pow_zero,mul_one]) hh (terrain Y h m 0) (tandem h S _)
where
 same{m A Q:Side}(M N:Side→Side)(f:∀ m,Mark (M m))(p:A=m)(w:M m=Q)(u:N A=Q)(e:M A=N A):
    (show Mark Q from w ▸ f m) = (show Mark Q from u ▸ (show Mark (N A) from e ▸ f A)) := by subst_vars; simp
end YM.CF.Buffered.Afterglow.Journey
