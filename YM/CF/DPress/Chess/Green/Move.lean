import YM.CF.Continuum.CoherentSeams
import YM.CF.DPress.Chess.Floor.Porch
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Green
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube RP Phase Branch Mir Mir.Trip Brace Nacre Window Tenant
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m B:Side}{l':Site (More m)}
local notation "V_"=> CSide m B
local notation "I_"=> northTrip m l'
local notation "α_"=> W.i
abbrev Attend (W:Wall)(B:Side)(l':Site (More m)):Prop:= (gaugeR m B).root l'=wrap (CSide m B) W.od
lemma purchase (W: Wall)(m B: Side)(h:(B.val:ℤ)∣ W.o) : ∃ l':Site (More m), Attend W B l':=by
 obtain ⟨i,h⟩:=h; refine ⟨wrap _ (i • step W.i),?_⟩; unfold Attend Wall.od; rw [Ratio.root_embed,Ratio.embed_wrap,h]; apply congrArg; change B.val • _ = _; ext i; simp
variable (p: Attend W B l')
include p
lemma pose0 : torShift B (I_) = wrap (Domain m B) (2 • W.od):=by unfold torShift paneShift; rw [←scale_eq, show (I_).move=l' from rfl,p,Ratio.root_embed,Ratio.embed_wrap]; rfl
lemma shift_v : fermShift m B (I_)= wrap (CSide m B) W.od:=by unfold fermShift; rw [show (I_).move=l' from rfl,p,show ankle (I_).glare=(0:Site (CSide m B)) from funext (fun _=>rfl),add_zero] -- tune decidable iff rfl
lemma crossing_v (x:Site (CSide m B)): fperm m B (I_) x=x+wrap (CSide m B) W.od:= by unfold fperm; change affine _ (fermShift m B (I_)) x=_; unfold affine; rw [shift_v W p]; rfl
lemma tof_v : Tofu (lagX W.od) V_ = fperm m B (I_):= by apply Equiv.ext; intro i; rw [crossing_v W p]; exact lag_i ..
lemma callG (U:Pane V_): through B (I_) U=Yg (lagX W.od) U:=by unfold through; rw [pose0 W p]; rfl
omit p
lemma meet : joinX W.shape (lagX W.od)=joinX (lagX W.od) (Window.shape W.i):=by
 unfold joinX Wall.shape Window.shape lagX; simp only [mul_one, one_mul,Signed.act_one,zero_add]; apply congrArg; ext j; by_cases h:j=W.i <;> simp [Signed.act,Signed.mirror,h,Ne.symm,Wall.od] <;> try ring
include p
lemma brace (X:Pane V_):through B (I_) (W.shine V_ X)=Window.mirrorPane m B W.i (through B (I_) X):=by
 rw [callG W p,callG W p]; have hz : Window.mirrorPane m B W.i= Yg (Window.shape W.i):=by rw [Window.mirrorPane_eq]; unfold Yg stir; rw [show (Window.shape W.i).t=(0:Cover) from rfl,smul_zero,map_zero]; rfl
 rw [Wall.shine_t,hz]; change Yg _ (Yg _ X)=_; rw [← Nacre.kor,← Nacre.kor, meet W]
lemma sendU (a:Wall)(x:Pane V_) : through B (I_)⁻¹ (Window.mirrorPane m B W.i (through B (I_) x))= W.shine _ x :=by rw [←brace W p,through_comp, mul_inv_cancel,through_o]
omit p in
lemma backT (x:Pane V_) : through B (I_)⁻¹ (through B (I_) x)=x:=by rw [through_comp,mul_inv_cancel,through_o]
/-- portal cut at top from shifted anticross -/
lemma φ_v : RP.portal m B l' (northZ m B) W.i=axisCut m B W.i (northZ m B) :=by
 unfold RP.portal axisCut; ext i; by_cases h:i=W.i; subst i; rw [update_self,update_self]
 rw [update_of_ne h,update_of_ne h, Trip.far,if_neg (by simp [northTrip])]; rw [shift_v W p, Wall.od,map_zsmul,wrap_step]; simp [h] -- tune
end YM.CF.DPress.Chess.Green
