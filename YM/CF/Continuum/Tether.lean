import YM.CF.Continuum.CoherentSeams
import YM.CF.Chaff.Diet
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 24000
namespace YM.CF.Window
open Function Filter NormedSpace Lattice Wilson Lat SU Fock Phase Mir Cube Mir.Trip RP Reflect Finset Spire Brace Spark Scroll Tulip Dial
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B : Side}
local notation "Λ"=>CSide m B
local notation "Ω"=>Xmind m B
local notation "β"=>northZ m B
local notation "Xskin"=> Skin m B
variable (i:Axis)
-- geometry with Carn.Shing. ALL stencils align at ORIGIN electrical unit.
def toTicket (s:Axis)(F: Evaluation (CSide m B)) : RP.Test m B :=fun x=> toSeam m B s (F x.1)
lemma ticketWeights {F: Evaluation Λ}(u:F∈nonnegativeTime m B i): OfferedF m B i (toTicket i F) false:=by
 obtain ⟨c,l,t,w⟩:= (mem_localObs ..).mp u; constructor
 · unfold toTicket toSeam; simp_rw [twist_formula]; exact (continuous_const.mul ((cxC _).comp (c.comp continuous_fst))).mul continuous_const -- ABI Matrix
 · intro x; exact toSeam_forward i ((t _).sector) rfl
 intro x y h; refine congrArg (toSeam m B i) (l _ _ (fun z p=> h.gaugeS z ((mem_filter.mp p).2.1) ((mem_filter.mp p).2.2)))
private theorem turn_U : costarU m B 0 (northZ m B) i = seamShift m B i:=by
 let p:=northTrip m (0:Site (More m)); have he:p=1:=rfl
 have ht:fermShift m B p=(0: Site Λ):=by
    unfold fermShift; rw [show p.move =0 from rfl, map_zero,zero_add]; funext x; change (if false=true then _ else (0:Per Λ))=_; simp -- False vs false=true
 have hz: far B p β = β:=by funext i; change (if false=true then _ else β i -_) = _; rw [if_neg (by decide),ht,Pi.zero_apply,sub_zero]
 have hm: fperm m B p= Equiv.refl (Site Λ):=by
    ext x :1; change affine (glazed p.glare) (fermShift m B p) x=x; rw [show glazed p.glare=1 from rfl,ht,affine, Signed.act_one, add_zero]
 change fringe (far B p β) (axisCut m B i (far B p β))*siteM _= _; rw [hz,hm,show siteM (Equiv.refl (Site Λ))=1 from Subtype.ext jump_id,mul_one]; rfl
lemma ticket_η {F:Evaluation Λ}(v: F∈ nonnegativeTime m B i) : squareR m B 0 β i (toTicket i F) false=Chaff.leer m B (flipTime m B i F * F):=by
 funext x; unfold squareR; rw [turn_U,show onPack B (northTrip m 0) x=x from pack_id ..]; unfold RP.fiscal; change twist _ ((1:ℂ) • (theta (finger m B i) (toSeam m B i (F (mirrorPane m B i x.1))) * toSeam m B i (F x.1)))=_; rw [one_smul,←toSeam_fiscal i v x.1]; exact twist_inv _ _ -- tune
end YM.CF.Window
