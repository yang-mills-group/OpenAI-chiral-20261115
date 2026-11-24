import YM.CF.Continuum.Tether
import YM.CF.BProof.Transit.Orel
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 24000
namespace YM.CF.BProof.Bide
open Function Filter NormedSpace Lattice Wilson Lat SU Fock Phase Mir Cube Mir.Trip RP Reflect Finset Spire Brace Spark Scroll Tulip Dial
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B : Side}
local notation "Λ"=>CSide m B
local notation "Ω"=>Xmind m B
local notation "β"=>northZ m B
local notation "Xskin"=> Skin m B
variable (i:Axis)
open Window
private theorem turn_U : costarU m B 0 (northZ m B) i = seamShift m B i:=by
 let p:=northTrip m (0:Site (More m)); have he:p=1:=rfl
 have ht:fermShift m B p=(0: Site Λ):=by
    unfold fermShift; rw [show p.move =0 from rfl, map_zero,zero_add]; funext x; change (if false=true then _ else (0:Per Λ))=_; simp -- False vs false=true
 have hz: far B p β = β:=by funext i; change (if false=true then _ else β i -_) = _; rw [if_neg (by decide),ht,Pi.zero_apply,sub_zero]
 have hm: fperm m B p= Equiv.refl (Site Λ):=by
    ext x :1; change affine (glazed p.glare) (fermShift m B p) x=x; rw [show glazed p.glare=1 from rfl,ht,affine, Signed.act_one, add_zero]
 change fringe (far B p β) (axisCut m B i (far B p β))*siteM _= _; rw [hz,hm,show siteM (Equiv.refl (Site Λ))=1 from Subtype.ext jump_id,mul_one]; rfl
lemma matterD : modes (upField m B i)=matterSet Λ (posY m B i):=by ext; simp [modes,matterSet,holder]
lemma tWeights {F: Obs (CSide m B)}(u:Allowed (upField m B i) F)(p:Continuous F): OfferedF m B i (toTicket i F) false:=by
  constructor
  · unfold toTicket toSeam; simp_rw [twist_formula]; exact (continuous_const.mul ((cxC _).comp (p.comp continuous_fst))).mul continuous_const
  · intro x; exact toSeam_forward i ((matterD i) ▸ u.modes_use x.1) rfl
  intro x y h; refine congrArg (toSeam m B i) (u.reads _ _ (fun z q v=> h.gaugeS z q v))
lemma tFiscal {F: Obs (CSide m B)} (u:Allowed (upField m B i) F) : squareR m B 0 β i (toTicket i F) false=Chaff.leer m B (Fixed.reflectTest i false F * F):=by
 funext x; unfold squareR; rw [turn_U,show onPack B (northTrip m 0) x=x from pack_id ..]; unfold RP.fiscal; let g:= F (mirrorPane m B i x.1); have hy: theta (finger m B i) (toSeam m B i g)=toSeam m B i (Fixed.reflectTest i false F x.1):=by
    unfold Fixed.reflectTest Reed.reverseW; rw [show Reflect.chord false=(1:ℂ) from rfl,one_smul]; have hz: Fixed.reflConfig Λ i=mirrorPane m B i:=by rw [mirrorPane_eq]
    rw [hz]; exact (toSeam_turn i (A:=g) ((matterD i) ▸ (u.modes_use _))).symm
 change twist _ ((1:ℂ) • (theta (finger m B i) (toSeam m B i g) * toSeam m B i (F x.1)))= _; rw [one_smul,hy,←toSeam_prod]; exact twist_inv _ _ -- tune
open Gully Spire Scree Jet Ave Skye Gas Pastry Dial RG Pressure
open Gloss Maize Nova Ione Salt Hive Vow
open Hom Vale Vale.Grace Kea RP RP.Str Gauge Paige Vault
open Precision Next.Free
variable {e a t A x h Q r c:ℝ}{L:Patch}{Z:Teller SU.group}{W:ChartRatio SU.group}{V:Grace Z L W}{U:Grasp V.U B e}{R:Scree.Loom (CSide m B)}{J : RegBudget (CSide m B)}{F0: Scroll m B (Brace.northZ m B)}{P:BudgetPoint}
local notation "λx" l:max => (Chaff.fulvia J c (Vale.launch V.L l P Λ))
lemma pane (l:ℝ)(u:Chaff.Lives_B (H:=h) V F0 J r Q P R U c)(v:Budget B e x)(he:ScaleK a A F0)(p:Rue.IsleB SU.group P.threshold)(z:0 ≤ r)(F: Obs (CSide m B))(g:Allowed (upField m B i) F)(hc:Continuous F) : 0 ≤ Fixed.numerator U (λx l) R (Fixed.reflectTest i false F * F) := by
 rw [show Fixed.numerator U (λx l) R (Fixed.reflectTest i false F * F)= _ from Chaff.lit_R V F0 J l u _ ((Fixed.reflectTest_cont _ _ hc).mul hc) he v p, ← tFiscal i g]; exact greenRF _ _ _ _ _ _ _ _ _ _ z he v _ _ _ (tWeights i g hc)
end YM.CF.BProof.Bide
