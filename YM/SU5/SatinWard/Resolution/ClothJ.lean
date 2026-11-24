import YM.CF.Scroll.Vines
import YM.SU5.SatinWard.Resolution.Orph
import YM.CF.Scroll.Verge
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 1600
noncomputable section
namespace YM.CF.Mezzo
open Function NormedSpace Lattice Laurent Finset Cube Lat Fock Tulip Peaks Drapes SU Ember
open Rush Scroll Paige Spire Fir Bloch Next.Free Dial
open scoped Topology Matrix MatrixOrder Kronecker Classical BigOperators InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
local notation "V𝕊" => UNI Slot
variable {N P:Side}(G:Ratio N P)(h:Odd G.count.val)
-- Flavor inquiry receipts
variable {I:Type*}[Fintype I][DecidableEq I]
lemma still_U {U:UNI I}{z:Op I}:twist U z=z ↔ Commute U.val z:=by
 refine ⟨fun h=>?_,Mir.twist_comm _ _ _⟩
 rw [twist_formula] at h; change U.val*z=z*U.val; nth_rw 2 [←h]; rw [mul_assoc (U.val*z), U.property.1,mul_one] -- nth sensitive? replace on rhs first? 
lemma inverse_cost {U:UNI I}{z:Op I}(p:twist U z=z): twist U z⁻¹=z⁻¹:=by
 rcases Matrix.nonsing_inv_cancel_or_zero z with h|h; swap; rw [h,map_zero]
 refine Eq.symm (Matrix.inv_eq_right_inv ?_); -- RHS?
 rw [show z*twist U z⁻¹=twist U (z*z⁻¹) by rw [map_mul,p],h.2,map_one]
/-- This purchase doesn't (yet) meet Flavor costs on any U-character question - only kin and their wardrobes. -/
def Registrar(g:V𝕊):Prop:=∀ x:SU.E, twist g (matter x).val=(matter x).val
lemma Registrar.one:Registrar 1:=fun _=> one_des _
lemma Registrar.mul{g G:V𝕊}(p:Registrar g)(w:Registrar G):Registrar (g*G):=fun x=> still_U.mpr (Commute.mul_left (still_U.mp (p x)) (still_U.mp (w x)))
lemma Registrar.inv{g:V𝕊}(p:Registrar g):Registrar g⁻¹:=fun x=>(show twist (star g) _= _ from by nth_rw 1 [←p x]; rw [twist_inv])
lemma Registrar.star{g:V𝕊}(p:Registrar g):Registrar (star g):=p.inv
section
variable (g:V𝕊)
abbrev ceremony : UNI Slot →* UNI (Iota G):= across (Inta G)
local notation "U"=> ceremony G g
local notation "T"=> twist U
lemma lobe_coat (k:Bool): T (lobe G k)=lobe G k:=by
 unfold lobe; rw [twistLook, map_one]
lemma hood_coat: T (hood G)=hood G:=by rw [shoulder, twistLook,map_one]
lemma foot_rose: foot G (singlet P g).val=(U).val:=by
 rw [foot]; change ((1:Op (Site P × SpinIdx))⊗ₖ g.val).submatrix _ _=(1:Op (Inta G))⊗ₖ g.val; ext ⟨i,a⟩ ⟨j,b⟩; simp [switchG,Matrix.one_apply]
-- D.cost on panes. Keep Thread fence (Sense effective)
lemma panel_alpha (x y:I)(A:Op Slot):twist (across I g) (Tulip.panel x y A)=Tulip.panel x y (twist g A):=by
 let D:Op I:=Matrix.single x y 1
 have he(A:Op Slot):Tulip.panel x y A=D ⊗ₖ A:=by
    ext ⟨q,a⟩ ⟨r,b⟩; by_cases h:q=x <;> by_cases e:r=y <;>simp [D,h,e, Tulip.panel,Matrix.single,Ne.symm, eq_comm]
 rw [he, twistLook,he]
local notation "A𝕊"=>Op (Iota G)
variable (p:Registrar g)
include p in
lemma receipt_veil (r k:Bool)(A: Track G.count)(x:Nom N P)
     (u:∀ i j,Summable fun z:Cover=> ‖A z i j‖): T (mosaic G r k A (unionP x))=mosaic G r k A (unionP x):=by
 have he (o:Lattice.Order)(z): T (driveH G r k A o x z)=driveH G r k A o x z:=by
    unfold driveH Peaks.drag; simp_rw [map_sum,panel_alpha _ _ _ _,unionP,track_pr,brand, twist_scalar, p _] -- p simplification doesn't match
 unfold mosaic; rw [map_smul,map_sum]; congr 1; apply sum_congr rfl; intro o _; rw [wrest G r k A o x u]
 refine (sings_sumts (p:=false) (ceremony G g) (driveH G r k A o x) ?_).trans (tsum_congr (he o))
 exact summable_sum fun _ _=> summable_sum fun _ _=>summ_h G r k A o x u _ _
include p h
lemma cloth_stock (j:ℕ)(M:Male)(x:Nom N P): T (Peaks.cloth j M G (unionP x))= Peaks.cloth j M G (unionP x):=by
 unfold Peaks.cloth; dsimp only; simp only [map_add,map_mul,lobe_coat,receipt_veil G g p true false _ x (cBrix j G.count h).sumK]
lemma ticket_stock (j:ℕ)(k:Bool)(M:Male)(x:Nom N P): T (ticketT (Peaks.cloth j) k M G (unionP x))=ticketT (Peaks.cloth j) k M G (unionP x):=by
 unfold ticketT; simp only [revI,map_add,map_mul,inverse_cost (cloth_stock G h g p j M x), lobe_coat,map_sub,map_one,map_star,cloth_stock G h g p j M x]
end
end YM.CF.Mezzo
