import YM.CF.BProof.Chess.Mercy
import YM.CF.BProof.Chess.Stave
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Chess
open Function Filter Metric NormedSpace Finset Lattice Cube Bide Spire Bide.Half RG Fock Lat Skye Scree
open scoped Matrix.Norms.L2Operator Matrix ComplexOrder Topology BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Tulip MeasureTheory
open Window.Unfit
variable {N L:Side}{i:Axis}{s t h z w:ℕ}
local notation "Trup"=> Scute N L i w
structure Drum (N L:Side)(i:Axis)(w:ℕ)(H:Obs N→ℝ): Prop where
 pos :0<w
 rise :∃ X: Orbit N→ Phys N,∃ v:ℂ, Envelope X ∧ (∀ T:Obs N, H T=‖v*Fixed.functional X T‖) ∧ ∀ (F: Obs N),Allowed (shade N i true w) F → 0 ≤ Fixed.functional X (Fixed.reflectTest i false F*F)
 rides:∀ (s:ℕ) (F:Obs N), H (move (drive N L i s) F)= H F
namespace Drum
variable {H:Obs N→ℝ}(D:Drum N L i w H)
variable (x y z:Scute N L i w)
local notation "Wt"=>Fixed.reflectSweep N i
local notation "R" x:max=> move (drive N L i x)
open Scute
lemma roller (p:home L s N)(F:Obs N)(g:plainP F): move (drive N L i s) F=F:=by rw [homeP N L i p, move_e g]
abbrev price (H:Obs N→ℝ)(x:Scute N L i w):=H x.mark
include D
lemma nonneg : 0 ≤ price H x:=by obtain ⟨z,a,g,t,_⟩:= D.rise; rw [price,t]; positivity
lemma circle (p:home L (x.length+y.length) N): price H (x*y)=price H (y*x):=by
 let t:= pace N L i y.length
 have hp:home L (y*x).length N:=by rw [surge,add_comm]; exact p
 unfold price; rw [←D.rides y.length (x*y).mark,slash,slash,map_mul,gather _ _ (plain y.permit),roller (surge y x ▸ hp :home L (y.length+x.length) N) y.mark (plain y.permit)]; rw [(y.commutes x (le_of_eq hp) D.pos).eq] -- tune home length
omit D
abbrev halfC(L N:Side)(l:ℕ):Prop:=field L l=N.val
lemma sole (v:halfC L N x.length)(p:halfC L N y.length): x.length=y.length:=by
 have he:=v.trans p.symm; unfold field at he; apply mul_left_cancel₀ (show L.val≠0 from L.property.ne'); apply mul_left_cancel₀ (show 2≠(0:ℕ) by omega); exact he
lemma horizon (v:halfC L N x.length)(p:halfC L N y.length): home L (x*y).length N:=by unfold home; rw [surge,field_add,natM,show field L x.length=N.val from v,show field L y.length=N.val from p]; omega -- tune no def
lemma material (v:halfC L N x.length): Allowed (shade N i true w) x.mark:= mode_p x.permit (stretch N L i v)
lemma red (v:halfC L N x.length)(p:halfC L N y.length): (R x.length) y.bar.mark = Fixed.reflectTest i false y.mark:=by
 rw [bar_t,gather _ _ (keys _ (plain y.permit)),roller (surge x y ▸ horizon x y v p : home L (x.length+y.length) N) _ (keys _ (plain y.permit)), Bide.origin i (plain y.permit)]
include D
lemma sumM (v:halfC L N x.length)(p:halfC L N y.length): (x*y.bar).mark= bellM i y.mark x.mark:=by
 rw [slash,(x.commutes y.bar (le_of_eq (horizon x y.bar v p)) D.pos).eq, red x y v p]
lemma shield (A B:Obs N)(a:Allowed (shade N i true w) A)(b:Allowed (shade N i true w) B): H (bellM i A B)^2 ≤ H (bellM i A A)*H (bellM i B B):=by
 obtain ⟨X,v,z,p,e⟩:= D.rise; have hx:= mercy i a b z e; rw [p,p,p]; simp_rw [norm_mul]; rw [mul_pow,show ‖v‖*_*(‖v‖*_) = _ from (by ring : ‖v‖*‖Fixed.functional X (bellM i A A)‖*(‖v‖*‖Fixed.functional X (bellM i B B)‖)=‖v‖^2*(‖Fixed.functional X (bellM i A A)‖*‖Fixed.functional X (bellM i B B)‖))]; exact mul_le_mul_of_nonneg_left hx (sq_nonneg _)
lemma edge (v:halfC L N x.length)(p:halfC L N y.length): price H (x*y)^2 ≤ price H (x*x.bar)*price H (y.bar*y):=by
 have he :halfC L N y.bar.length:=p
 have hk:= D.sumM x y.bar v he; have hh:=D.sumM y.bar y.bar he he; rw [bar_b] at hk hh; unfold price; rw [hk,sumM D x x v v,hh,mul_comm]; exact D.shield _ _ (material y.bar he) (material x v)
 -- ...
end Drum
end YM.CF.BProof.Chess
