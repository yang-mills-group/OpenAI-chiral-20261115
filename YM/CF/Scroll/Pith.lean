import YM.CF.Scroll.Camp
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable {b r:Bool}{N P: Side}(G:Ratio N P)(ho:Odd G.count.val)(a:Shape)(u:ColorT b)(U:UNI SpinIdx)(p:JetS a.s b r U)
lemma hoodL : sings b (pflux a G U u) (hood G)=hood G:=by
 rw [hood]; rw [clampS]; rw [singT,win_i,map_one]
variable (j:ℕ)(hj:1≤j)
def PaidG(e:ℝ)(x:Bkg (More N)):Prop:=Safe (dome N (profile x)) ∧∀ M:Male,Safe (art N j M.val (profile x))
include p hj in
lemma skew_lobe (M:Male)(x:Bkg (More N))(e:ℝ)(H:∀ x:Bkg (More N),Guard x e→PaidG j e x)(v:Guard x e)(k:Bool): sings b (prepU a U u N) (skewE j M k N (profile x))=skewE j M (r.xor k) N (profile (stir u a x)):=by
 have hp:= funde_f a u U p x j hj M e H v
 cases k; swap; cases r; exact hp; exact hp
 change sings b _ (1-funde _ _ _ _)=_; rw [singT,win_l,win_i,map_sub,map_one,←singT,hp]; cases r; rfl; unfold swapX; simp [skewE]
lemma singm {I:Type*}[Fintype I][DecidableEq I](p:Bool)(X:UNI I)(A B:Op I): sings p X (A*B)=sings p X A * sings p X B :=by simp only [singT,win_m,map_mul]
lemma singsUnit {I:Type*}[Fintype I][DecidableEq I](p:Bool)(X:UNI I)(A:Op I)(h:IsUnit A): sings p X A⁻¹=(sings p X A)⁻¹:=by
 refine Eq.symm (Matrix.inv_eq_right_inv ?_); rw [←singm,(live h).1,singT,win_i,map_one]
include p ho in
lemma titles (M:Male)(x:Nom N P)(k:Bool)(v:IsUnit (Peaks.cloth j M G (unionP x))): sings b (pflux a G U u) (ticketT (Peaks.cloth j) k M G (unionP x))=ticketT (Peaks.cloth j) (r.xor k) M G (unionP (stanza G a u x)):=by
 let V:= Peaks.cloth j M G (unionP x); let X:=pflux a G U u
 have he:=clothing _ ho a u U p j M x
 unfold ticketT; rw [revI,revI]
 simp only [singT,win_a,win_l,win_s,win_i,win_m,map_add,map_sub,map_star,map_one,map_mul]; rw [←singT b X V⁻¹,←singT b X V] -- maybe tune
 change sings _ _ V⁻¹ *_+star (sings _ _ V)*(1-_)= _
 rw [singsUnit b X V v,show sings _ _ V=_ from he, ← singT, taxL _ a u U p] -- tune
-- only % used for all step. use Stamped
variable (M: Male)(e:ℝ) (x:Nom N P) (v:JointB G x e)
include p ho hj v in
lemma hoarD (H:∀ x:Bkg (More N),Guard x e→PaidG j e x)(hp:∀ x:Bkg (More P),Guard x e→PaidG j e x)(k:Bool) : sings b (pflux a G U u) (foal j k M G (unionP x))=foal j (r.xor k) M G (unionP (stanza G a u x)) ∧ sings b (pflux a G U u) (wh j G.count ho k M G (unionP x))= wh j G.count ho (r.xor k) M G (unionP (stanza G a u x)):=by
 have hg: JetS (Shape.broad G a).s b r U:=p
 constructor
 · rw [foal,foal,portFoot G ho]; change foot G (sings _ _ (skewE j M k P (profile x.1)))=_; rw [skew_lobe _ u U hg j hj M _ e hp v.fg]; rfl
 rw [wh,wh,singT,win_a,map_add,←singT, ←singT,singm,taxL G a u U p,clampS]; let Y:= upMale G.count ho M
 rw [singT _ (pflux a G U u),win_l,map_sub,win_i,map_one,←singT,hoodL]; unfold unionP
 change _+ endorse G (sings b (prepU a U u N) (skewE j Y k N (profile x.2)))=_; rw [skew_lobe _ _ _ p _ hj Y _ e H v.cg]; rfl
end YM.CF.Scroll
