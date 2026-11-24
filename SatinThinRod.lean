import SatinThinShaft

set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Metric Fock Finset Lattice Lat Fir Ember Thera BPress.Spin.Blank Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
variable {M:Tulip.Male}{j K m:ℕ}{γ α R r δ:ℝ} {N:Side}

lemma windLace (U:UNI I)(Q:Op I)(f:Wave I)(h:Sea Q f): Sea (twist U Q) (acts (quantU U).val f):=by
 rw [Sea,line_twist]; exact ⟨(Fock.swivel (quantU U) (lineOp Q) f).symm.trans (by rw [h.1]),by simp only [act_unit_norm U,act_unit_norm (quantU U),h.2]⟩

def unitStem (U:UNI I): Shaft I:=⟨U.val,star U.val,U.property.2⟩
lemma era_fold (Y:Shaft I)(U:UNI I)(f:Wave I): acts (quant (Y.foldC (unitStem U)).sell) f=acts (quant Y.sell) (acts (quantU U).val f):=by unfold Shaft.foldC unitStem; rw [quant_mul,act_mul]; rfl
lemma bra_fold (Y:Shaft I)(U:UNI I)(f:Wave I): acts (quant (star (Y.foldC (unitStem U)).buy)) f=acts (quant (star Y.buy)) (acts (quantU U).val f):=by unfold Shaft.foldC unitStem; rw [star_mul,star_star,quant_mul,act_mul]; rfl
lemma craftE (A:Op (Single N))(S:ColumnDeal A R)(n:Seat N→ SU.E) : ColumnDeal (A*(tradew N n).val) (45*R):=by
 constructor; intro i; rw [act_mul]; let U:=tradew N n; let x:=basisKet i; let V:= acts U.val x
 have he: V= ∑ j:Slot,V.ofLp (i.1,j) • basisKet (i.1,j):=by
    nth_rw 1 [←basis_expand V]; unfold Single; rw [Fintype.sum_prod_type];
    rw [sum_eq_single i.1]; · intro l z d; apply sum_eq_zero; intro j h; unfold V x U; rw [basis_act]; simp only [tradew, jump_apply,Equiv.refl_apply,if_neg d,zero_smul]
    simp
 change ‖acts A V‖ ≤ _; rw [he,map_sum]; apply (norm_sum_le ..).trans; apply le_trans (b:=∑ j:Slot,R) (sum_le_sum (fun j h=>?_)); · rw [sum_const,card_univ,slots,nsmul_eq_mul]; norm_num
 rw [map_smul,norm_smul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_) (S.all (i.1,j)); exact (PiLp.norm_apply_le V _).trans_eq (by unfold V x; rw [act_unit_norm]; simp [basisKet])

local notation "K"=>spar j M (1:Pane N)
variable (V:Op (Single N))(g:Seat N→ SU.E) (p:IsStarProjection (spar j M (1:Pane N)))(z:postage j R)

lemma paint_stays : (Saber (B:=tickA N) p m).sell*K=K:=by
 unfold Saber; simp only [add_mul,one_mul]; rw [show star (Comb _ K m)*K=0 from ?_,add_zero]
 nth_rw 2 [←p.isSelfAdjoint.star_eq]; rw [←star_mul,comb_px p,star_zero]
include z
lemma postal (m:ℕ) :
 let T:= Saber (B:=tickA N) p m; ColumnDeal T.sell (1+R) ∧ ColumnDeal (star T.buy) (1+R):=by
 intro T; unfold T Saber; simp only [star_sub, star_star,star_one]
 constructor
 · constructor; intro i; rw [act_add,act_one]; apply (norm_add_le ..).trans; rw [show ‖basisKet i‖=1 from by simp [basisKet]]; exact add_le_add_right ((z _ _ _ p _).2) 1
 constructor; intro i; rw [act_sub,act_one]; apply (norm_sub_le ..).trans; rw [show ‖basisKet i‖=1 from by simp [basisKet]]; exact add_le_add_right ((z _ _ _ p _).1) 1
omit z

def metroS (m:ℕ): Shaft (Single N) := (Saber (B:=tickA N) p m).foldC (unitStem (tradew N g))
include z
lemma metroBuy (m:ℕ) : ColumnDeal (metroS g p m).sell (45*(1+R)) ∧ ColumnDeal (star (metroS g p m).buy) (45*(1+R)):=by
 constructor
 · exact craftE _ (postal p z m).1 g
 unfold metroS Shaft.foldC unitStem; simp only [star_mul,star_star]; apply craftE; exact (postal p z m).2
omit z
lemma metro_mate (m:ℕ) : ‖acts (quant (star (metroS g p m).buy)) (mateK N)‖=Real.exp (stunt m (tickA N) K):=by
 let f:= mateK N; let Z:=tickA N; let U:= tradew N g; let v:=acts (quantU U).val f; have he:Sea Z v:=by
    have hv:= windLace U Z f (tickB N); rwa [Cascade.tick_g] at hv
 unfold metroS; rw [bra_fold, show star (Saber (B:=tickA N) p m).buy=1-(Comb Z K m) from ?_]; exact purse p (Cascade.plus_P N) m v he
 unfold Saber; simp; rfl
include z
lemma metro_windE (V:Op (Single N))(q:IsStarProjection (twist (tradew N g) V))(x:Wave (Single N))(t:Sea V x)(m:ℕ):
 ‖acts (quant (metroS g p m).sell) x‖ ≤ Real.exp (((1+R)^2+1)*revE (twist (tradew N g) V-K)/2):=by
 unfold metroS; rw [era_fold]; exact sea_gain K _ _ _ _ q p (windLace _ V x t) (postal p z _).1 (paint_stays p)
end YM.CF.Papyrus.Franc
#print axioms YM.CF.Papyrus.Franc.metro_windE
