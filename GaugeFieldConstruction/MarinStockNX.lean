import YM.SU5.Assay.Dawn
import YM.SU5.Thin.Operators
import GaugeFieldConstruction.Flavor
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3600
set_option linter.unusedSectionVars false
set_option maxHeartbeats 110000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace Topology Classical
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}
open YM.CF.Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal (Weaver household)
open Kea
open Flare
open YM.GaugeFieldConstruction.Matter
-- `Λbasis` Canonical 72, spin-paired arbitrary birth nonzero or not.Use D(ΦMask).
abbrev VFlavorNX:=YM.GaugeFieldConstruction.Matter.FlavorIndex
noncomputable abbrev bookColorNX (k:VFlavorNX):Op SU.Slot:= coeffs (Pi.single k 1)
namespace Lead
variable (A:Lead R)(k:VFlavorNX)(j w:Fin 2)
abbrev VLeadNX (U:SU.E) :Op SU.Slot := bookColorNX k*(matter U).val
abbrev highlightNX (N:Side)(n:SU.Slot):=basisC N A.birth (upSpin j) n
abbrev lowlightNX (N:Side)(n:SU.Slot):=basisC N A.death (dnSpin j) n
def rollNX : Weaver:=fun N U=>∑ p:SU.Slot,∑ q:SU.Slot,(VLeadNX k (A.laps U.1) p q) • (create (A.highlightNX j N p)* Fock.remove (A.lowlightNX w N q))
def batonNX (x y:Site N×SpinIdx)(U:SU.E):Op (Single N) := Matrix.of fun i l=> if i.1=x∧l.1=y then VLeadNX k U i.2 l.2 else 0
lemma baton_mvNX (x y:Site N×SpinIdx)(U:SU.E)(g:Seat N→SU.E) : twist (tradew N g) (batonNX k x y U)= batonNX k x y (g (node x.1)*U*(g (node y.1))⁻¹):=by
 let H:=tradew N g; let V:=g (node x.1)*U*(g (node y.1))⁻¹
 have he(z:SU.E)(a b:Site N×SpinIdx):tap (batonNX k x y z) a b= if a=x∧ b=y then VLeadNX k z else 0:=by ext i j; by_cases t:a=x∧ b=y <;>simp [batonNX,tap,t]
 have hp(a b:Site N×SpinIdx): tap (sings false H (batonNX k x y U)) a b= tap (batonNX k x y V) a b:=by
   change tap (sings false (portX (Equiv.refl (Site N × SpinIdx)) (fun i=>matter (g (node i.1)))) _) _ _= _; rw [tap_sg (p:=Equiv.refl (Site N × SpinIdx)) (F:=fun i=>matter (g (node i.1))),he,he]
   by_cases h:a=x ∧ b=y; swap
   · simp only [Equiv.refl_apply,if_neg h,win_z,mul_zero,zero_mul]
   obtain ⟨rfl,rfl⟩:= h; simp only [Equiv.refl_apply,true_and,if_true]; unfold V VLeadNX; rw [map_mul,map_inv,map_mul]
   let X:= matter (g (node a.1)); let Y:=matter (g (node b.1)); let D:=bookColorNX k
   have ht:X.val *D= D*X.val:= YM.GaugeFieldConstruction.Matter.coeff_ok (Pi.single k 1) (g (node a.1))
   change X.val * (D * (matter U).val) * star Y.val = D * ( X.val * (matter U).val * star Y.val)
   rw [←mul_assoc,ht]; simp only [mul_assoc]
 ext ⟨x,n⟩ ⟨y,m⟩; exact congrFun (congrFun (hp x y) n) m
lemma rolesNX (U: SU.E)(x y:Site N×SpinIdx) : dg (batonNX k x y U)=∑ i:SU.Slot,∑ j:SU.Slot,(VLeadNX k U i j) • (put (x,i)*takeF (y,j)):=by
 let f(i j:Single N):= batonNX k x y U i j • (put i * takeF j); change ∑ i,∑ j,f i j=_
 have h(a: Site N×SpinIdx)(i:SU.Slot):∑ t:Single N,f (a,i) t=∑ j:SU.Slot,f (a,i) (y,j):=by
    rw [show (∑ t : Single N,f (a,i) t)=_ from Fintype.sum_prod_type (fun k: (Site N×SpinIdx)×SU.Slot=> f (a,i) k),sum_eq_single y]
    · intro k _ p; apply sum_eq_zero; intro j _; unfold f batonNX; rw [Matrix.of_apply,if_neg (fun t=>p t.2),zero_smul]
    simp
 rw[show (∑ i: Single N,∑ j, f i j)=_ from Fintype.sum_prod_type (fun k : (Site N×SpinIdx) ×SU.Slot=>∑ j,f k j)]; simp_rw[h]
 rw[sum_eq_single x]; swap; · intro i _ q; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro l _; unfold f batonNX; rw [Matrix.of_apply, if_neg (fun p=>q p.1),zero_smul]
 swap; · simp
 apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; unfold f batonNX; rw [Matrix.of_apply,if_pos ⟨rfl,rfl⟩]
lemma crestNX (U: Fields N) : A.rollNX k j w N U=(Lifted.winding N A.birth*Lifted.winding N A.death) • dg (batonNX k (wrap N A.birth,upSpin j) (wrap N A.death,dnSpin w) (A.laps U.1)):=by
 rw [rollNX,rolesNX, smul_sum]; apply sum_congr rfl; intro p _; rw[smul_sum]; apply sum_congr rfl; intro q _
 unfold highlightNX lowlightNX basisC Fock.remove; rw [map_smul,map_smul,star_smul,create_put,create_put,Matrix.smul_mul,Matrix.mul_smul,show star (Lifted.winding N A.death)=_ from fee_real (Rush.periods N _), smul_smul,smul_smul,smul_smul]; exact congrArg (· • (put _*takeF (Lifted.index N A.death _ q))) (by unfold Lifted.winding; ac_rfl)
lemma lawNX : covariant (A.rollNX k j w N):=by
 intro g U
 rw [crestNX,crestNX]; rw [twist_scalar,dg_cov,baton_mvNX]; simp only [show (simultaneous g U).1=Lattice.gauge g U.1 from rfl,A.laps_t, travel_gauge, node_of]; rw[←wrap_stop_cover,A.moves]
#print axioms lawNX
end Lead
end YM.CF.Buffered.Ballad
end
