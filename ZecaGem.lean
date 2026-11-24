import ZecaFilm
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "κ"=> P.calibration
local notation "ℓ"=> (κ).ℓ
local notation "R"=> ruler P.par.block
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> marks (timeMesh P.par)
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "X"=> P.ColorHil j x

local notation "E"=> (P.physicalEnergy j x).E

variable (D:P.Apron)
local notation "ET" => (P.seasons j x).E
local notation "G" => P.ManyF j x
local notation "r"=> D.realWidth P j

local notation "K"=>P.wealth j x
local notation "η"=>P.enter j x
local notation "C"=>P.cartage j x
def coffer : (P.ColorHil j x).Op →ₗ[ℂ] (P.ManyF j x).Op where
 toFun T:= (P.wealth j x).comp (T.comp (P.enter j x).toContinuousLinearMap)
 map_add' S T:=by rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
 map_smul' z T:=by
   change _ = z • _
   rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
lemma coffer_pay(T:(P.ColorHil j x).Op): ‖P.coffer j x T‖≤‖T‖:=by
 have p:=P.tableau_pay j x T 0
 unfold tableau at p; rw [neg_zero,P.cart_zero] at p; exact p
lemma gem_truck(z:P.VMark)(a:X): P.wealth j x (P.truck j x z a)=C (P.laysM z) (K a):=by rw [P.uses_cart];exact (P.roll_motion j x (z ∘ Subtype.val) a).symm
lemma coffer_charter(z:P.VMark)(A:(P.ColorHil j x).Op):
 P.coffer j x (P.charter j x z A)=P.tableau j x (P.laysM z) A:=by
 ext1 y
 change K (P.truck j x z (A (P.truck j x (-z) (η y)))) =_
 rw [P.gem_truck,P.cart_and,P.lays_neg];rfl

lemma coffer_heat (S:(P.ColorHil j x).Op)(a d:ℝ≥0):
   P.coffer j x (E a * S * E d)=ET a * (P.coffer j x S)*ET d:= by
 ext1 y
 change P.bank j x (E a (S (E d (η y)))) = _
 rw [P.bankHeat,←P.soleHeat]; rfl
lemma coffer_rawCat (z:P.VMark)(a b:ℝ):
  P.coffer j x (P.rawCat j x D z a b)= P.ruby j x D (P.laysM z) a b:=by
 unfold rawCat innerCut ruby; rw [P.coffer_heat,P.coffer_charter]
lemma coffer_innerCut (a b:ℝ):
 P.coffer j x (P.innerCut j x D a b (D.engine P j x))=P.ruby j x D 0 a b:=by
 unfold ruby tableau innerCut
 rw [P.coffer_heat,neg_zero,P.cart_zero];rfl

section utility
variable {M:Hilbert}
def bun (X₁ X₂:M.Op): M.Op →ₗ[ℂ] M.Op:={
 toFun:=fun A=>X₁*A*X₂
 map_add':=by intros; rw [mul_add,add_mul]
 map_smul':=by intro z A; rw [mul_smul_comm,smul_mul_assoc]; rfl}
lemma bun_here (a b c:M.Op):bun a b c=a*c*b:=rfl
lemma bun_le {a b:M.Op}(h:‖a‖≤1)(g:‖b‖≤1)(c:M.Op):
  ‖bun a b c‖≤ ‖c‖:=by
 calc
  _ ≤ ‖a*c‖ := (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) g)
  _ ≤ _ := (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) h)
lemma bun_bun (a b c d e:M.Op):bun a b (bun c d e)=bun (a*c) (d*b) e:=by
 simp only [bun_here, mul_assoc]
lemma bun_one (e:M.Op):bun 1 1 e=e:=by rw [bun_here,one_mul,mul_one]
end utility
abbrev dazzle (u:Vantage):=(bun (M:=P.ManyF j x) (P.cartage j x u) (P.cartage j x (-u)))
abbrev buff(a b:ℝ):=(bun (M:=P.ManyF j x)
    ((P.seasons j x).E a.toNNReal)
    ((P.seasons j x).E b.toNNReal))
local notation "ds"=>P.dazzle j x
local notation "vf"=>P.buff j x

lemma dazzle_pay(y:Vantage)(T:(P.ManyF j x).Op): ‖P.dazzle j x y T‖ ≤ ‖T‖ := bun_le (P.cart_pay j x _) (P.cart_pay j x _) T
lemma buff_pay(a b:ℝ)(T:(P.ManyF j x).Op):‖P.buff j x a b T‖≤‖T‖:=
    bun_le ((P.seasons j x).shrinks _) ((P.seasons j x).shrinks _) T
lemma dazzle_zero(T:(P.ManyF j x).Op):P.dazzle j x 0 T=T:=
  (congrArg₂ (fun U V=>(bun (M:=P.ManyF j x) U V T)) (P.cart_zero ..)
      (Eq.trans (congrArg _ (neg_zero)) (P.cart_zero j x))).trans (bun_one (M:=P.ManyF j x) T)
lemma cart_join (y z:Vantage):C y*C z=C (y+z):= (P.cart_paves ..).symm
lemma cart_hours(y:Vantage)(b:ℝ≥0): ET b * C y=C y * ET b:=by
 rw [P.uses_cart]; exact (P.seasons j x).independent b _
lemma dazzle_join(y z:Vantage)(T:(P.ManyF j x).Op):P.dazzle j x y (ds z T)=ds (y+z) T:=by
 unfold dazzle; rw [bun_bun, P.cart_join,P.cart_join, neg_add_rev]
lemma dazzle_buff (z:Vantage)(a b:ℝ)(T:(P.ManyF j x).Op):ds z (vf a b T)=vf a b (ds z T):=by
 unfold buff dazzle
 rw [bun_bun,bun_bun,P.cart_hours,P.cart_hours]

lemma hot_TT {u v w:ℝ} (p:u+v=w)(h:0≤u)(g:0≤v):
     ET u.toNNReal*ET v.toNNReal=ET w.toNNReal:= by
   rw [←p,Real.toNNReal_add h g]
   exact ((P.seasons j x).time ..).symm
lemma buff_join {a b c d e f:ℝ}(i:a+c=e)(o:d+b=f)(p:0≤a)(q:0≤b)(v:0≤c)(k:0≤d)
  (T:(P.ManyF j x).Op) :
     P.buff j x a b (P.buff j x c d T)=P.buff j x e f T:=by
   unfold buff; rw [bun_bun,P.hot_TT j x i p v,P.hot_TT j x o k q]
lemma dazzled (z:Vantage) (T:(P.ColorHil j x).Op):
        ds z (P.coffer j x T)=P.tableau j x z T:=rfl
lemma ruby_price(y:Vantage)(a b:ℝ): P.ruby j x D y a b=
      vf (a-D.realWidth P j) (b-D.realWidth P j)
      (ds y (P.coffer j x (D.engine P j x))):=rfl
lemma ruby_turn (y z:Vantage)(a b:ℝ): P.dazzle j x z (P.ruby j x D y a b)=
    P.ruby j x D (z+y) a b:=by
 rw [P.ruby_price,P.dazzle_buff,P.dazzle_join,P.ruby_price]

lemma ruby_large {a b c d:ℝ} (e v:ℝ) (i:e+a=c)(o:b+v=d)
       (p:0≤e)(q:0≤v)(h:D.realWidth P j ≤ a)(t:D.realWidth P j ≤ b)
       (y:Vantage): P.buff j x e v (P.ruby j x D y a b)=P.ruby j x D y c d:=by
 rw [P.ruby_price,P.buff_join j x (by rw [← add_sub_assoc,i])
     (by rw [sub_add_eq_add_sub,o]) p q (sub_nonneg.mpr h) (sub_nonneg.mpr t),P.ruby_price]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
