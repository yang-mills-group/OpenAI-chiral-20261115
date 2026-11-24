import SatinPP.Stock
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry


section
variable {X:Hilbert}{j:Axis}(S:OS.Semigroup X j)
local notation "E"=>S.E

def jacket (u v:ℝ): X.Op →ₗ[ℂ] X.Op where
 toFun A:= E u.toNNReal * A * E v.toNNReal
 map_add' x y:=by rw [mul_add, _root_.add_mul]
 map_smul' c A:=by change _=c • _; rw [mul_smul_comm,smul_mul_assoc]

local notation "J"=>jacket S
lemma jacket_go {u v s t:ℝ}(a:0 ≤ u)(b:0 ≤ v)(c:0 ≤ s)(d:0 ≤ t)(A:X.Op):
    J (u+s) (v+t) A = J u v (J s t A):=by
 have h₀:(u+s).toNNReal=u.toNNReal+s.toNNReal:=by ext; simp [a,c]
 have h₁:(v+t).toNNReal=t.toNNReal+v.toNNReal:=by ext; simp [b,d,add_comm v]
 change E ((u+s).toNNReal) * _ * E ((v+t).toNNReal)=_
 rw [h₀,h₁,S.time,S.time]; rfl

lemma jacket_cost (u v:ℝ)(A:X.Op):‖J u v A‖  ≤  ‖A‖:=by
    exact (norm_mul_le (E (u.toNNReal) * A) (E (v.toNNReal))).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (S.shrinks _)).trans
       ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))))



lemma jacket_widen {u v s t:ℝ}(a:0 ≤ s)(b:0 ≤ t)(c:s ≤ u)(d:t ≤ v)(A:X.Op):
    J u v A = J (u-s) (v-t) (J s t A):=by
 rw [←jacket_go _ (sub_nonneg.mpr c) (sub_nonneg.mpr d) a b,sub_add_cancel,sub_add_cancel]

lemma jacket_le {u v s t:ℝ}(a:0 ≤ s)(b:0 ≤ t)(c:s ≤ u)(d:t ≤ v)(A:X.Op):
    ‖J u v A‖  ≤  ‖J s t A‖:=by rw [jacket_widen S a b c d]; exact jacket_cost ..

lemma jacket_zero (A:X.Op):J 0 0 A=A:=by
 change E _ * A * E _=A; simp only [Real.toNNReal_zero,S.eZero]; rfl
end

namespace Spine
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "X"=>P.ColorHil j x
local notation "Y"=>P.physicalEnergy j x
local notation "T"=>timeMesh P.par
/-- Left and right thermal wall distances measured from time-mark center
in CP18 clock units. Below intrinsic width, decoating not asserted; the
def uses width as floor. -/
def locket (A:P.Apron)(s t:ℝ):(P.ColorHil j x).Op:= jacket (P.physicalEnergy j x) (s-A.realWidth P j) (t-A.realWidth P j) (A.engine P j x)




lemma widen_locket (A:P.Apron){a b s t:ℝ}
 (h:A.realWidth P j ≤ s)(k:A.realWidth P j ≤ t)(u:s ≤ a)(v:t ≤ b):
    P.locket j x A a b = jacket Y (a-s) (b-t) (P.locket j x A s t):=by
 unfold locket
 rw [jacket_widen Y (sub_nonneg.mpr h) (sub_nonneg.mpr k) (sub_le_sub_right u _) (sub_le_sub_right v _),sub_sub_sub_cancel_right,sub_sub_sub_cancel_right]




lemma charter_ge (z:P.VMark)(A:(P.ColorHil j x).Op):‖A‖ ≤ ‖P.charter j x z A‖:=by
 apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
 intro y
 let K:=P.truck j x z y
 rw [←P.truck_norm j x z (A y),← P.truck_norm j x z y]
 have h:P.truck j x (-z) K=y:=by
    unfold K; rw [←ContinuousLinearMap.comp_apply, ← P.truck_paves, neg_add_cancel, P.truck_zero]; rfl
 have he:= (P.charter j x z A).le_opNorm K
 change ‖P.truck j x z (A (P.truck j x (-z) K))‖ ≤ _ at he
 rwa [h] at he
lemma charter_inside (s t:ℝ)(z:P.VMark)(A:(P.ColorHil j x).Op):
 P.charter j x z (jacket Y s t A) = jacket Y s t (P.charter j x z A):=by
 apply ContinuousLinearMap.ext; intro y
 change P.truck j x z ((Y).E _ (A ((Y).E _ (P.truck j x (-z) y))))=
    (Y).E _ (P.truck j x z (A (P.truck j x (-z) ((Y).E _ y))))
 rw [P.sixWard_truck_heat,P.sixWard_truck_heat]
lemma locket_own (A:P.Apron):
    P.locket j x A (A.realWidth P j) (A.realWidth P j)=A.engine P j x:=by
 unfold locket; rw [sub_self,jacket_zero]


variable (A:P.Apron)(n:ℕ)(r:Cover)
local notation "u"=> A.zoom P n j
local notation "S"=>P.shifts j
local notation "R"=>A.realWidth P j

/-- At natural mesh left & right buys a,b advancing to wall distances l,k. -/
lemma transport_stock {l k:ℕ}(dn:A.s ≤ n)(hl:u ≤ l)(hk:u ≤ k):
    P.Stock j x n (l+k) (S ((l:ℤ)-r j) (P.chartAll r (A.full P n)))
      (P.charter j x (P.vtile n r) (P.locket j x A (bell T n l) (bell T n k))):=by
 let w:=u
 let Z:=P.chartAll r (A.full P n)
 let t:=P.vtile n r
 have hp:=A.zoomP P j n
 obtain ⟨f,ad,ed,e⟩:=A.transported P j x n dn r
 have st:P.Stock j x n (w+w) (S ((w:ℤ)-r j) Z) (P.charter j x t (A.engine P j x)):=by
    unfold t Z w; rw [e,←ed]
    exact stock_door _ _ ad
 let a:=l-w; let b:=k-w
 have he:a+w=l:=Nat.sub_add_cancel hl
 have hb:w+b=k:=Nat.add_sub_of_le hk
 have q₁:S ((l:ℤ)-r j) Z = S a (S ((w:ℤ)-r j) Z):=
    (by rw [P.shifts_sum]; congr 2; omega)

 have hl (c d:ℕ)(e:c=w+d):(bell T n c-R).toNNReal=whenly T n d:=by
    refine Eq.trans (congrArg Real.toNNReal ?_) Real.toNNReal_coe -- tune NNReal method
    rw [←A.zoom_bell P j n dn]; refine Eq.trans ?_ (natural_time T n d)
    simp [e,bell,w,_root_.add_mul]
 have hv:=st.attach a b
 rw [←q₁,show a+(w+w)+b=l+k from by omega,← hl l a (by omega),←hl k b hb.symm] at hv
 unfold locket; rw [charter_inside]
 exact hv

lemma locket_stock {l k:ℕ}(dn:A.s ≤ n)(hl:u ≤ l)(hk:u ≤ k):
    P.Stock j x n (l+k) (S l (A.full P n)) (P.locket j x A (bell T n l) (bell T n k)):=by
 let y:=A.full P n
 have hy:P.chartAll 0 y=y:= by
    suffices ∀ t:List Axis,P.cruise t 0 y=y from this _
    intro t; induction t with
    | nil=>rfl
    | cons a t ih=>rw [P.cruise_step,AlgHom.comp_apply,ih,Pi.zero_apply,P.shifts_zero]
 have ht:P.vtile n 0=0:=by funext i; change notch T n 0=0; ext; simp [notch,bell]
 have h:=P.transport_stock j x A n 0 dn hl hk
 unfold charter at h
 rw [ht,hy,Pi.zero_apply,sub_zero,neg_zero,P.truck_zero,ContinuousLinearMap.id_comp,ContinuousLinearMap.comp_id] at h
 exact h

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
