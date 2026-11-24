import Anomaly.Ward.Fern
import YM.SU5.Regis.Visions
import YM.CF.Reef.Tes
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill Sour
open Nacre Next.Free Exterior Precision Wilson _root_.Zephyr.Chern SpectrumQ
open Ione.Clock Hove Spire Regis.Head
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace PotQ
-- H pull on Tangent p. also P*(scalar cost)
variable (s:Sweep n)
local notation "G"=>SU.group
local notation "N"=> More n
local notation "Xq"=> fieldDir G (More n) 1
-- local notation "τb"=> (assembly n).embed s.b

def sailH (U:Xq):Xq:=if s.charge then Reef.cloak _ (bank s.s ((assembly n).embed s.b) U) else bank s.s ((assembly n).embed s.b) U
lemma colorTravel (U:Xq)(a:ℝ): represent (a • sailH s U)=flashA s (represent (a • U)):=by
 unfold sailH; rw [revoke]; cases p:s.charge
 · exact bank_at ..
 change represent (a • Reef.cloak _ _)=Reef.echo _; rw [←map_smul, Reef.repr_c,bank_at]
lemma curlEcho (U:Xq)(i: Face (Per N)): Work.F03.faceCurl i (Reef.cloak _ U)=Reef.frolic (Work.F03.faceCurl i U):=by
 rw [show Work.F03.faceCurl i U= linkSum (collect SU.group U) i.1 (square i.2.val.1 i.2.val.2) from (fundamental ..).symm, show Work.F03.faceCurl i _= _ from (fundamental G (Reef.cloak _ U) i.1 i.2).symm]
 exact trop i.1 _
where trop(x: Site (More n))(w:Walk):linkSum (collect G (Reef.cloak _ U)) x w=Reef.frolic (linkSum (collect G U) x w):=by
       induction w generalizing x with
       | nil=> rw [linkSum,linkSum,map_zero]
       | cons i l e=> rw [linkSum,linkSum,e,map_add]; split_ifs; rw [map_neg]; rfl; rfl

def budge (b: Face (Per (More n))) := Face.send s.s ((assembly n).embed s.b) b
lemma budCurl (p:Face (Per (More n)))(U:Xq):Work.F03.faceCurl p (bank s.s ((assembly n).embed s.b) U)= turned s.s p.2 • Work.F03.faceCurl (budge s p) U:=by
 let e:= Face.send s.s 0 p; let x:= s.s; let W:= arbor ((assembly n).embed s.b) U
 have he: Work.F03.faceCurl p (bank x ((assembly n).embed s.b) U)= turned x p.2 • Work.F03.faceCurl e W:=by
    ext i; change (d 1 _ *ᵥ (parts _ _ (Bid.pulled W x) i)) _= turned _ _ *(d 1 _*ᵥ(parts _ _ W i)) _; rw [pigment]; exact rotations_d ..
 refine he.trans (congrArg (fun i=> turned x p.2 • i) ((face_drift ((assembly n).embed s.b) U e.2 e.1).trans ?_)); unfold budge e Face.send Face.lower atFace affine; dsimp only; simp only [add_zero]; -- Φ target floors
 apply congrArg (fun i=>Work.F03.faceCurl (i,p.2.rotate x) U); abel -- tune
abbrev colorCL (b:Bool): SU.group.Color →L[ℝ] SU.group.Color:= if b then Reef.frolic.toContinuousLinearMap else ContinuousLinearMap.id ℝ _
lemma cable (A:Xq)(j:Face (Per (More n))) :
 Work.F03.faceCurl j (sailH s A)= turned s.s j.2 • colorCL s.charge (Work.F03.faceCurl (budge s j) A):=by unfold sailH; cases s.charge <;> simp only [ite_false,Bool.false_eq_true,ite_true]; exact budCurl ..; rw [curlEcho,budCurl,map_smul]; rfl
lemma budgetHi (X:Face (Per N)): separation (boxA s X.1) (budge s X).1≤2:=by
 have h := Work.H03.touched_send s.s ((assembly n).embed s.b) X; have ht : boxA s X.1 ∈ touched (budge s X):=by unfold budge; rw [h,sitA]; exact mem_image_of_mem _ (Work.E01.base_touched _)
 -- likely lemma.\n
 rw [separation_comm]; exact Work.E01.sep_touched _ _ ht
lemma colorDef (b:Bool)(x:SU.group.Color):‖colorCL b x‖=‖x‖:=by cases b; rfl; exact Reef.frolic.norm_map x
local notation "ι"=> SU.group.ColorIndex
abbrev corn (x:ι): SU.group.Color:=EuclideanSpace.basisFun ι ℝ x
abbrev threadQ (i:Face (Per N))(a b: ι):ℝ:= turned s.s i.2 * (colorCL s.charge (corn b)) a
def movesT(i:TrackKey G N)(b:SU.group.ColorIndex): TrackKey G N:=(budge s i.1,b)
lemma tuneQ (i:TrackKey G N)(b:SU.group.ColorIndex):|threadQ s i.1 i.2 b| ≤ 1:=by
 unfold threadQ; rw [abs_mul]; have ht:|turned s.s i.1.2|=1:=by nlinarith [sq_abs (turned s.s i.1.2),abs_nonneg (turned s.s i.1.2),turned_sq s.s i.1.2]
 rw [ht,one_mul]; calc
 _ = |inner ℝ (corn i.2) (colorCL s.charge (corn b))|:=by rw [EuclideanSpace.basisFun_inner] -- tune
 _ ≤ _:= abs_real_inner_le_norm _ _
 _ = _:=by rw [colorDef]; simp [corn]
lemma costTravel (A:Xq)(b:TrackKey G N):
 receipt (sailH s A) b=∑ i,threadQ s b.1 b.2 i * receipt A (movesT s b i):=by
 let W:= Work.F03.faceCurl (budge s b.1) A; let L:= EuclideanSpace.basisFun ι ℝ; let T:=colorCL s.charge; have hp: W=∑ i:ι,W i • corn i:=by
    refine Eq.trans (Eq.symm (L.sum_repr W)) ?_; congr! 2 -- tune
 unfold receipt; rw [cable]; change turned s.s b.1.2 * T W b.2=_ -- binder f
 let Q: SU.group.Color→L[ℝ] ℝ := EuclideanSpace.proj b.2
 change turned s.s b.1.2 * Q (T W)=_
 nth_rw 1 [hp]; rw [map_sum,map_sum]; simp_rw [map_smul,smul_eq_mul,mul_sum]; exact sum_congr rfl fun i _=> by unfold threadQ; change turned _ _*(W i *(colorCL s.charge _) _) = _ * W i; ring -- tune
variable {q:Xq} (T: tableQ G (More n) ℂ)
-- transported stencil's TRUE quadratic probe. Off orientations opaque may pay more radius.
lemma branchQ (U:Site N)(b:ℕ) (v:Regional U b T):∃ D: tableQ G (More n) ℂ, costs D ≤ (Fintype.card ι:ℝ)^2*costs T ∧ Regional (boxA s U) (b+2) D ∧ ∀ Q:Xq, tariff T (receipt (sailH s Q))=tariff D (receipt Q):=by
 let F:= ChainKey G (More n); let C:= Fin 2→ SU.group.ColorIndex; let K(j:F)(k:C):F:=fun i=> movesT s (j i) (k i); let H(j:F)(k:C):ℂ:=(∏ i: Fin 2,threadQ s (j i).1 (j i).2 (k i)) • T j
 let D(i:F):=∑ j:F,∑ k:C,if K j k=i then H j k else 0
 have hv(j:F)(k:C): ‖H j k‖ ≤ ‖T j‖:=by unfold H; rw [norm_smul,Real.norm_eq_abs,abs_prod]; exact mul_le_of_le_one_left (norm_nonneg _) (prod_le_one (fun _ _=>abs_nonneg _) (fun i _=> tuneQ s (j i) (k i)))
 refine ⟨D,?_,?_,?_⟩
 · have hh(i:F): ‖D i‖ ≤ ∑ j:F,∑ k:C, if K j k=i then ‖H j k‖ else 0:=by
      apply (norm_sum_le ..).trans; simp_rw [← norm_zero (E:=ℂ)] -- norm_zero syntax
      exact sum_le_sum fun j _=> (norm_sum_le ..).trans_eq (sum_congr rfl fun k _=> apply_ite ..)
   refine (sum_le_sum (fun i _=> hh i)).trans ?_; rw [sum_comm]; unfold costs; rw [mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [sum_comm];
   have he(j): (∑ z:F, if K i j=z then ‖H i j‖ else 0)=‖H i j‖:=by rw [sum_eq_single (K i j)]; simp; intro b _ p; rw [if_neg p.symm]; simp
   simp_rw [he]; refine (sum_le_sum (fun j _=> hv i j)).trans (?_); simp [C]
 · intro i p j; obtain ⟨k,_,q⟩:= exists_ne_zero_of_sum_ne_zero p; obtain ⟨l,_,u⟩:=exists_ne_zero_of_sum_ne_zero q; split at u; swap; exact (u rfl).elim
   rename_i h; subst i; have ht:(k j).1.1 ∈ halo b {U}:=v k (fun h=> u (by simp [H,h])) j
   refine Next.Rank.Spindle.doors _|>.mpr ?_; change separation (boxA s U) (budge s (k j).1).1 ≤ _; exact (separation_triangle _ (boxA s (k j).1.1) _).trans (Nat.add_le_add ((sitT ..).trans_le (Next.Rank.Spindle.doors _|>.1 ht)) (budgetHi ..))
 intro L; let Z:=receipt L
 unfold tariff; unfold D; simp_rw [costTravel, Fintype.prod_sum, Finset.sum_smul, Finset.smul_sum]; rw [sum_comm (f:=fun i j=> ∑ y:C,(∏ z:Fin 2,Z (i z)) • (if K j y=i then H j y else 0))]; apply sum_congr rfl; intro i _
 rw [sum_comm (f:=fun j (y:C)=>_)]; apply sum_congr rfl; intro j _; rw [sum_eq_single (K i j)]
 · unfold H; simp only [if_true,prod_mul_distrib]; rw [smul_smul]; apply congrArg (· • T i); rw [mul_comm]; -- tune
 intro b _ p; rw [if_neg p.symm,smul_zero]
 simp
end PotQ
end YM.CF.Swell.Sonar
