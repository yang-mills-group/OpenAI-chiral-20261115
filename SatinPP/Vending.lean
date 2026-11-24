import SatinPP.Pearl
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

open Anvil (Limited Pearl)
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 3)
local notation "ξ"=>P.advocate 3 x j
local notation "X"=>P.ColorHil j (P.advocate 3 x j)
local notation "ω"=>P.colorZero j ξ
local notation "H"=>P.ManyF j (P.advocate 3 x j)
local notation "S"=>P.physicalEnergy j (P.advocate 3 x j)
local notation "Ε"=>P.seasons j (P.advocate 3 x j)
local notation "π₁"=>P.wealth j ξ
local notation "λ'"=>P.enter j ξ
def seating (A:(X).Op):(H).Op:= (π₁).comp (A.comp (λ').toContinuousLinearMap)
local notation "Φ"=>P.seating j x

lemma seating_cost (A:(X).Op):‖Φ A‖≤ ‖A‖:=by
 apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro y
 exact (P.bank_cost j ξ _).trans ((A.le_opNorm ((λ') y)).trans_eq (congrArg (‖A‖ * ·) ((λ').norm_map y)))



lemma inner_seating(y z:H)(A:(X).Op): inner ℂ y (Φ A z)=inner ℂ ((λ') y) (A ((λ') z)):=by
 let V:=P.visitors j ξ
 change inner ℂ ((λ') y) (V (A ((λ') z)))=_
 rw [←ContinuousLinearMap.adjoint_inner_left,
    show V.adjoint=V from (P.voyageF j ξ).symmetricstack _,
    show V _ = (λ') y from (P.voyageF j ξ).grounded _ y.property]

lemma seating_star (A:(X).Op):Φ (star A)=star (Φ A):=by
 apply ContinuousLinearMap.ext; intro y; apply ext_inner_left ℂ; intro u
 rw [inner_seating,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.star_eq_adjoint,
     ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
 exact (congrArg (starRingEnd ℂ) (P.inner_seating j x y u A) |> fun h=>by simpa using h.symm)

lemma seating_jacket (u v:ℝ)(A:(X).Op):Φ (jacket (S) u v A)=jacket (Ε) u v (Φ A):=by
 apply ContinuousLinearMap.ext; intro y
 change P.bank _ _ ((S).E _ (A ((S).E _ _)))=_
 exact P.bankHeat ..


lemma seating_Limited {l:Filter ℕ}{A:ℕ→(X).Op}{D:(X).Op}
   (t:Limited l A D): Limited l (fun n=>Φ (A n)) (Φ D):=by
 obtain ⟨M,p,h⟩:=t.uniform
 refine ⟨⟨M,p,h.mono fun i y=> (P.seating_cost j x _).trans y⟩,fun a b=>?_⟩
 simp_rw [inner_seating]; exact t.confirms _ _

def seats (D:Stamp (X)):Stamp (H):= fun u v=>Φ (D u v)
lemma seats_paid {D:Stamp (X)}{c:ℝ}{m:ℕ}(t:Paid (S) m c D): Paid (Ε) m c (P.seats j x D):=by
 refine ⟨t.pos,fun a b h g=> ?_,fun a p=>(P.seating_cost j x _).trans (t.le a p)⟩
 unfold seats; rw [t.fits a b h g,seating_jacket]

local notation "Ω"=>P.heaven j ξ
variable (V:∀ i:Axis,List Axis → ℝ→P.ColorHil i (P.advocate 3 x i))(A:ℕ→ P.Apron)
variable {B:ℝ}{D:Concert P x}(l:List Axis)

structure Seated (C:Stamp H)(B:ℝ): Prop where
 paid:Paid (Ε) 5 B C
 vacuum{u v:ℝ}(a:0<u)(b:0<v): C u v Ω= π₁ (V j l u)
 vacuum'(u v:ℝ)(a:0<u)(b:0<v): star (C u v) Ω= π₁ (V j (j::l) v)
 actual(u v:ℝ)(a:0<u)(b:0<v):Limited (finalReel:Filter ℕ)
   (fun i=> Φ (P.locket j ξ ((A i).pivot P l) u v)) (C u v)

variable {V A P x}
lemma ConcertPlays.seated (C:P.ConcertPlays x A B D)(h:Radiates P x A V):
    P.Seated j x V A l (P.seats j x (D j l)) B:=by
 refine ⟨P.seats_paid j x (C.paid ..),
   fun a b=>congrArg (π₁) (C.vacuum _ _ h a b),?_,
   fun _ _ a b=> P.seating_Limited j x (C.provides j l _ _ a b)⟩
 intro u v a b; unfold seats
 rw [←seating_star,←C.mirrors _ _ b a]
 exact congrArg (π₁) (C.vacuum _ _ h b a)

#print axioms ConcertPlays.seated
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

