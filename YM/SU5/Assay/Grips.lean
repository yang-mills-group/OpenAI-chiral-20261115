import YM.SU5.Assay.Brim
import YM.SU5.Assay.SandCup
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
variable (t:ℕ)
local notation "Φ"=>P.colorSpace j x
local notation "μ"=>P.seenBox j x t
local notation "σ"=>P.shifts j
local notation "τ"=>P.tock t
local notation "T"=>enclave P.calibration
local notation "ℇ"=>(P.physicalEnergy j x).wax
def Sill (a b:ℝ)(f:P.Test)(A:X)(m:ℤ)(w:ℕ):Prop:=a ≤ τ m ∧ τ (m+w) ≤ b ∧ P.Brim j m w f ∧ A=(U).sand (P.costing j x t m w f) (τ m-a) (b-τ (m+w))
def Grips (a b:ℝ)(f:P.Test)(A:X):Prop:= (f=0 ∧ A=0) ∨ ∃ m:ℤ, ∃ w:ℕ, P.Sill j x t a b f A m w
local notation "β"=>P.costing j x t
local notation "𝕤"=>P.Sill j x t
local notation "𝔤"=>P.Grips j x t
variable {P j x t}{a b c d:ℝ}{f g:P.Test}{A L:(P.ColorHil j x).Op}{m n:ℤ}{w v:ℕ}
lemma Sill.grips (h:𝕤 a b f A m w):𝔤 a b f A:= Or.inr ⟨_,_,h⟩
lemma Sill.widen (h:𝕤 a b f A m w)(l:n ≤ m)(r:m+w ≤ n+v)(p:a ≤ τ n)(q:τ (n+v) ≤ b):𝕤 a b f A n v:=by
 obtain ⟨_,_,vh,h⟩:=h
 obtain ⟨u,z⟩:=vh.stretch x t l r
 refine ⟨p,q,u,?_⟩
 rw [h,z,sand_join (U) (sub_nonneg.mpr ((P.tock_le t _ _).mpr l)) (sub_nonneg.mpr ((P.tock_le t _ _).mpr r)) (sub_nonneg.mpr p) (sub_nonneg.mpr q)]
 simp only [show τ m-τ n+(τ n-a)=τ m-a by abel,show τ (n+v)-τ (m+w)+(b-τ (n+v))=b-τ (m+w) by abel]
lemma Sill.common (h:𝕤 a b f A m w)(k:𝕤 a b g L n v):
 ∃ z:ℤ, ∃ r:ℕ, 𝕤 a b f A z r ∧ 𝕤 a b g L z r:=by
 let z:=min m n;let y:=max (m+w) (n+v)
 have p:a ≤ τ z:=(min_choice m n).elim (fun e=>le_of_le_of_eq h.1 (congrArg (τ) e.symm)) (fun e=>le_of_le_of_eq k.1 (congrArg (τ) e.symm))
 have q:τ y ≤ b:=(max_choice (m+w) (n+v)).elim (fun e=>(congrArg (τ) e).trans_le h.2.1) (fun e=>(congrArg (τ) e).trans_le k.2.1)
 have zl:z ≤ m:= min_le_left ..;have zr:z ≤ n:=min_le_right ..
 have yl:m+w ≤ y:=le_max_left ..;have yr:n+v ≤ y:=le_max_right ..
 let r:ℕ:= (y-z).toNat;have hr:z+r=y:=by omega
 have q': τ (z+r) ≤ b:=hr.symm ▸ q
 exact ⟨z,r,h.widen zl (hr.symm ▸ yl) p q',k.widen zr (hr.symm ▸ yr) p q'⟩
lemma Sill.zero (h:𝕤 a b 0 A m w): A=0:=by
 obtain ⟨_,_,p,rfl⟩:=h
 rw [Brim.price_zero x t m p.1.pos];simp only [sand,mul_zero,zero_mul]
/-! All Sills agree, also if stamp tested at 0. -/
lemma Grips.unique (h:𝔤 a b f A)(p:𝔤 a b f L): A=L:=by
 rcases h with ⟨rfl,rfl⟩|⟨m,w,h⟩ <;> rcases p with v|⟨n,i,p⟩
 · exact v.2.symm
 · exact p.zero.symm
 · obtain ⟨rfl,rfl⟩:=v;exact h.zero
 obtain ⟨_,_,t,q⟩:=h.common p;exact t.2.2.2.trans q.2.2.2.symm
lemma Grips.zero (P:Spine)(j:Axis)(x:P.Spectrum0 j)(t:ℕ)(a b:ℝ):P.Grips j x t a b 0 0:= Or.inl ⟨rfl,rfl⟩
lemma Grips.color (h:𝔤 a b f A):f∈T:=by
 rcases h with ⟨rfl,_⟩|⟨_,_,h⟩
 · exact zero_mem _
 exact h.2.2.1.2
lemma Grips.smul (h:𝔤 a b f A)(z:ℂ):𝔤 a b (z•f) (z•A):=by
 rcases h with ⟨rfl,rfl⟩|⟨m,w,u,v,p,rfl⟩
 · rw [smul_zero,smul_zero];exact Grips.zero ..
 exact Sill.grips (m:=m) (w:=w) ⟨u,v,p.smul z,by rw [Brim.price_smul x t p,sand_smul]⟩
lemma Grips.add (h:𝔤 a b f A)(p:𝔤 a b g L):𝔤 a b (f+g) (A+L):=by
 rcases h with ⟨rfl,rfl⟩|⟨m,w,h⟩; · simpa only [zero_add] using p
 rcases p with ⟨rfl,rfl⟩|⟨n,i,p⟩; · simpa only [add_zero] using h.grips
 obtain ⟨d,k,⟨u,v,l,rfl⟩,_,_,r,rfl⟩:=h.common p
 exact Sill.grips (m:=d) (w:=k) ⟨u,v,l.add r,by rw [Brim.price_add x t l r,sand_add]⟩
lemma Grips.sum {I:Type*}(s:Finset I)(f:I→P.Test)(A:I→X)(h:∀i∈s,𝔤 a b (f i) (A i)):𝔤 a b (∑i∈s,f i) (∑i∈s,A i):=by
 induction s using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty];exact Grips.zero ..
 | insert i s v ih=>
   rw [sum_insert v,sum_insert v];exact (h i (mem_insert_self ..)).add (ih (fun k t=>h k (mem_insert_of_mem t)))
lemma Grips.outer (h:𝔤 a b f A)(p:c ≤ a)(q:b ≤ d):𝔤 c d f ((U).sand A (a-c) (d-b)):=by
 rcases h with ⟨rfl,rfl⟩|⟨m,w,u,v,z,rfl⟩
 · simp only [sand,mul_zero,zero_mul];exact Grips.zero ..
 refine Sill.grips (m:=m) (w:=w) ⟨p.trans u,v.trans q,z,?_⟩
 rw [sand_join (U) (sub_nonneg.mpr u) (sub_nonneg.mpr v) (sub_nonneg.mpr p) (sub_nonneg.mpr q),show τ m-a+(a-c)=τ m-c by abel,show b-τ (m+w)+(d-b)=d-τ (m+w) by abel]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
