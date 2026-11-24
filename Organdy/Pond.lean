
import Organdy.Domaine
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Larva
open Filter Topology Metric Lattice Exterior Precision 
open Tulip Branch Cube Lat Tenant Drapes _root_.Zephyr.Chern

open scoped Matrix.Norms.L2Operator Matrix
attribute [local instance] opCStarAlgebra
local notation "G" => SU.group
variable {N m:Side}{d r:ℝ}


open Wilson Scroll
open scoped ComplexConjugate
structure Sidelight {N:Side}(k:ℕ)(r τ η D δ:ℝ)
 (W:Wilson.Config SU.group (More N)→ℂ)(A:Ink (Chip (More N))):Prop where
 plate: Domaine k r τ η D W A
 notes: _root_.Zephyr.Chern.Bud (W ∘ petals (stream N))
 lyrics: bud (W ∘ petals (stream N)) 2 = A.gilt (decree ∘ dot)
 tint: δ≤ dint A

private lemma ortho {f:ℝ→ℂ}(u:_root_.Zephyr.Chern.Bud f):
 Bloom (conj ∘ f) (fun i=>conj (bud f i)):=by
 let L:=Complex.conjCLE
 refine Bloom.of_der (a:=conj ∘ deriv f)
   (u.1.mono (fun i h => L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt i h.hasDerivAt))
   (b:= conj (deriv (deriv f) 0)) (L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 u.2.hasDerivAt)
   rfl rfl ?_
 change conj (_ /2) = _
 rw [map_div₀,map_ofNat]

variable {k:ℕ}{r τ η D δ:ℝ}
 {W:Config SU.group (More N)→ℂ}{A:Ink (Chip (More N))}
lemma Sidelight.charge (p:Sidelight k r τ η D δ W A):
 Sidelight k r τ η D δ (conj ∘ W) (Domaine.white A):=by
 have h:=ortho p.notes
 have x:(Domaine.white A).gilt (decree ∘ dot) = conj (A.gilt (decree ∘ dot)):=Domaine.white_gilt _
 refine ⟨p.plate.charge,h.1,?_,?_⟩
 · rw [Function.comp_assoc,h.bud_eq,x];exact congrArg _ p.lyrics
 rw [dint,x]
 exact p.tint

lemma Sidelight.summed {I:Type} [Fintype I][DecidableEq I]
 {W:I→Config SU.group (More N)→ℂ}{A:I→Ink (Chip (More N))}
 {e c g:I→ℝ}
 (p:∀i,Sidelight k r τ (e i) (c i) (g i) (W i) (A i)):
 Sidelight k r τ (∑i,e i) (∑i,c i) (∑i,g i) (∑i,W i) (∑i,A i):=by
 let y:=fun i=> W i ∘ petals (stream N)
 let x:=∑ i,bud (y i)
 have v: Bloom ((∑i,W i) ∘ petals (stream N)) x:=by
    rw [show ((∑i,W i) ∘ petals (stream N))=fun t=>∑ i,y i t by funext t; rw [Function.comp_apply,Finset.sum_apply];rfl]
    exact Bloom.sum _ (fun i _=>(p i).notes.bloom)

 refine ⟨Domaine.streak (fun i=>(p i).plate),v.1,?_,?_⟩
 · rw [v.bud_eq,Ink.gilt_sum]
   unfold x;rw [Finset.sum_apply]
   exact Finset.sum_congr rfl fun i _=>(p i).lyrics
 rw [dint,Ink.gilt_sum,Complex.re_sum]
 exact Finset.sum_le_sum fun i _=>(p i).tint

abbrev honeycomb {I:Type}[Fintype I] (W:I→Config SU.group (More N)→ℂ)
 := fun U=>(Fintype.card I:ℂ)⁻¹ * ((∑i,W i) U)
lemma Sidelight.total {I:Type}[Fintype I][DecidableEq I][Nonempty I]
 {W:I→Config SU.group (More N)→ℂ}{A:I→Ink (Chip (More N))}
 (p:∀i,Sidelight k r τ η D δ (W i) (A i)):
 Sidelight k r τ η D δ (honeycomb W) ((Fintype.card I:ℂ)⁻¹ • (∑i,A i)) :=by
 let a:= (Fintype.card I:ℝ)
 let b:= (Fintype.card I:ℂ)⁻¹
 have v:0<a:= by unfold a; positivity
 have g:b=(a⁻¹:ℝ):=by unfold a b; simp
 let P:=Sidelight.summed p
 have f:=P.plate.weighted b
 let H:=P.notes.bloom.scale b

 have pay(w:ℝ):‖b‖ * (∑_i:I,w)=w:=by
    rw [g,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr v),
        Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
    exact inv_mul_cancel_left₀ v.ne' _
 rw [pay,pay] at f
 let u:=∑i,A i
 obtain ⟨-,-,-,c⟩:=Ink.dye_ink b u P.plate.inside P.plate.sym
 refine ⟨f,H.1,?_,?_⟩
 · change bud (fun t=>b*((∑i,W i) ∘ petals (stream N)) t) 2= Ink.gilt (b•u) (decree ∘ dot)
   rw [H.bud_eq, Pi.smul_apply, P.lyrics,c,smul_eq_mul]
 rw [dint,show ((Fintype.card I :ℂ)⁻¹ • ∑ i,A i) = b•u from rfl,c,g,Complex.re_ofReal_mul]
 nth_rw 1 [←pay δ,g,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr v)] -- nth occurrence depends
 exact mul_le_mul_of_nonneg_left P.tint (inv_nonneg.mpr v.le)

end YM.CF.Organdy.Larva
