import YM.SU5.FiniteGaugeData.Tower.Multigrid
/-! # Sample expansion
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter Finset MeasureTheory
open Vacancy
open scoped Topology Classical BigOperators NNReal ENNReal InnerProductSpace

variable {K A B:Type*}[Fintype K][Fintype B][CommRing A][Algebra ℂ A]
noncomputable def algMean (f:K→A): A:= ((Fintype.card K:ℂ)⁻¹) • ∑ i:K,f i

lemma algConstant [Nonempty K](v:A) : algMean (fun _:K=>v)=v:=by
 unfold algMean; rw [Finset.sum_const,Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀,one_smul]; norm_cast; exact NeZero.ne _
lemma algPoint (i:K)(f:(K→B)→A) : algMean f= algMean (fun q:B=> algMean (fun p : Average.Other K i→B=> f ((Equiv.funSplitAt i B).symm (q,p)))):=by
  let D:= Average.Other K i; let W:=D→B; let E:= Equiv.funSplitAt i B
  have he:(∑ j:K→B,f j)= ∑ x:B, ∑ y:W,f (E.symm (x,y)):= (E.symm.sum_comp f).symm.trans (Fintype.sum_prod_type _)
  unfold algMean; rw [he,Fintype.card_congr E,Fintype.card_prod]; rw [← Finset.smul_sum,smul_smul,Nat.cast_mul,mul_inv_rev,mul_comm]

lemma alloc_eq (t:List K) (F G:K→ A)(p:∀i∈ t,F i=G i) : (t.map F).prod=(t.map G).prod:= congrArg (List.prod ·) (List.map_congr_left (fun i u=> p i u))

variable [Nonempty B] (F : K→B→ A) (l:List K)
theorem algProduct (p:l.Nodup):
    algMean (fun v:K→B=> (l.map (fun i=> F i (v i))).prod)= (l.map (fun i=> algMean (F i))).prod := by
 induction l with
 | nil=> exact algConstant _
 | cons i t ih=>
    let x:=Classical.choice (show Nonempty B by infer_instance)
    let A₀:=(Average.Other K i→ B); let W(v:B)(q:A₀):K→B:= (Equiv.funSplitAt i B).symm (v,q)
    let d(q:A₀):= (t.map fun i=> F i (W x q i)).prod
    obtain ⟨hv,ht⟩:=List.nodup_cons.mp p
    let G(v:K→B):=(t.map (fun i=> F i (v i))).prod
    have he(v:B)(y:A₀) : G (W v y)=d y:= by
       apply alloc_eq
       intro j u; apply congrArg (F _); unfold W; rw [Average.stands,Average.stands]
       · exact fun g=> hv (g ▸ u)
    specialize ih ht
    rw [algPoint i (K:=K) (B:=B)]; change algMean (fun v:B=>algMean (fun p:A₀=> F i (W v p i)*G (W v p)))= algMean (F i) * ((t.map _).prod)
    rw [← ih]; change _= _ * algMean G; rw [algPoint i G]; change _= _*algMean (fun v:B=> algMean (fun p:A₀=> G (W v p)))
    simp_rw [he]; rw [algConstant]
    have hm(v:B)(p:A₀) : W v p i=v:= Average.stops ..
    simp_rw [hm]
    have hx(v:B): algMean (fun p:A₀=> F i v*d p)= F i v * algMean d:=by unfold algMean; rw [← Finset.mul_sum, Algebra.mul_smul_comm]
    simp_rw [hx]; set y:=algMean d; unfold algMean; rw [← Finset.sum_mul, Algebra.smul_mul_assoc]
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.algProduct
