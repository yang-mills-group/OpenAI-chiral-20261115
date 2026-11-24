import GaugeFieldConstruction.Halloma4
import GaugeFieldConstruction.Sparver
import GaugeFieldConstruction.PhysA
import YM.CF.Sault.Cider
import YM.CF.Sour.Millet
import YM.CF.Leaf.Jive
import YM.CF.Hest.Boat
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
set_option linter.flexible false
section op
-- local calculus. use turbot.C
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{Y α g A:Type}{ι:Type}[LinearOrder ι][Fintype ι]
variable {n:ℕ}(μ: g→E→Y){a b c h:ℝ}{F G:Y→FC ι}{s:E}
structure Portμ (μ:g→E→Y)(x:E)(P:Y→FC ι)(h c:ℝ)(d:ℕ):Prop where
    bill : ∃ Z: Finset ι→Finset ι→ℝ,(∀ i j,0≤ Z i j) ∧(∀ j:Finset ι,(∑ i:Finset ι,h^i.card*Z i j)≤ c*h^j.card)∧ ∀ (V:g)(i j:Finset ι),Pence d (fun y=>P (μ V y) i j) x (Z i j)
variable {μ}
lemma Portμ.rise (p:Portμ μ s F h c n)(d:c≤a)(t:0≤h) : Portμ μ s F h a n:=by obtain ⟨Z,H,p,E⟩:=p.bill; exact ⟨Z,H,(fun i=> (p i).trans (mul_le_mul_of_nonneg_right d (pow_nonneg t _))),E⟩
lemma Portμ.add (p:Portμ μ s F h c n)(q: Portμ μ s G h b n) : Portμ μ s (F+G) h (c+b) n:=by
 obtain ⟨Z,v,hp,V⟩:=p.bill; obtain ⟨T,H,hs,U⟩:=q.bill
 refine ⟨⟨Z+T,(fun i j=>add_nonneg (v i j) (H i j)),?_,fun i a b=>(V i a b).add (U i a b)⟩⟩; intro j; simp only [Pi.add_apply,mul_add,sum_add_distrib,add_mul]; exact add_le_add (hp j) (hs j)
lemma Portμ.mult (p:Portμ μ s F h c n)(q: Portμ μ s G h b n)(v:0≤c) : Portμ μ s (F*G) h (c*b) n:=by
 obtain ⟨Z,g,H,V⟩:=p.bill; obtain ⟨W,u,U,Q⟩:= q.bill
 let M(x y:Finset ι):=∑ j:Finset ι,Z x j*W j y
 refine ⟨⟨M,fun x y=>sum_nonneg (fun _ _=>mul_nonneg (g _ _) (u _ _)),?_,?_⟩⟩
 · intro j; unfold M; simp_rw [mul_sum]; rw [mul_assoc,Finset.sum_comm]; apply le_trans _ (mul_le_mul_of_nonneg_left (U j) v); rw [mul_sum]; apply sum_le_sum; intro i _; simp_rw [←mul_assoc,←sum_mul]; exact mul_le_mul_of_nonneg_right (H _) (u _ _)
 intro i x y; unfold M; let D(z:Finset ι)(j:E):= F (μ i j) x z * G (μ i j) z y
 have ht(z):Pence n (D z) s (Z x z* W z y):= (V i x z).twice (Q i z y)
 exact (Pence.money (fun i (_:i∈univ)=>ht i)).germ (Eventually.of_forall (fun q=> (Finset.sum_apply ..).trans (Matrix.mul_apply ..).symm))
lemma Portμ.scale (p:Portμ μ s F h c n)(f:Y→ℂ)(u:0≤b)(q:∀ i,Pence n (f ∘ μ i) s b) : Portμ μ s (fun x=> f x • F x) h (b*c) n:=by
 obtain ⟨V,w,C,d⟩:=p.bill; refine ⟨⟨b • V,(fun _ _=>mul_nonneg u (w ..)),?_,fun _ _ _=> (q _).twice (d ..)⟩⟩
 intro i; simp only [Pi.smul_apply,smul_eq_mul,mul_left_comm (h^_) b,←mul_sum, mul_assoc]; exact mul_le_mul_of_nonneg_left (C i) u
lemma Portμ.sMul (p:Portμ μ s F h c n)(t:ℂ): Portμ μ s (t • F) h (‖t‖*c) n:= p.scale (fun _=>t) (norm_nonneg _) (fun _=> Pence.const ..)
lemma Portμ.neg (p:Portμ μ s F h c n): Portμ μ s (-F) h c n:=by simpa using p.sMul (-1)
lemma Portμ.zero (h:ℝ)(s:E):Portμ (ι:=ι) μ s 0 h 0 n:=⟨0,fun _ _=>le_refl _, fun j=>by simp,fun _ _ _=> (show Pence n (fun _:E=> (0:ℂ)) s 0 from (norm_zero (E:=ℂ)) ▸ Pence.const (k:=n) s (0:ℂ))⟩
lemma Portμ.sum (S:Finset α)(F:α→Y→FC ι)(c:α→ℝ)(p:∀ i∈S,Portμ μ s (F i) h (c i) n): Portμ μ s (∑ i∈S,F i) h (∑ i∈S,c i) n:=by
 induction S using Finset.induction_on with
 | empty=> rw[sum_empty,sum_empty]; exact Portμ.zero _ _
 | insert i S ih ph=> rw[sum_insert ih,sum_insert ih]; exact (p i (mem_insert_self ..)).add (ph fun i y=>p i (mem_insert_of_mem y))
lemma Portμ.const (i:FC ι)(p:Sour.Ark i h a): Portμ μ s (fun _=> i) h a n:=⟨fun i' j=> ‖i i' j‖,fun _ _=>norm_nonneg _,p.tubes,fun _ _ _=>Pence.const ..⟩
variable (μ h n s)
lemma mist_t (x:ι)(u:0<h): Portμ μ s (fun _=>takeF x) h h⁻¹ n:=by
 apply Portμ.const; refine ⟨(inv_pos.mpr u).le,?_⟩
 intro j; simp_rw [take_entry]; by_cases p:x∈j; swap; · simp_rw[if_neg p, norm_zero,mul_zero,sum_const_zero]; positivity
 simp_rw [if_pos p,apply_ite _ _]; simp only [parity,norm_pow,norm_neg,norm_one,one_pow,mul_one,norm_zero,mul_zero,sum_ite_eq',mem_univ,ite_true]
 refine le_of_eq ?_; conv_rhs=>arg 2; rw [←insert_erase p,card_insert_of_notMem (notMem_erase x j)]
 rw [pow_succ,mul_comm (_^_),←mul_assoc,inv_mul_cancel₀ u.ne',one_mul]
lemma mist_p (x:ι)(v:1≤h): Portμ μ s (fun _=>put x) h h n:= Portμ.const _ (Ark.blond h v x)
lemma mist_q (i:Finset ι)(v:1≤h):Portμ μ s (fun _=>poke i) h (h^i.card) n:=by
 induction i using Finset.induction_on_min with
 | empty=>simp only [poke,Poly.tag_void,card_empty,pow_zero]; exact Portμ.const _ (Ark.one _)
 | insert i S k ih=> rw[poke,Poly.tag_min (cane ι) _ _ k,card_insert_of_notMem (fun p=>lt_irrefl _ (k _ p)),pow_succ']; exact (mist_p n μ h s i v).mult ih (zero_le_one.trans v)
#print axioms mist_p
end op
end Ivey
end YM.CF.Scree.Ing
end
