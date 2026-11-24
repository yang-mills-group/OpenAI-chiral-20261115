import YM.CF.Rel.Still
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
variable {v:Axis→ℝ}{k:Site n}{F X:FileM n G}{x:Site n}{j M N:ℕ}{f g:SpaceX G n}{B:ℝ}
@[simp] lemma stroll_z (f:SpaceX G n)(k:Site n): stroll k 0 f=f:=by ext1 x; change pulseP k 0 * _= _; rw [pulse_z,one_mul]; congr 1; ext1 p; simp [Lattice.translate]
lemma Sea(k:Site n)(F:SpaceX G n): shapeV k (Sean k F):= fun i U=>by change _= pulseP k i*stroll k 0 F _; rw [stroll_z]
lemma tide(k i:Site n)(h:CakeF f 0 l m σ A):CakeF (Sean k f i) i l m σ A:=by
 have hv:= (h.rotate i).pay (pulseP k i); rw [pulse_a,one_mul,zero_add] at hv; exact hv
lemma sumF(p:FileM n G)(j:ℕ)(A:Fin j→InputZ G n)(he:∀ i:Site n,ContDiffAt ℝ j (satX (p i)) 0):
   (∑ i,cake j (satX (p i)) A)= cake j (satX (∑ i,p i)) A:=by
 unfold cake; simp only [_root_.smul_apply,← Finset.smul_sum]; congr 1; rw [show satX (∑ i,p i)=∑ i,satX (p i) from funext (fun x => by simp [satX])]; rw [iteratedFDeriv_sum_apply]; rw [_root_.sum_apply]; exact fun i _=>he i -- tune
lemma stint {α:Type}(X:Finset α)(f:α→ SpaceX G n)(k x:Site n):stroll k x (∑ i∈X,f i)=∑ i∈X,stroll k x (f i):=by ext1; simp only [stroll,Sean,mul_sum,Finset.sum_apply]
lemma none_s {k:Site n}(h:Travel k m j M N σ A f): ∑ i, Sean k f i=0:=by
 obtain ⟨p,x,h₁,h₂,h₃,h₄,h⟩:=h.profit; rw [h]; change (∑ i, stroll k i _)=0
 have hh{f g:SpaceX G n}(i:Site n): stroll k i (f-g)=stroll k i f-stroll k i g:=funext fun a=> mul_sub ..
 simp_rw [stint,hh,sum_ride k _ (0:Salt n G),sum_sub_distrib]; -- tune order
 rw [sum_comm]; apply sub_eq_zero.mpr; conv_rhs=> rw [sum_comm]
 refine sum_congr rfl fun j _=> ?_; exact Equiv.sum_comp (Equiv.addRight j) (fun i=>stroll k i (p j))
lemma Slice (v:Body 1 n)(b:G.ColorIndex): ‖flaw G v b‖≤1:=(pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=>by unfold flaw; rw [Pi.single_apply]; split <;> simp [jewelG]
lemma scopes(j:ℕ)(h:∀ i: Site n, CakeF (F i) i M m σ A)(hs:0<σ)(he:j+1 ≤ m): Prox F (j+1) (plot M*A):=by
 intro v s; let i:= (v 0).1; let b(p:Site n):= cake (j+1) (satX (F p)) (fun j=> flaw G (v j) (s j)); have ht : ‖(0:InputZ G n)‖<σ:= by simpa using hs
 have hx(p): ‖b p‖ ≤ A:= ((cake (j+1) (satX (F p))).le_opNorm (fun i=> flaw G (v i) (s i))).trans ((mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun i _=>norm_nonneg _) (fun i _=> Slice (v i) (s i)))).trans (pollen hs (h p) he)) -- tune
 let r:= pavilion M i; have hp(p)(hi:p∉r):b p=0:= scatter v s (h p).toAtom (((h p).ledger 0 ht).smooth.of_le (by exact_mod_cast he)) 0 (by change _ < separation p i; rw [separation_comm]; exact not_le.mp ((theatre ..).not.mp hi))
 have hA:0 ≤ A:=(norm_nonneg _).trans (hx i)
 change ‖∑ p,b p‖ ≤ _; rw [← sum_subset (subset_univ r) (fun i (_:i∈univ) he=>hp i he)]; apply (norm_sum_le ..).trans
 apply (sum_le_sum (g:=fun _=> A) fun i _=> hx i).trans; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (pay_v _)) hA
lemma sunny (hf:Prox F j A){V:FileM n G}{C:ℝ}(hv:Prox V j C)(hs:∀ i, ContDiffAt ℝ j (satX (F i)) 0)(h:∀ i,ContDiffAt ℝ j (satX (V i)) 0)(hX:∀ i,ContDiffAt ℝ j (satX (X i)) 0)(he:(∑ i,X i)=(∑ i,F i)-∑ i,V i): Prox X j (A+C):=by
 intro i s; let f i':=satX (F i'); let g i':= satX (V i'); let Y(u:FileM n G):= satX (∑ i,u i); let p:=fun i' : Fin j=> flaw G (i i') (s i'); have hx:ContDiffAt ℝ j (Y F) 0:=by simp_rw [Y,satX,Function.comp_def,Finset.sum_apply]; exact ContDiffAt.sum fun i _=>hs i
 have hp:ContDiffAt ℝ j (Y V) 0:=by simp_rw [Y,satX,Function.comp_def,Finset.sum_apply]; exact ContDiffAt.sum fun i _=> h i
 rw [sumF X _ _ hX,he]; change ‖cake j (Y F-Y V) p‖ ≤ _; unfold cake; rw [iteratedFDeriv_sub_apply hx hp,smul_sub,_root_.sub_apply]
 apply (norm_sub_le ..).trans; change ‖cake j _ _‖+‖cake j _ _‖ ≤ _; rw [←sumF F j p hs,←sumF V j p h]; exact add_le_add (hf ..) (hv ..) -- tune
end YM.CF.Rel
