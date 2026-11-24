import YM.CF.Rel.Early
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
open Cube
variable {v:Axis→ℝ}{k:Site (More n)}{F:FileM (More n) G} {j s:ℕ}
lemma cake_ch {f:SpaceX G n}(c:ℂ)(h: ContDiffAt ℝ m (satX f) 0)(x:Fin m→InputZ G n):cake m (satX (c • f)) x = c* cake m (satX f) x:=by
 let L:= (ContinuousLinearMap.lsmul ℝ ℂ c : ℂ→L[ℝ]ℂ); change _=L (cake _ _ x); simp_rw [show satX (c • f) = L ∘ satX f from rfl,cake, L.iteratedFDeriv_comp_left h le_rfl, _root_.smul_apply,map_smul]; rfl
lemma cakeSum{α:Type}[Fintype α](F:α→ SpaceX G n)(h:∀ i,ContDiffAt ℝ m (satX (F i)) 0)(x:Fin m→InputZ G n): cake m (satX (∑ i,F i)) x=∑ i,cake m (satX (F i)) x:=by
 unfold cake; rw [show satX (∑ i,F i)=∑ i,satX (F i) from funext (fun x=> by simp [satX]),iteratedFDeriv_sum_apply (u:=univ) (fun i _=>h i)]; simp only [Finset.smul_sum,_root_.sum_apply]
lemma massM : ‖massX‖=(Fintype.card Charm:ℝ):=by simp [massX]
lemma massΩ : 0<‖massX‖:= norm_pos_iff.mpr mass_p
variable (p:LayerP n F)
include p
lemma mer d (h:∀ i, CakeF (F i) i l m σ A) (i:Site (More n)): CakeF (laidC d n F i) i l m σ A:=by
 have he(t:Site (More n)): CakeF (pose F i t) i l m σ A:=by have hv:= (h (i+t)).rotate (-t); rw [add_neg_cancel_right] at hv; exact hv
 rw [restoreX p];
 have ht : ∀ j:Charm, CakeF (cell d j • pose F i (logo n j)) i l m σ A:=by intro j; have hv:= (he (logo n j)).pay (cell d j); rwa [legX,one_mul] at hv
 apply ((CakeF.sigmaH univ (fun i _=> ht i)).pay massX⁻¹).under le_rfl le_rfl
 rw [sum_const,card_univ,nsmul_eq_mul,norm_inv,←massM,inv_mul_cancel_left₀ massΩ.ne']
lemma slideY (c:Charm)(x:Site (More n))(h:∀ i, cFoot j (satX (F i)))(p':∀ i,CakeF (F i) i l m σ A)(hp:0<σ)(hj:j ≤ m): cFoot j (satX (laidC c n F x)):=by
 have he:‖(0:InputZ G (More n))‖<σ:=by simpa using hp
 have hh(d:Charm): prism j (pose F x (logo n d)) (courseC 0 (-(logo n d)) (trim j (satX (F (x+logo n d))))) :=by -- course k=0 cell 1
    let f:=F (x+logo n d); have hh:=prizeC (0:Site (More n)) (-logo n d) (show prism j f (trim j (satX f)) from (argent (((p' _).ledger 0 he).smooth.of_le (by exact_mod_cast hj))).mp (h _));
    rw [show stroll (0:Site (More n)) (-logo n d) f =pose F x (logo n d) from ?_] at hh; exact hh
    ext1 i; change pulseP _ _* _=_; rw [pulseP, cell_duality 0 _,cell_origin,inv_one,one_mul]; rfl
 apply (asideF (((mer p c p' x).ledger 0 he).smooth.of_le (by exact_mod_cast hj)) (massX⁻¹ • ∑ i,cell c i • courseC 0 (-(logo n i)) (trim j (satX (F (x+logo n i))))) ?_).1
 rw [restoreX p]; exact prism.mul _ (prism.sumZ _ _ _ (fun i _=>prism.mul (cell c i) (hh i)))
lemma cash_s {X:ℝ}(h:∀ i,CakeF (F i) i l m σ X)(hc:Prox F j A)(hp:0<σ)(he:j ≤ m)(p':Charm):Prox (laidC p' n F) j A:=by
 intro i s; have H:‖(0:InputZ G (More n))‖<σ:=by simpa using hp
 let D(a):=flaw G (i a) (s a); let G'(k:Site (More n))(d:Charm):= pose F k (logo n d)
 have hi(k:Site (More n))(d:Charm):ContDiffAt ℝ j (satX (cell p' d • G' k d)) 0:= ((((h (k+logo n d)).rotate (-(logo n d))).pay (cell p' d)).ledger 0 H).smooth.of_le (by exact_mod_cast he)
 have hh(k:Site (More n)): ContDiffAt ℝ j (satX (∑ i:Charm, cell p' i • G' k i)) 0:=by rw [show satX _= _ from ?_]; exact ContDiffAt.sum (s:=univ) (fun d _=>hi k d); ext1; simp [satX]
 let L(k:Site (More n))(d:Charm):=loanX (F (k+logo n d)) (-logo n d)
 have ht(k:Site (More n)): cake j (satX (laidC p' n F k)) D = massX⁻¹ * ∑ i:Charm, cell p' i*cake j (satX (F (k+logo n i))) (fun t=> te (D t) (-logo n i)):=by
    rw [restoreX p,cake_ch massX⁻¹ (hh k),show cake j _ D=_ from cakeSum _ (hi k) D]; congr 1; apply sum_congr rfl; intro i _; rw [cake_ch (f:=G' k i) (cell p' i) (show ContDiffAt _ _ _ _ from ((((h (k+logo n i)).rotate (-logo n i)).ledger 0 H).smooth.of_le (by exact_mod_cast he)))]; exact congr_arg (cell p' i *·) (shape_m (_:Site (More n)) D _ (((h (k+logo n i)).ledger 0 H).smooth.of_le (by exact_mod_cast he)))
 have hu(d:Charm)(b:Fin j): te (D b) (-logo n d)=flaw G ((i b).1+logo n d,(i b).2) (s b):=by
    ext1 p; unfold D te flaw; simp_rw [Pi.single_apply]; simp only [Prod.ext_iff]; simp only [show p.1 + -logo n d=(i b).1 ↔ p.1=(i b).1 +logo n d from by rw [←sub_eq_add_neg,sub_eq_iff_eq_add]]
 change ‖∑ k, cake _ _ D‖≤ _; simp_rw [ht, hu, mul_sum]; rw [sum_comm]; simp_rw [← mul_sum]; rw [norm_mul]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (norm_nonneg _)).trans; simp_rw [norm_mul,legX,one_mul]; apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=>A) (fun a _=>?_)) (norm_nonneg _)) ?_; swap
 · let p:=fun k:Site (More n)=> cake j (satX (F k)) (fun b:Fin j=>flaw G ((i b).1+logo n a,(i b).2) (s b)); change ‖∑ k,p (Equiv.addRight (logo n a) k)‖ ≤ _; rw [Equiv.sum_comp]; exact hc (fun b=> ((i b).1+logo n a,(i b).2)) s
 rw [sum_const,card_univ,nsmul_eq_mul, norm_inv,←massM, inv_mul_cancel_left₀ massΩ.ne']
end YM.CF.Rel
