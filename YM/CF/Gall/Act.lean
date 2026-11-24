import YM.CF.Gall.Penn
set_option autoImplicit false
noncomputable section
namespace YM.CF.Gall
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]{A:Op n}{p q f:Wave n}{k v C d b w:ℝ}
lemma bill_p {L:Op n}(h:∀ i:n,‖acts L (basisKet i)‖≤C ∧ ‖acts (star L) (basisKet i)‖≤ C)(b:WordX n):‖iceT L (artW b)‖ ≤ C+1:=by
 rw [Emu.wing_h]; apply (norm_add_le ..).trans; apply add_le_add
 · apply le_trans (cost_pe ..); unfold artW; rcases b with ⟨i,k⟩; cases i
   · simp only [Bool.false_eq_true,ite_false]; rw [act_neg,norm_neg]; exact (h _).1
   exact (h _).2
 apply (cost_pe ..).trans; simp [artW,basisKet]
lemma boom_v {P Q T D K:Op n}[Nonempty n](h:Clad P Q T D K)(g:∀ i:n, ‖acts (laneP Q T K) (basisKet i)‖≤ C ∧ ‖acts (star (laneP Q T K)) (basisKet i)‖≤ C)(L: List (WordX n))(x:Sea P p)(y:Sea Q q): ‖inner ℂ q (acts (rollC pack L *quant T) p)‖≤ ‖skyGlow q T p‖*(C+1)^L.length:=by
 have he:rollC Gall.pack L=rollC ton (L.map artW):=by simp only [rollC,List.map_map]; rfl
 let F:= iceT (laneP Q T K)
 have ht: ‖rollC F (L.map artW)‖≤ (C+1)^L.length:=by
    clear he; induction L with
    | nil=> simp [rollC]
    | cons i L ih=>
       rw [List.map_cons,rollC,List.map_cons,List.prod_cons,List.length_cons,pow_succ',←rollC]; exact (norm_mul_le ..).trans (mul_le_mul (bill_p g i) ih (norm_nonneg _) ((norm_nonneg _).trans (bill_p g i)))
 rw [he,Flare.read0 h _ _ x y,norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); let V:=rollC F (L.map artW); have hp:= norm_inner_le_norm (𝕜:=ℂ) q (acts V q); have hq: ‖acts V q‖ ≤ ‖V‖*‖q‖:=((acts V).le_opNorm _)|>.trans_eq (by rw [show ‖acts V‖=‖V‖ from Matrix.l2_opNorm_toEuclideanCLM _])
 rw [y.2,one_mul] at hp; rw [y.2,mul_one] at hq; exact hp.trans (hq.trans ht)
variable {j:ℕ}{r:ℝ}
lemma cash(H:1≤j)(p:0<r):∃ G C:ℝ,0<G∧0<C∧∀ N:Side,Even N.val→ r *pinch N^2≤1/8→∀ b:Candle,∀ S:Slide N b,∀ M:Jill.Male,∀ x:Wave (Single N),Sea (Dofu N (field S j M)) x→Gall.Yep C (mateK N) x (G*iceK j S M r):=by
 obtain ⟨l,h⟩:=risky_card j H r p; let w:= l*4+1; let C:ℝ:=(w+1:ℝ)*heave r; have hx:= heave_p r; have hc:heave r ≤ C:= le_mul_of_one_le_left hx.le (by simp)
 obtain ⟨c,hb,V⟩:=rod j C hc p; obtain ⟨B,u,U⟩:=octant j H p hc; obtain ⟨v,hv,Z⟩:=bead_bound w
 let V':= c^2*Real.pi; have hp:0<V':=by unfold V'; positivity
 obtain ⟨V'',hV,X'⟩:= Gall.fame H p hp
 refine ⟨v*B,(V''+1),mul_pos hv (zero_lt_one.trans_le u),by positivity,fun N w' l' b s M i k y=>?_⟩; let T:=risky s j M r; let Y:=costs (V''+1) y; have hy:0≤Y:=pow_nonneg (by positivity) _
 let a:=iceK j s M r; have ha:0<a:=ice_p _ _ _ p
 rw [wage _ i (heave r*pinch N) T w (by unfold T w; have h:= h N w' b s M; omega)]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun j' => |bead w (-1) j'| * (B*a*Y)) ?_).trans ?_)
 · intro i' hi; let t:=(i'+1:ℝ)*heave r; have ht:t∈ Set.Icc (heave r) C:=by refine ⟨le_mul_of_one_le_left hx.le (by simp),mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ (mem_range.mp hi).le) hx.le⟩
   let F:=portT s M j r t; let W:= mateV T (t*pinch N); rw [norm_mul,Complex.norm_real, Real.norm_eq_abs,show openW T (_ *(heave r*pinch N))=F from (by unfold F portT; rw [←mul_assoc])]
   obtain ⟨K,v,e,X,R⟩:=V N w' l' b s M t ht; have hv:= torn s w' j M K F W v; exact mul_le_mul_of_nonneg_left ((boom_v hv (fun x=> by
      rw [←Emu.tall_s]; exact X' (Emu.tilt F K) s w' (Emu.attire v w' p hb e R) x) y k (tickB _)).trans (mul_le_mul_of_nonneg_right (U _ w' l' b s M t ht.1 ht.2 i k) hy)) (abs_nonneg _)
 rw [←sum_mul]; exact (mul_le_mul_of_nonneg_right (Z _ (by norm_num)) (mul_nonneg (mul_nonneg (zero_le_one.trans u) ha.le) hy)).trans_eq (by unfold a Y; ring)
end YM.CF.Gall
