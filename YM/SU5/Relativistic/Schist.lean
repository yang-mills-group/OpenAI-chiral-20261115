import YM.SU5.Relativistic.Yokel
import YM.SU5.Relativistic.Millet
import YM.SU5.FiniteGaugeData.Pannier.CaneSugar
/-! # pinpoint charge. On clean ORBIT. (For unrepaired dirty count by t.) -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Metric Fock Finset Lattice Lat Fir Ember Thera BPress.Spin.Blank Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I][Nonempty I]
variable {P B:Op I}(p:IsStarProjection P)
local notation "Xα" => Comb B P
lemma sparks (T:Shaft I)(h:‖T.sell‖≤ 2)(t:‖T.buy‖≤2)(k:ℕ)(i:LeanV I)(C:ℝ)
    (q:‖acts (Xα k) (basisKet i.2)‖≤ C)(s:‖acts (star (Xα k)) (basisKet i.2)‖≤C):
    ‖(T.foldC (Saber (B:=B) p k)).glow (drawT P i)‖ ≤ 2*(1+C):=by
 rw [T.fold_use]; let L:= Saber p (B:=B) k; let V:= basisKet i.2
 have hw(Q:Op I)(g:IsStarProjection Q) : ‖acts Q V‖ ≤ 1:=(Flare.opy Q V).trans ((mul_le_mul (g.norm_le _) (show ‖V‖≤1 from (by simp [V,basisKet])) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
 unfold drawT; split
 · rw [seekF,prong_p, Shaft.glow_up, T.glow_up]; let v:= acts L.sell (acts (1-P) V)
   apply ((Flare.cost_pe false _).trans (Flare.opy _ (v))).trans; apply mul_le_mul h _ (norm_nonneg _) zero_le_two; unfold v L Saber; simp only [act_add,act_one]; rw [←act_mul]; apply (norm_add_le ..).trans; apply add_le_add (hw _ p.one_sub); have he:star (Xα k)*(1-P)=star (Xα k):=by rw [mul_sub, mul_one, show star (Xα k)*P=0 from (?_),sub_zero]; nth_rw 2 [← (show star P=P from p.isSelfAdjoint)]; rw [←star_mul,comb_px p, star_zero]
   rw [he]; exact s
 rw [hideF,prong_t, Shaft.glow_down, T.glow_down]; let v:= acts (star L.buy) (acts P V)
 apply ((Flare.cost_pe true _).trans (Flare.opy _ (v))).trans; apply mul_le_mul ((norm_star _).trans_le t) _ (norm_nonneg _) zero_le_two; unfold v L Saber; simp only [star_sub,star_star,star_one,act_sub,act_one]; rw [←act_mul,comb_xp p]
 exact (norm_sub_le ..).trans (add_le_add (hw _ p) q)
lemma scyth(k:ℕ)(C:ℝ)(u:‖Comb B P k‖ ≤ C)(p0:0≤C)(i:LeanV I)(T:Shaft I)(h:‖T.sell‖≤2)(t:‖T.buy‖≤2): ‖(T.foldC (Saber (B:=B) p k)).glow (drawT P i)‖≤ 2*(1+C):=by
 apply sparks p _ h t k _ C _ _ ; exact (Flare.opy ..).trans (by simpa [basisKet] using u)
 exact (Flare.opy ..).trans (by simpa [basisKet] using u)
variable {M:Tulip.Male}{j K w s n v:ℕ}{γ α R r δ:ℝ} {N:Side}
lemma off_age : ∃ C:ℝ,0<C∧∀ (S:Side)(k:Op (Single S)), IsStarProjection k→‖Comb (tickA S) k n‖≤ C:=by obtain ⟨C,p,h⟩:= Staff.power (Staff.ice n); refine ⟨C,p,fun a b y=>?_⟩; rw [←Staff.ice_at]; exact h a b y

-- any unitary tradew: fiber local. omits halo cost.
lemma seriesG (E:Op (Single N)) (X:Seat N→SU.E) (i:Single N){C':ℝ}(u:∀ (j:Slot),‖acts (twist (tradew N X) E) (basisKet (i.1,j))‖≤ C') : ‖acts E (basisKet i)‖ ≤45*C':=by
 let U:=tradew N X; let Y:=twist U E; let x:=basisKet i; let V:= acts U.val x
 rw [←act_unit_norm U, Fock.swivel]; change ‖acts Y V‖ ≤ _
 have he: V= ∑ j:Slot,V.ofLp (i.1,j) • basisKet (i.1,j):=by
    nth_rw 1 [←basis_expand V]; unfold Single; rw [Fintype.sum_prod_type]; -- restrict outer
    rw [sum_eq_single i.1]; · intro l z d; apply sum_eq_zero; intro j h; unfold V x U; rw [basis_act]; simp only [tradew, jump_apply,Equiv.refl_apply,if_neg d,zero_smul]
    simp
 rw [he,map_sum]; apply (norm_sum_le ..).trans; apply le_trans (b:=∑ j:Slot,C') (sum_le_sum (fun j h=>?_)); · rw [sum_const,card_univ,slots,nsmul_eq_mul]; norm_num
 rw [map_smul,norm_smul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_) (u j); exact (PiLp.norm_apply_le V _).trans_eq (by unfold V x; rw [act_unit_norm]; simp [basisKet]) -- normLp
abbrev postage (j:ℕ)(C:ℝ):Prop:=∀ n:Side,∀ M:Tulip.Male,∀ k:ℕ,let Z:=spar j M (1:Pane n); let X:=Comb (tickA n) Z k; IsStarProjection Z→∀ i:Single n, ‖acts X (basisKet i)‖≤ C∧‖acts (star X) (basisKet i)‖≤C
lemma grantH (j:ℕ)(p:1≤j):∃ C:ℝ,0<C∧postage j C:=by obtain ⟨C,g,v⟩:= columnC j p; exact ⟨_,g,fun _ _ _ p i=>v _ _ p _ _⟩
open Staff
variable (z:0≤δ)(W:∀ ε>(0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,K≤n.val→ Winter j δ n γ w ε)
abbrev charge (C:ℝ):=2*(1+45*(1+C))
variable (H:postage j R)
include z W H
lemma localMail (k:ℕ):∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,K≤ n.val→∀ M:Tulip.Male,IsStarProjection (spar j M (1:Pane n))→∀ S:Support (More n),∀ U U':Pane n,∀ (g:Seat n→ SU.E), Rightful (Lattice.halo w S) U 1 γ → U=Lattice.gauge g U' → Guard U δ →∀ p:IsStarProjection (spar j M U'), IsStarProjection (spar j M U) → twist (tradew n g) (spar j M U')=spar j M U →∀ i:LeanV (Single n), node i.2.1.1∈S → ∀ T:Shaft (Single n),‖T.sell‖ ≤2→‖T.buy‖≤2→ ‖(T.foldC (Saber (B:=tickA n) p k)).glow (drawT (spar j M U') i)‖≤charge R :=by
 let t:= Staff.ice k; obtain ⟨γ,d,w,f⟩:= playsA j δ z W t 1 zero_lt_one; obtain ⟨γ',d',w',f'⟩:= playsA j δ z W t.flip 1 zero_lt_one; refine ⟨min γ γ',lt_min d d',max w w',fun n v M p S U U' g s e h p' y u i z T r h' =>?_⟩
 let Y:=tradew n g; let x:=i.2; let Q:=spar j M U; let P:=spar j M U'; let B:=tickA n; let A:=spar j M (1:Pane n)
 obtain ⟨-,l⟩:=stage_big j δ t f (le_max_left w w') (min_le_left γ γ') le_rfl v M S p
 obtain ⟨-,l'⟩:=stage_big j δ _ f' (le_max_right w w') (min_le_right γ γ') le_rfl v M S p
 have he: IsStarProjection B:= by unfold B; rw [← t_comp]; exact cutM_idp _
 let F:=Comb B P k; let X:=Comb B Q k; let Z:=Comb B A k
 have hp: ‖(X-Z)*Vo S‖≤ 1:=by simpa only [t,X,Z,ice_at] using l _ h s y
 have hg: ‖(star X-star Z)*Vo S‖ ≤ 1:=by
    have ht:t.flip.stem B Q=star X:=by rw [flip_p _ _ _ y he]; unfold t; rw [ice_at]
    have hu:t.flip.stem B A=star Z:=by rw [flip_p _ _ _ p he]; unfold t; rw [ice_at]
    rw [←ht,←hu]; exact l' U h s y
 have hf: twist Y F=X:=by have he: F=t.stem B P:= (ice_at ..).symm; rw [he, t.spin, show twist Y P=Q from u, show twist Y B=B from Cascade.tick_g .. ]; exact ice_at .. -- tune
 have ht (i:Slot)(F G: Op (Single n))(a:‖(F-G)*Vo S‖≤1)(b:‖acts G (basisKet (x.1,i))‖ ≤ R): ‖acts F (basisKet (x.1,i))‖≤ 1+R:=by
    let T:=basisKet (x.1,i); refine (norm_le_norm_sub_add (acts F T) (acts G T)).trans (add_le_add ?_ b); rw [←act_sub]; nth_rw 1 [← show acts (Vo S) T=T from (within_basis (modesIn n S) _ ((modes_at ..).2 z))]; rw [←act_mul]; apply (Flare.opy ..).trans; unfold T; simpa [basisKet] using a
 apply (sparks p' T r h' k i (45*(1+R)))
 · apply seriesG F g x; rw [hf]; exact fun l=> ht l X Z hp (H n M k p (x.1,l)).1
 apply seriesG (star F) g x; rw [map_star, hf]; exact fun l=> ht l _ _ hg (H n M k p (x.1,l)).2
end YM.CF.Papyrus.Franc
