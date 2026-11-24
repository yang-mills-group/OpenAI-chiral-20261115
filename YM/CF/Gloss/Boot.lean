import YM.CF.Gloss.Scene
import YM.CF.Floe.Tex
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gloss
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire
attribute [local instance] opCStarAlgebra
variable {m B N:Side}
variable{A D d e:ℝ}{m B:Side}{c:Part m B}{W:Scroll m B c}
variable(x:Era m)(i:costG m B)(U:Skin m B)(y: Cue m)(h:ScaleK A D W)(g:Budget B e d)
-- ancestors must be paid. Cycle as elsewhere. Off-chart powers support.
lemma chairs_P (S:Support (Domain m B)): (chairs m B S).image (ρx x)=chairs m B (S.image (ψx B x)) :=by
 ext i; obtain ⟨i,rfl⟩:=(ρx x).surjective i; simp only [mem_image, Equiv.apply_eq_iff_eq,exists_eq_right]; rw [chaff,chaff]; constructor
 · rintro ⟨q,l,V,v,H⟩; exact ⟨_, mem_image_of_mem _ l,_,(active_b B x _ _).mpr v,(tx x _ _).mpr H⟩
 rintro ⟨q,l,V,v,H⟩; obtain ⟨q,l,rfl⟩:= mem_image.mp l; obtain ⟨V,rfl⟩:=(ρx x).surjective V; exact ⟨q,(by simpa only [mem_image,Equiv.apply_eq_iff_eq,exists_eq_right] using l),V,(active_b ..).mp v,(tx x _ _).mp H⟩
lemma padP(S:Support (Domain m B)): (pavilion m B S).image (ρx x)=pavilion m B (S.image (ψx B x)):=by
 ext i; obtain ⟨i,rfl⟩:=(ρx x).surjective i; simp only [mem_image,Equiv.apply_eq_iff_eq,exists_eq_right]; rw [pad_iff,pad_iff]; have ht(a b: Index m): separation (ρx x a) (ρx x b)=separation a b:=by unfold ρx; exact (separation_translate ..).trans (separation_signed ..)
 constructor
 · rintro ⟨q,l,V,v,H⟩; exact ⟨_, mem_image_of_mem _ l,_,(matB B x _ _).mpr v, (ht V i).trans_le H⟩
 rintro ⟨q,l,V,v,H⟩; obtain ⟨q,l,rfl⟩:= mem_image.mp l; obtain ⟨V,rfl⟩:=(ρx x).surjective V; rw [ht] at H; exact ⟨q,(by simpa only [mem_image,Equiv.apply_eq_iff_eq,exists_eq_right] using l),V,(matB ..).mp v,H⟩
lemma wallP(S:Support (Domain m B)):(walls m B S).image (ψx B x)=walls m B (S.image (ψx B x)):=by
 unfold walls; rw [image_union]; congr 1; rw [←padP,image_biUnion,biUnion_image]; apply biUnion_congr rfl; exact fun i _=> ξ_p x B i
lemma grove_e (S:Support (Domain m B))(h: Grove (terr _) S): Grove (terr _) (S.image (ψx B x)):=by
 induction h with|single=>rw [image_singleton]; exact .single _|join _ y h ih=> rw [image_insert]; exact .join ih (mem_image_of_mem _ y) (((separation_translate ..).trans (separation_signed ..)).trans_le h) -- tune
lemma ripp(m:Side):0 ≤ rip m:=by unfold rip; positivity
include h g
def tenorQ (i:costG m B): Stamp m B:=i.2.image (ψx B i.1)
def dinQ {c:Part m B}(W:Scroll m B c)(d:ℝ) (i:costG m B):ℝ:= rip m*dust W d i.2
lemma χs : supportsCup m B (tenorQ i) (seedQ W i) (dinQ W d i) e:=by
 let F:=i.1; let T:=i.2; let V:=vest B F; obtain ⟨q,y,l,u,w,H⟩:=leavings h g T; have hx(x):x∈payer m B e→ V x∈payer m B e:=fun t=> voxel B F e x t
 refine ⟨(continuousOn_const (c:=rip m)).smul ((kilo_o _).comp_continuousOn (q.comp (vest_p F).continuousOn (fun _=>hx _))),fun x p=> ?_,mul_nonneg (ripp m) l,fun z x p=> ?_,fun p=>grove_e i.1 T (w (right_ne_zero_of_mul p)),?_⟩
 · unfold seedQ workQ dinQ; rw [norm_smul,pay_t,Real.norm_of_nonneg (ripp m)]; exact mul_le_mul_of_nonneg_left (y _ (hx x p)) (ripp _)
 · obtain ⟨f,K⟩:= squirm B F z x; change _ • payZ F (W.leftover _ (V _)) = _; rw [show V _=_ from K]; exact congrArg (fun x:ℂ=>rip m • payZ F x) (u f (V x) (hx _ p))
 intro x p y k r h; unfold seedQ workQ; apply congrArg; apply congrArg; apply H _ (hx x p) _ (hx y k) ?_ (setN _ _ _ _ (by rw [wallP]; exact h))
 intro j u; have hp: (ρx F j) ∈ chairs m B (tenorQ i):=by unfold tenorQ; rw [←chairs_P]; exact mem_image_of_mem _ u
 exact congrArg (doveV F.charge) (r _ hp)
lemma hit_μ{a v:ℝ}(y:∀ i,cellHit m B a (dust W d) i ≤ v)(k: Index m) : (∑ i:costG m B,if k∈pavilion m B (tenorQ i) then rent a (pavilion m B (tenorQ i))*dinQ W d i else 0) ≤ v:=by
 let V:=pavilion m B; rw [Fintype.sum_prod_type]; have hp:=Fintype.card_pos (α:=Era m); have h (i: Era m): ∑ j:Stamp m B,(if k∈V (tenorQ (i,j)) then rent a (V (tenorQ (i,j)))*dinQ W d (i,j) else 0) ≤ rip m*v:=by
    apply le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (y ((ρx i).symm k)) (ripp m)); unfold cellHit spotHit; rw [sum_filter,mul_sum]; apply sum_congr rfl; intro j _; have hv: V (tenorQ (i,j))=(V j).image (ρx i):=(padP i j).symm; rw [hv]; obtain ⟨k,rfl⟩:=(ρx i).surjective k; unfold V at *; unfold rent; simp only [mem_image, Equiv.apply_eq_iff_eq, exists_eq_right,Equiv.symm_apply_apply,mul_ite,mul_zero, card_image_of_injective _ (ρx i).injective]; split<;> (first|rfl|exact mul_left_comm ..)
 apply (sum_le_sum (fun i _=>h i)).trans_eq; rw [sum_const,card_univ,nsmul_eq_mul, ←mul_assoc]; unfold rip; rw [mul_inv_cancel₀ (by positivity),one_mul]
omit h g -- shadow
variable {L:Side}{j:ℕ}{ho:Odd L.val}{T:Paige.Pricing j L ho (Vault.Thread j)}{e:ℝ}{P: Paige.Grasp T B e} -- tune duplicate e & actual
end YM.CF.Gloss
