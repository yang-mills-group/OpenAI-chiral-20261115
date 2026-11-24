import YM.SU5.FiniteGaugeData.Pannier.Gale
/-! # The sparse **both** spin stencils.
used on a repaired gauge, simultaneously for any number of insertions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {z R ε:ℝ}
section
variable {ι:Type*}[LinearOrder ι][Fintype ι][Nonempty ι]
variable {X U Y: Op ι}{s S D:Finset ι}
private lemma altar {δ:ℝ} (h:IsUnit X)(p:‖X⁻¹‖≤R) (u:‖Y-X‖≤δ)(q:δ*R ≤ 1/3) : IsUnit Y ∧ ‖Y⁻¹‖ ≤2*R:=by
 let T:= Y*X⁻¹; have ht: ‖T-1‖≤1/3:=by
   rw [show T-1=(Y-X)*X⁻¹ from (by unfold T; rw [sub_mul,(live h).1])]; exact (norm_mul_le ..).trans ((mul_le_mul u p (norm_nonneg _) ((norm_nonneg _).trans u)).trans q) -- last matches upper δ
 obtain ⟨t,hT⟩:= Fock.inv_close_le (1:UNI _) ht
 have hf: IsUnit Y:=live_of (S:=X⁻¹*T⁻¹) (by rw [←mul_assoc]; exact (live t).1)
 refine ⟨hf,?_⟩; have hu:Y⁻¹=X⁻¹*T⁻¹:=Matrix.inv_eq_right_inv (by rw [←mul_assoc]; exact (live t).1)
 rw [hu,mul_comm 2]; apply (norm_mul_le ..).trans; exact mul_le_mul p hT (norm_nonneg _) ((norm_nonneg _).trans p)

private def Wdiag (X:Op ι): Op ι:= Matrix.diagonal fun i=>X i i
private lemma sermon (w:0<z) (hp:∀ i, z≤ ‖X i i‖) :
    IsUnit (Wdiag X) ∧ ‖(Wdiag X)⁻¹‖ ≤ z⁻¹ := by
 let D:Op ι:=Matrix.diagonal fun i=>(X i i)⁻¹
 have he: Wdiag X*D=1:=by
    unfold D; rw [Wdiag,Matrix.diagonal_mul_diagonal,←Matrix.diagonal_one]; congr; ext i; rw [mul_inv_cancel₀ (by have hx:= w.trans_le (hp i); exact norm_pos_iff.mp hx)] -- tune
 refine ⟨live_of he,?_⟩; rw [Matrix.inv_eq_right_inv he]; unfold D; rw [Matrix.l2_opNorm_diagonal]; apply (pi_norm_le_iff_of_nonneg (by positivity)).2; intro i; rw [norm_inv]; exact inv_anti₀ w (hp i)
private lemma snowfall (Y:Op ι)(p:‖(Y-X)*cutM s‖ ≤ ε): ‖Fock.padded s Y-Fock.padded s X‖≤ε:=by
 rw [show Fock.padded s Y-Fock.padded s X= cutM s*((Y-X)*cutM s) from ?_]; exact ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _))).trans p
 rw [Fock.padded,Fock.padded,←mul_assoc,mul_sub,sub_mul,add_sub_add_right_eq_sub]
lemma cut_from_right (S T:Finset ι)(x:S ⊆ T):cutM T*cutM S=cutM S:=by
 ext i j; rw [cutM,Matrix.diagonal_mul]; by_cases p:i=j; · subst j; by_cases z:i∈S; simp [cutM,z,x z]; simp [cutM,z]
 simp [cutM,p]
lemma cut_from_left (S T:Finset ι)(x:S ⊆ T):cutM S*cutM T=cutM S:=by
 have hg:= congr_arg star (cut_from_right S T x); rwa [star_mul,(cutM_idp _).isSelfAdjoint,(cutM_idp _).isSelfAdjoint] at hg
lemma cut_less (h:s⊆ S):cutM (S \ s)= cutM S-cutM s:=by
 unfold cutM; rw [Matrix.diagonal_sub]; congr 1; ext i; by_cases p:i∈ s; · simp [p,h p]
 simp [p]
lemma within_more {x:Ket ι}(h:withinM s x)(p:s⊆S) : withinM S x:=by unfold withinM; nth_rw 1 [←h]; rw [←act_mul,cut_from_right _ _ p,h]
lemma bill_cut (h:‖U*cutM S‖≤ ε) (p:s ⊆ S) : ‖U*cutM s‖≤ ε:=by
 rw [←cut_from_right _ _ p,←mul_assoc]; exact ((norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _))).trans h
end
variable {M:Tulip.Male}{n:Side}{S s D:Finset (Seat n)} {δ γ:ℝ}{j w d:ℕ}
-- All distances on gauge torus
abbrev Vo (S: Finset (Seat n)):= cutM (modesIn n S)
def Distant (w:ℕ) (s T:Finset (Seat n)): Prop := ∀ x∈s,∀ y∈T,w ≤ separation x y
def Sparse (d:ℕ)(S:Finset (Seat n)):Prop:= ∀ x∈S,∀ y∈S,x ≠ y → d ≤ separation x y
lemma Sparse.mono (p:d≤w)(u:S ⊆ s): Sparse w s→Sparse d S:= fun g x hx y hy h=> p.trans (g _ (u hx) _ (u hy) h) -- gcongr dir?
lemma Distant.symm (U:Distant d s S): Distant d S s:=fun x hx y hy=> (separation_comm x y) ▸ U y hy x hx
lemma Distant.mono {D L:Finset (Seat n)}(h:Distant d D L)(p:s ⊆ D)(u:S⊆ L): Distant d s S:= fun x hx y hy=> h _ (p hx) _ (u hy)
abbrev sp (b:Bool)(j:ℕ)(M:Tulip.Male)(P:Pane n):=hand b (spar j M P)
def HearthB (R:ℝ)(P: Op (Single n))(s: Finset (Seat n)) := let U:= Fock.padded (modesIn n s) P; IsUnit U∧ ‖U⁻¹‖ ≤ R
lemma HearthB.weaken {R E:ℝ}{P:Op (Single n)}(g:HearthB R P s)(p:R ≤ E) : HearthB E P s:= ⟨g.1,g.2.trans p⟩
private lemma Wspot (u:0<z)(q:z≤1)(P: Op (Single n))(h:∀ i, z≤‖P i i‖) : ∀ i:Single n,z≤‖Fock.padded (modesIn n S) P i i‖:=by
 intro i; by_cases p:i∈ modesIn n S; · simpa [Fock.padded,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul, (modes_at ..).1 p] using h i
 simpa [Fock.padded,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul, show node i.1.1 ∉ S from fun x=> p ((modes_at ..).2 x)] using q
private lemma offsite {b:Bool} (u:Winter j δ n γ d (z/3))(p:0≤δ) (t:Sparse d S) (P:Op (Single n)) (e:P= sp b j M (1:Pane n)) (w:∀ i k:Single n, i.1.1=k.1.1 → i≠k → P i k=0) :
 let U:=Fock.padded (modesIn n S) P; ‖U-Wdiag U‖ ≤ z/3:=by
 intro U; apply u.vent b M (1:Pane n) (guard0 p); intro i k; by_cases g:i=k; subst k; simp [Wdiag]
 rw [Matrix.sub_apply,Wdiag,Matrix.diagonal_apply_ne _ g,sub_zero]; unfold U; rw [Fock.padded,Matrix.add_apply]; -- unfold cut
 by_cases h:i∈ modesIn n S<;>by_cases e':k∈ modesIn n S
 all_goals simp only [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.one_apply_ne g,Matrix.sub_apply,Matrix.diagonal_apply_ne _ g]
 · simp only [if_pos h,if_pos e', mul_one,one_mul, sub_zero,add_zero]; by_cases a:i.1.1=k.1.1; exact Or.inl (w i k a g)
   exact Or.inr ⟨t _ ((modes_at ..).1 h) _ ((modes_at ..).1 e') (fun v=> a (Tenant.needle v)),le_of_eq (congrArg (fun A:Op (Single n)=> ‖A i k‖) e)⟩
 all_goals simp only [*, if_pos,if_false,mul_zero,zero_mul,sub_zero,add_zero, true_or] -- may tune
lemma hearth_price (u:Winter j δ n γ d (z/3))(p:0<z)(q:z≤1)(h: Sparse d S)(b:Bool)(e:0≤δ)(k:∀ i, z≤‖sp b j M (1:Pane n) i i‖)(f:∀ i l:Single n,i.1.1=l.1.1→i≠l→sp b j M (1:Pane n) i l=0) :
 HearthB (2*z⁻¹) (sp b j M (1:Pane n)) S:=by
 obtain ⟨g,hp⟩:= sermon p (Wspot (S:=S) p q _ k)
 exact altar g hp (offsite u e h (sp b j M (1:Pane n)) rfl f) (by field_simp; rfl)
variable {ε:ℝ}{U:Pane n}{b:Bool}
lemma chosenFlatPrice (j:ℕ)(p:1≤j): ∃ R δ:ℝ,0<R ∧ 0<δ ∧ ∃ N d:ℕ,
    (∀ n:Side,N ≤ n.val→∀ S:Finset (Seat n), Sparse d S→∀ (M:Tulip.Male)(b:Bool),HearthB R (sp b j M 1) S) ∧
    ∀ ε>(0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N≤n.val→Winter j δ n γ w ε:=by
 obtain ⟨δ,u,h,t⟩:= winter j p; obtain ⟨z,hz,k,f⟩:= kidney j p
 let z':= min z 1; have g:0<z':= lt_min hz zero_lt_one; have he:z'≤z:= min_le_left ..
 obtain ⟨a,_,d,l⟩:= t (z'/3) (by positivity)
 refine ⟨2*(z')⁻¹,δ,by positivity,u,max h k,d,fun n q S r M b=>?_,fun e he=>?_⟩
 · obtain ⟨hf,x⟩:= f n (by omega) M b; refine hearth_price (l n (by omega)) g (min_le_right ..) r b u.le (fun i=>?_) x
   obtain ⟨z,w,_,hl⟩:= hf i; unfold sp; rw [hl, Complex.norm_real,Real.norm_of_nonneg (hz.le.trans w)]; exact he.trans w
 obtain ⟨a,b,w,l⟩:=t e he; exact ⟨a,b,w,fun n q=>l n (by omega)⟩
lemma hearthB_wind (p: Winter j δ n γ w ε)(q:0≤δ)(u:Guard U δ)(e:Rightful (Lattice.halo w S) U 1 γ) :
    ‖(sp b j M U-sp b j M (1:Pane n))*Vo S‖≤ ε:=by
 apply p.plank b M S U 1 u (guard0 q) e; intro i k; unfold Vo cutM; rw [Matrix.mul_diagonal]; split
 next h=> exact Or.inr ⟨(modes_at ..).1 h,le_of_eq (congrArg _ (mul_one _))⟩
 next _=>exact Or.inl (mul_zero _)
lemma hearthB_stands {P Q:Op (Single n)}(h:HearthB R P S)(g:‖(Q-P)*Vo S‖≤ε)(f:ε*R≤1/3): HearthB (2*R) Q S:= altar h.1 h.2 (snowfall _ g) f
lemma hearthB_cross (p:Winter j δ n γ w ε)(b:Bool)(M:Tulip.Male)(u:Guard U δ)(h:Distant w s S): ‖Vo s*sp b j M U * Vo S‖≤ ε:=by
 apply p.vent b M U u; intro i k; unfold Vo cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; split <;> rename_i he; split; next v=> rw [one_mul,mul_one]; exact Or.inr ⟨h _ ((modes_at ..).1 he) _ ((modes_at ..).1 v),le_rfl⟩
 all_goals simp_all -- tune
lemma Vo_less (u: s⊆ S): Vo (S \ s)=Vo S-Vo s:=by
 have ht:modesIn n (S \ s)=modesIn n S \ modesIn n s:= by ext; simp
 unfold Vo; rw [ht,cut_less (modes_monotone u)]
lemma Vo_neg : Vo (Sᶜ)=1-Vo S:=by
 unfold Vo; rw [show modesIn n Sᶜ=(modesIn n S)ᶜ from ?_,dim_cut]; ext; simp
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.chosenFlatPrice
