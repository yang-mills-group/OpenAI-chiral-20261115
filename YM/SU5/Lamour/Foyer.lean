import YM.SU5.Lamour.Stock
import YM.SU5.Lamour.Sleigh
/-!
# landing. turn corners through g and through lens. retain precision lease.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 145000
noncomputable section
namespace YM.CF.Lamour
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {N:Side}{a j d r:ℕ}{e ε δ z u:ℝ}
section cols
variable {n:Type*}[LinearOrder n][Fintype n][Nonempty n]{P Y L:Op n}{X W T Z:Finset n}
lemma entry_c (g:Wat W P e)(i j:n)(v:j∈ W): ‖P i j‖≤ e:=by rw [←basis_act P i j, ←basis_inner]; exact (norm_inner_le_norm ..).trans (by simp [g j v]) -- simp
lemma ray_cash (h:1≤e)(p:Wat W P e)(q:Wat W (star P) e)(Z:Finset n)(U:Finset n): Bun (ray P Z) U W e:=by
 intro j w; have ht(A:Op n)(p:Wat W A e): (∑ i∈ U,‖A i j‖^2) ≤ (e^2)^2:=by
    rw [←measure_col,act_mul]; exact pow_le_pow_left₀ (norm_nonneg _) ((pcut ..).trans ((p j w).trans (by nlinarith))) _
 cases hx:shadeK Z j with
 | true =>
    refine (sum_le_sum (g:=fun i=>‖star P i j‖^2) (fun i _=> ?_)).trans (ht _ q); change ‖fern (shadeK Z i) _ P _ _‖^2 ≤ _; unfold fern; rw [hx]; cases shadeK Z i; · rw [if_neg (by decide), if_neg (by decide),basis_inner,basis_act,Matrix.star_apply,norm_star];
                                                                                  
    rw [if_pos rfl,norm_zero]; norm_num
 | false =>
    refine (sum_le_sum (g:=fun i=>‖P i j‖^2) (fun i _=> ?_)).trans (ht _ p); change ‖fern _ (shadeK Z j) P _ _‖^2≤_; unfold fern; rw [hx]; cases shadeK Z i; · rw [if_pos rfl,norm_zero]; norm_num
    rw [if_neg (by decide),if_pos rfl,norm_neg,basis_inner,basis_act]
lemma Wat.ray_p (g:Wat W P e)(h:Wat W (star P) e) (Z:Finset n) (i j:n)(v:j∈W): ‖ray P Z i j‖≤ e :=by
 change ‖fern (shadeK Z i) (shadeK Z j) P (basisKet _) (basisKet _)‖≤ e; have he: ‖P i j‖≤ e:= entry_c g _ _ v; have ht: ‖P j i‖≤ e:= (by simpa [Matrix.star_apply] using entry_c h i _ v); unfold fern; split; rw [norm_zero]; exact (norm_nonneg _).trans he; split; · rw [norm_neg,basis_inner,basis_act]; exact he
 rw [basis_inner,basis_act]; exact ht
lemma ray_toll (p:Wat W (P-L) ε)(q:Wat W (star (P-L)) ε)(v:j≤d)(Z:Finset n) (i j:n)(w:j∈W) : ‖ray P Z i j-ray L Z i j‖≤ ε :=by
 apply (Wat.ray_p p q Z i j w).trans'; show ‖fern (shadeK Z i) (shadeK Z j) _ (basisKet i) _-fern _ _ _ _ _‖ ≤_; have hx(b a:Bool)(x y: Ket n): fern b a P x y - fern b a L x y=fern b a (P-L) x y:=by cases b <;> cases a <;> simp [fern,inner_sub_right] <;> abel
 rw [hx]; exact le_rfl
lemma pet_shop (p:Wat T ((cutM W)*P) (e^2))(q:Wat T ((cutM W)*(star P)) (e^2))(Z:Finset n): Bun (ray P Z) W T e:=by
 intro j v; cases hx:shadeK Z j with
 | true =>
    refine le_trans ?_ ((show ∑ i∈ W,‖star P i j‖^2=‖acts (cutM W*star P) (basisKet j)‖^2 from (measure_col ..).symm).le.trans (pow_le_pow_left₀ (norm_nonneg _) (q j v) _)); apply sum_le_sum; intro i u; change ‖fern (shadeK Z i) _ _ (basisKet i) _‖^2≤_; rw [hx]; cases shadeK Z i; · simp [fern, Matrix.star_apply,basis_inner,basis_act] -- tune
    simp [fern, sq_nonneg]
 | false =>
    refine le_trans ?_ ((show ∑ i∈ W,‖P i j‖^2=‖acts (cutM W*P) (basisKet j)‖^2 from (measure_col ..).symm).le.trans (pow_le_pow_left₀ (norm_nonneg _) (p j v) _)); apply sum_le_sum; intro i u; change ‖fern _ (shadeK Z j) _ _ _‖^2≤_; rw [hx]; cases shadeK Z i; · simp [fern, sq_nonneg]
    simp [fern,basis_inner,basis_act]
lemma Wat.zen (p:Wat T P e)(q:e≤ε): Wat T P ε:=fun i t=>(p i t).trans q
lemma plaza (p:T⊆ W)(g:Wat W P e): Wat T P e:=fun i v=> g i (p v)
lemma Wat.trimC (p:Wat T P e)(S: Finset n): Wat T (cutM S*P) e:=fun i t=>by rw [act_mul]; exact (pcut ..).trans (p i t)
end cols
namespace Bridge
variable {T S X:Finset (Seat N)}{P:Pane N}{M:Tulip.Male}
local notation "ℶ" => modesIn N
local notation "⚜" => sill N j M z
lemma Wat.across {P Q:Op (Single N)}(g:Seat N→SU.E)(h:twist (tradew N g) P=Q)(w: Wat (ℶ T) Q e)(t:0≤e): Wat (ℶ T) P (180*e):=by
 intro i l; let x:=node i.1.1; let D:= modesIn N {x}; have he:D=pet x:=by ext; simp [D,pet,modeX]; -- tune
 have hp:D⊆ ℶ T:=modes_monotone (singleton_subset_iff.mpr ((modes_at ..|>.1 l)))
 let V:=twist (tradew N g); have hu:‖P*cutM D‖=‖Q*cutM D‖:=by rw [← twist_norm (tradew N g),map_mul,gauge_frost {x} g,h]
 apply (cash_cut (S:=D) _ i (modes_at ..|>.2 (mem_singleton_self _))); apply hu.trans_le; exact (cut_bill t (plaza hp w)).trans (mul_le_mul_of_nonneg_right (by rw [he]; exact_mod_cast spot_cost x) t) -- tune order apply undec
lemma acreage(S:Finset (Seat N)): (ℶ S).card ≤ 180*S.card:=by
 have he:ℶ S=S.biUnion fun i=>pet i:=by ext i; rw [modes_at,mem_biUnion]; simp [pet,modeX] -- tune
 rw [he]; exact (card_biUnion_le ..).trans ((sum_le_sum (g:=fun _=>180) (fun i _=> spot_cost i)).trans_eq (by rw [sum_const,nsmul_eq_mul,mul_comm,Nat.cast_id])) -- tune
/-- who bought range at their settings -/
def Margin(N:Side)(j:ℕ)(e:ℝ)(r:ℕ):Prop:=∀ M, ∃ V, Glaze.Ranged r V ∧ Glaze.Billow e (lake N j M - V)
abbrev Truth (N:Side)(j:ℕ)(u:ℝ):Prop:=∀ M, Glaze.Billow u (lake N j M)
lemma stockyard(p:1 ≤ j): ∃ x:ℝ,0<x∧ (∀ {N:Side},Even N.val → Truth N j x) ∧ ∀ e>(0:ℝ), ∃ a w, ∀ {N:Side}, Kea.Pad j N→ a≤N.val→ Margin N j e w:=by
 obtain ⟨x,t,H⟩:=lake_local p; refine ⟨x,t,H,fun e v=>?_⟩; obtain ⟨w,t,T⟩:=lake_range p e v; exact ⟨t,w, T⟩ -- implicit ↑
lemma toe_cut (p:Glaze.Ranged r (lake N j M)∨ True)(h:Distant (r+1) S T) {A:Op (Single N)}(v:Glaze.Ranged r A): Vo S*A*Vo T=0:=by
 ext i j; unfold Vo cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; split_ifs with u w; all_goals first| simp only [one_mul,mul_one,mul_zero,zero_mul,Matrix.zero_apply] -- tune
 exact v i j (h _ ((modes_at ..).1 u) _ ((modes_at ..).1 w))
lemma Wat.until (c: Clear S P j M z ε)(t:Distant (r+1) T S)(v:Margin N j e r) : Wat (ℶ S) (Vo T*sill N j M z P) (ε+e) ∧ Wat (ℶ S) (Vo T* star (sill N j M z P)) (ε+e):=by
 let A:=sill N j M z P; let P:=Vo T; let Q:=Vo S; let L:=lake N j M; obtain ⟨X,w,d⟩:=v M
 have ht {X Z V:Op (Single N)}(w: Glaze.Ranged r X)(p:Wat (ℶ S) (Z-V) ε)(e': Wat (ℶ S) (V-X) e): Wat (ℶ S) (P*Z) (ε+e):=by
    intro i x; have hu: Wat (ℶ S) (P*(Z-X)) (ε+e):=by apply _root_.YM.CF.Lamour.Wat.trimC; rw [show Z-X=(Z-V)+(V-X) by abel]; exact p.add' e'
    apply (hu i x).trans'; have hx:acts (P*X) (basisKet i)=0:=by
       nth_rw 1 [←show acts Q (basisKet i)=basisKet i from (cut_basis ..).trans (if_pos x)]; rw [←act_mul, toe_cut (M:=M) (j:=j) (Or.inr trivial) t w,act_zero] -- p new
    rw [mul_sub,act_sub,hx,sub_zero]
 refine ⟨ht w c.reach (fun i _=> (d i).1),?_⟩; apply ht (V:=star L) w.star; rw [←star_sub]; exact c.fetch; rw [←star_sub]; exact fun i _=> (d i).2
lemma liftleigh (p:Truth N j u)(h:Clear S P j M z e): Wat (ℶ S) (sill N j M z P) (e+u) ∧ Wat (ℶ S) (star (sill N j M z P)) (e+u):=by
 let V:= sill N j M z P; let L:= lake N j M; have hh:= h.fetch; have ht: V= (V-L)+L:= (sub_add_cancel ..).symm; change Wat _ V _ ∧ _; refine ⟨?_,?_⟩ -- rewrite might change everywhere
 · rw [ht]; exact h.reach.add' (fun i _=> (p M i).1)
 rw [show star (sill N j M z P) =star (V-L)+star L from (by rw [←star_add,←ht])]; exact hh.add' fun i _=> (p M i).2
lemma Wat.pine (v:Truth N j u)(h:Kea.Pad j N)(p:Sparkle N δ M j)(a:Guard P δ)(x:Seat N→SU.E)(u':0≤u)(q:0<z)(t:z≤1)(y:0≤e)(u_:0≤ε)(l:Margin N j ε r)(t_: Clear S (Lattice.gauge x P) j M z e):
 let V:= sill N j M z P; Wat (ℶ S) V (180*(e+u)) ∧ Wat (ℶ S) (star V) (180*(e+u)) ∧ (∀ b:Bool, Wat (ℶ S) (fleece N j z M P b) (180*e)) ∧
 ∀ (T:Finset (Seat N)),Distant (r+1) T S → Wat (ℶ S) (Vo T * V) (180*(e+ε)) ∧ Wat (ℶ S) (Vo T * star V) (180*(e+ε)):=by
 intro V; obtain ⟨d,w⟩ := mica x p q t a; obtain ⟨U,D⟩:=liftleigh v t_; have he:0 ≤ e+u:= add_nonneg y u'; let X:= sill N j M z (Lattice.gauge x P); have hX:twist (tradew N x) (star V)=star X:= by rw [map_star,←d]; -- tune V
 refine ⟨Wat.across x d.symm U he, Wat.across x hX D he,fun b=>Wat.across x (w b).symm (t_.yarn b) y,fun T θ=>?_⟩; have ht:= Wat.until t_ θ l; refine ⟨Wat.across x (by rw [map_mul,gauge_frost,show twist (tradew N x) V = _ from d.symm]) ht.1 (by positivity), Wat.across x (by rw [map_mul,hX,gauge_frost]) ht.2 (by positivity)⟩
end Bridge
end YM.CF.Lamour
#print axioms YM.CF.Lamour.Bridge.Wat.pine
#print axioms YM.CF.Lamour.pet_shop
