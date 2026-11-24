import YM.CF.Sour.Stow
import YM.CF.Vp929.Match.Reframe
/-! Adapted from Exa and Milo.Spear to retain Poetic certificates. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Exa
open Function Filter Metric Lattice Wilson Laurent Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Branch NormedSpace Finset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Thera Haro
open Sour
variable {ρ:ℝ}[Nonempty (ΘS ρ)](e:ℝ)(N:Side){a b r:ℝ}
structure Pinion (F:Gem N (ΘS ρ))(a r:ℝ) : Prop where
 has: ∃ T:Lawn N e F a r, Tempered (Sour.hull T) ∧ ∀ X:Support (More N),X.card≠1→ T.W X=0
open Branch
lemma boxX {J:Type*}[Fintype J](R:J→Support (More N))(h:∀ j,(R j).card=1)(Y:Gem N (ΘS ρ))(M:J→ΘS ρ→Raw (Openc (More N) e) (Single N))(C:J→Toll (Single N))(uΩ:∀ j:J,∀ x:Openc (More N) e,Poetic (fun i=> M j i x))(q:∀ i,pendB (badge _) (bail N e) (bail N e) (M i) (R i) (C i))(p:∀ i y,Y i y.val=∑ j:J,M j i y)(r_:0 ≤ r)(w:∀ i:Single N,∑ j:Single N,∑ k:J,Branch.rent a (R k)* C k i j ≤ r)(u:∀ j:Single N,∑ i:Single N,∑ k:J,Branch.rent a (R k)*C k i j ≤ r) : Pinion e N Y a r:=by
 let X S i j:=∑ k∈ dest R S,C k i j
 let F(S: Support (More N))(i:ΘS ρ)(x:Openc (More N) e):= ∑ k∈dest R S,M k i x
 have he(i j):saleM a X i j=∑ k:J,Branch.rent a (R k)*C k i j:=by rw [lump R (fun k=>_)]; unfold saleM X; apply sum_congr rfl; intro Z _; rw [mul_sum]; exact sum_congr rfl fun k v=> by rw [(mem_filter.mp v).2]
 have ht(S:Support (More N)):pendB (badge _) (bail N e) (bail N e) (F S) S (X S):=by
    unfold F; refine ⟨fun i=> ⟨Ticket.sumT (dest R S) C (fun k=>M k i) (fun k h=> (mem_filter.mp h).2 ▸ (q k|>.1 i).toTicket), (badge _).suppose (dest R S) (fun k=>M k i) (fun k _=> (q k|>.1 i).fuel)⟩,fun i=>continuous_finsetSum _ (fun k _=>(q k).2 i)⟩
 refine ⟨⟨⟨F,X,ht,⟨r_,fun i=>?_,fun j=>?_⟩,fun i x=>(p i x).trans (Branch.lump R _)⟩,fun S y=>Poetic.cogv _ _ (fun j _=> uΩ j y),?_⟩⟩; · simp_rw [he]; exact w _
 · simp_rw [he]; exact u _
 intro S x; funext i j; exact sum_eq_zero fun k v=> False.elim (x ((mem_filter.mp v).2 ▸ h k))
lemma pawnO (x y:SpinIdx)(V:ΘS ρ→Op Slot)(K:ℝ)(p:0≤K)(h:Continuous V)(u:∀ i,‖V i‖ ≤ K)(hU:Poetic V)(v:∀ i g,mater g*V i= V i*mater g): Pinion e N (fun i _=>∑ b:Site N,panel (b,x) (b,y) (V i)) a ((Fintype.card Slot)*(Tap.Br a*K)):=by
 let F(t:Site N):=(t,x); let Y(t:Site N):=(t,y); let R(t:Site N): Finset (Site (More N)):={node t}; let X(b):= reed (F b) (Y b) K; let A(t:Site N)(i:ΘS ρ)(_ : Openc (More N) e):=panel (F t) (Y t) (V i)
 have he(i:Site N): pendB (badge _) (bail N e) (bail N e) (A i) (R i) (X i):=by
    constructor
    · intro l; exact panel_ticket (s:=bail N e) (t:=bail N e) (p:=fun g v=>matter (g (node v.1))) (q:=fun g v=>matter (g (node v.1))) (fun _=> rfl) (fun _=> rfl) _ _ _ _ (fun _=>V l) (.single _) (fun k=>show node i∈ R i from mem_singleton_self _) (fun k=>show node i∈ R i from mem_singleton_self _) (fun g x=> (v l (g (node i))).symm) p ((badge _).base (V l)) continuous_const (fun x=>u _) (fun x y=> (by rw [sub_self,norm_zero]; exact mul_nonneg p ((forum N e).pos ..)))
    intro z; apply continuous_matrix; intro a b; unfold A panel; simp only [Matrix.of_apply]; split; exact h.matrix_elem ..; exact continuous_const
 have hv :0 ≤ Br a*K:=mul_nonneg (by unfold Br; positivity) p
 have hx i k l: Branch.rent a (R i)*X i k l=reed (F i) (Y i) (Br a*K) k l:=by simp [R,Branch.rent,Br,X,reed,mul_ite]
 refine boxX e N R (fun _=> Finset.card_singleton _) _ A X ?_ he (fun i _=>rfl) (by positivity) ?_ ?_
 · intro b z; exact Poetic.c_lin (panel (F b) (Y b)) (by intro X Y; ext i j; unfold panel; simp only [Matrix.add_apply,Matrix.of_apply]; split <;> simp) (by intro m x; ext i j; unfold panel; simp only [Matrix.smul_apply, Matrix.of_apply]; split <;> simp) hU
 · intro i; simp_rw [hx]; exact wheel F (fun a b h=> congr_arg Prod.fst h) Y _ _ (fun _=> le_rfl) hv _
 intro i; simp_rw [hx]; have hh t l k : reed (F t) (Y t) (Br a*K) l k=reed (Y t) (F t) (Br a*K) k l:=by unfold reed; simp only [and_comm]
 simp_rw [hh]; exact wheel Y (fun a b h=>congr_arg Prod.fst h) F _ _ (fun _=>le_rfl) hv _
lemma Pinion.portion {J:Type}(S:Finset J)(F:J→Gem N (ΘS ρ))(r:J→ℝ)(p:∀ i∈S,Pinion e N (F i) a (r i)):Pinion e N (fun i x=>∑ j∈ S,F j i x) a (∑ j∈S,r j):=by
 classical
 induction S using Finset.induction_on with
 |empty=> simp_rw [sum_empty]; refine ⟨⟨⟨_,_, (Elm.zero0 (n:=N) (κ:=ΘS ρ) e a).coat, (Elm.zero0 (n:=N) (κ:=ΘS ρ) e a).bank,?_⟩,fun _ _=>Poetic.zero,fun _ _=>rfl⟩⟩; simp [Elm.zero0]
 |insert i S g ih=>
    obtain ⟨U,k₀,h⟩:= (p i (mem_insert_self ..)).has; obtain ⟨V,k₁,hv⟩:= (ih fun i v=>p i (mem_insert_of_mem v)).has; let K:Elm _ _ _ _ _:= (Sour.hull U).plus (Sour.hull V)
    simp_rw [sum_insert g]; refine ⟨⟨⟨_,_,K.coat,K.bank,?_⟩,fun z v=> (k₀ z v).add (k₁ z v), fun z v=> (by change U.W z+ V.W z=0; rw [h _ v,hv _ v,zero_add])⟩⟩; intro j v; change F i j v.val + (∑ s∈S,F s j v.val)=∑ Z: Support (More N),(U.F Z j v+ V.F Z j v); rw [sum_add_distrib,U.shape]; congr 1; exact V.shape ..
lemma Pinion.big{P:Gem N (ΘS ρ)}{c:ℝ}(p:Pinion e N P a b)(v:b≤c):Pinion e N P a c:=by obtain ⟨H,k,g⟩:=p.has; exact ⟨⟨⟨_,_,H.coat,H.store.book v,H.shape⟩,k,g⟩⟩
lemma pawn_H (V:ΘS ρ→Op Slot)(K:ℝ)(T:Op SpinIdx)(p:0≤K)(h:Continuous V)(u:∀ i,‖V i‖ ≤ K)(hU:Poetic V)(v:∀ i g,mater g*V i= V i*mater g): Pinion e N (fun i _=>headW N T (V i)) a (wingRent T a * K):=by
 have hx(i j:SpinIdx):let c:= T i j; Pinion e N (fun x _=> ∑ b:Site N,panel (b,i) (b,j) (c • V x)) a ((Fintype.card Slot)*(Br a*(‖T i j‖*K))) := pawnO e N i j _ _ (by positivity) ((continuous_const (y:=T i j)).smul h) (fun i'=>by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (u i') (norm_nonneg _)) (hU.money _) (fun i g=> by rw [Matrix.mul_smul,Matrix.smul_mul, v])
 have he(z:Op Slot):headW N T z=∑ i:SpinIdx,∑ j:SpinIdx,∑ b:Site N, panel (b,i) (b,j) (T i j • z):=by ext ⟨⟨x,i⟩,b⟩ ⟨⟨y,j⟩,l⟩; change jump (Equiv.refl (Site N)) (fun _=>T⊗ₖ z) (x,i,b) (y,j,l)=_; rw [jump_apply]; by_cases h:x=y <;> simp [panel,h,Matrix.sum_apply,Prod.mk_inj,ite_and] <;> grind
 simp_rw [he]; apply Pinion.big _ _ (Pinion.portion e N Finset.univ _ _ (fun i _=> Pinion.portion e N Finset.univ _ _ (fun j _=>hx i j))); unfold wingRent; simp_rw [sum_mul, mul_assoc]; rfl
lemma bold_P (V:ΘS ρ→Op Slot)(K:ℝ)(p:0≤K)(h:Continuous V)(u:∀ i,‖V i‖ ≤ K)(pU:Poetic V)(v:∀ i,Mind (V i))(w:a ≤ 1): Pinion e N (fun i _=>κR N V i) a (wingRent (Aop-(1/2:ℂ) • 1) 1*K):=by
 let T:=Aop-(1/2:ℂ) • 1
 obtain ⟨F,k,b⟩:= (pawn_H (a:=a) e N V K T p h u pU fun i=>(v i).firm).has
 have ht(S:Support (More N)): pendB (badge _) (bail N e) (bail N e) (fun i X=> -F.F S i X) S (F.W S):=⟨fun i=> by simpa using (F.coat S|>.1 i).accel (-1),fun d=>(F.coat S|>.2 d).neg⟩
 refine Pinion.big e N (b:=wingRent T a*K) ?_ ?_; · refine ⟨⟨⟨_,_,ht,F.store,?_⟩,fun V x=> (k V x).neg,b⟩⟩; intro i x; rw [sum_neg_distrib]; exact congrArg Neg.neg (F.shape i x)
 apply mul_le_mul_of_nonneg_right _ p; exact sum_le_sum fun i _=> sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr w) (norm_nonneg _)) (by positivity)
end YM.CF.Exa
