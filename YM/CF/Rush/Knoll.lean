import YM.CF.Rush.Loop
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rush
open Fir Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N F:Side}(G:Ratio N F)
variable {a:Type*}[DecidableEq a][Fintype a]
lemma pilesP (f g:Momentum→Op a): plates N f*plates N g=plates N fun p=> f p*g p:=by unfold plates; rw [← map_mul,mark_prod]
lemma pilesM (f g:Momentum→Op a): plates N f-plates N g=plates N fun p=> f p-g p:=by unfold plates; rw [← map_sub,mark_sub]
lemma pilesA (f g:Momentum→Op a): plates N f+plates N g=plates N fun p=> f p+g p:=by unfold plates; rw [←map_add,mark_add]
lemma piles1 : plates N (fun _=>(1:Op a))=1:=by unfold plates; rw [unity_m,map_one]
lemma pilesS (f:Momentum→Op a):star (plates N f)=plates N fun p=>star (f p):=by unfold plates; rw [← map_star,mark_adj]
lemma pilesE (f g:Momentum→Op a)(h:∀ p,p∈realCube zone→p≠0→f p=g p): plates N f=plates N g:=by unfold plates; rw [dropped f g h]
open scoped Kronecker
lemma pilesV (Y: Op a): plates N (fun _=>Y)=jump (Equiv.refl _) (fun _=>Y):=by
  rw [plates,twist_formula]; change (overU N a).val * jump (Equiv.refl _) (fun _=>Y) * star (overU N a).val = _
  simp only [jump_replicate,overU,op_star_kron,op_kron_mul,mul_one,one_mul,(Lat.fourier_mem N).2,star_one]
lemma pilesI (f:Momentum→Op a)(h:∀ p,p∈realCube zone→p≠0→ IsUnit (f p)): IsUnit (plates N f) ∧ plates N (fun p=>(f p)⁻¹)=(plates N f)⁻¹:=by
  let C p:=(f p)⁻¹
  have he: plates N f*plates N C=1:=by rw [pilesP,← piles1]; exact pilesE _ _ fun p hp hg=> Matrix.mul_nonsing_inv (f p) ((Matrix.isUnit_iff_isUnit_det _).mp (h p hp hg))
  exact ⟨isUnit_iff_exists_inv.mpr ⟨_,he⟩,(Matrix.inv_eq_right_inv he).symm⟩
variable (j:ℕ)(L M:Side)(u:Bool)(hg:1≤j)(hJ:Even j)(hM:Odd M.val)
include hg hM in
lemma cBar: Reads (tub (bent u j M)) (bent u j M):=paid (bent_budget u j hg (fun _:Unit=>M) (fun _=>hM)) (fun _ p hp x hh=>by change bent u j M _=bent u j M _; unfold bent; rw [bar_overlap _ _ hp x hh]) ()
lemma cBrix (hi:Odd L.val) : Reads (tub (brix j L)) (brix j L):=by
  have he:= (trimP L).times (W_quote j L hi)
  change Pay (fun _:Unit=>1*1) (fun _=> brix j L) at he; exact paid he (fun _ p hp x hh=> verifies _ _ hp x hh) ()
include hM hg hJ in
lemma cBoards (hi:Odd L.val): Reads (tub (boards u j L M)) (boards u j L M):=by
  have he:= (trimP L).times (ticket u j L (fun _:Unit=>M) hi (fun _=>hM) hJ hg); change Pay _ (fun _=> boards u j L M) at he
  exact paid he (fun _ p hp x hx=> board_verify u j L M hJ hi hM hp x hx) ()
variable (ho:Odd G.count.val)
include ho hJ in
lemma brix_inv : IsUnit (cart N (tub (brix j G.count))) := by
  rw [cart_traded (cBrix _ _ ho)]; apply (pilesI _ ?_).1; intro p hp hx
  have h:= (pointed G.count p hp.1).1
  exact IsUnit.mul (isUnit_iff_exists_inv.mpr ⟨_,mul_eq_one_comm.mp h⟩) (lofty j G.count hJ ho hp)
include ho hJ in
lemma piles_conj :
  let W:=cart N (tub (brix j G.count)); let S:=plates N fun _=>sA u G.count
  W⁻¹*S + star W*(1-S)=plates N fun p=>wood u j G.count p*star (trident G.count p):=by
  intro W S; let L:=G.count
  have he(p:Momentum)(hp:p∈realCube zone): IsUnit (brix j L p):=IsUnit.mul (isUnit_iff_exists_inv.mpr ⟨_,(pointed _ _ hp.1).2⟩) (lofty j G.count hJ ho hp)
  rw [show W=plates N _ from cart_traded (cBrix j L ho) N,← (pilesI (N:=N) _ (fun p hp _=> he p hp)).2, pilesS]; unfold S; rw [← piles1, pilesP,pilesM,pilesP,pilesA]; apply pilesE; intro p hp hx; let B:=trident L p
  simp only [brix,Matrix.mul_inv_rev,wood]
  have hs : B⁻¹=star B:= Matrix.inv_eq_right_inv (pointed L p hp.1).2
  have ht:sA u L*star B=star B*sA u L:=by have hu:=congr_arg star (slateT u L p); rwa [star_mul,star_mul,slateS] at hu
  rw [returned, show star p=p from hp.1,hs, star_mul,add_mul]; change _ = _+star (stackW _ _ _)*(1-sA u L)*star B
  change ((stackW j L p)⁻¹ * star B)*sA u L + (star (stackW j L p)*star B)*(1-sA u L)= (stackW j L p)⁻¹ * sA u L * star B + star (stackW j L p)*(1-sA u L)*star B
  have hw: star B*(1-sA u L)=(1-sA u L)*star B:= by rw [mul_sub,sub_mul,one_mul,mul_one,ht]
  simp only [mul_assoc,ht,hw]
include ho hJ hg hM in
theorem sock : let H:=cart N (tub (boards u j G.count M)); let T:=cart N (tub (brix j G.count)); let S:=plates N (fun _=>sA u G.count); let P:= solo G (cart F (tub (bent u j M))); let Q:= plates N (vine u j G.count M); let K:=T⁻¹*S+star T*(1-S);
   Q*K*P*H = Q ∧ H*(Q*K*P) = P ∧ P*H=H ∧ H*Q=H ∧ H*plates N (fun _=>peb G.count)=plates N (fun p=> trident G.count p*tower u j G.count M p):=by
  intro H T S P Q K; let L:=G.count
  have he:H=plates N (boards u j L M):=cart_traded (cBoards _ _ _ _ hg hJ hM ho) N -- order check
  have hp:P=plates N (fun p=> trident L p*born u j L M p*star (trident L p)):=loop_m G _ _ (cBar j M u hg hM) ho -- edit
  let Z:=trident L
  have hk : K=plates N (fun p=>wood u j L p*star (Z p)):=piles_conj G j u hJ ho
  have hy: Q*K*P=plates N (fun p=>splitY u j L M p*star (Z p)):=by
    unfold Q; rw [hp,hk,pilesP,pilesP]; apply pilesE; intro p hc hv; simp only [← mul_assoc]; rw [mul_assoc _ (star (Z p)) (Z p), (pointed L p hc.1).1,mul_one]; rfl
  rw [hy,hp,he]; unfold Q; simp only [pilesP];
  refine ⟨pilesE _ _ ?_,pilesE _ _ ?_,pilesE _ _ ?_,pilesE _ _ ?_,pilesE _ _ ?_⟩ <;> intro p hc hv
  · unfold boards; rw [←mul_assoc,mul_assoc _ (star (Z p)),(pointed L p hc.1).1,mul_one]; exact (chase u j L M hJ ho hM hc hv).1
  · unfold boards; rw [← mul_assoc,(mul_assoc (trident L p) (clockK u j L M p)),roundabout u j L M hJ ho hM hc hv]
  · unfold boards; rw [← mul_assoc,mul_assoc _ (star (Z p)),(pointed L p hc.1).1,mul_one,mul_assoc,(chase u j L M hJ ho hM hc hv).2.2]
  · unfold boards; rw [mul_assoc,(chase u j L M hJ ho hM hc hv).2.1]
  unfold boards; rw [mul_assoc,driver u j L M hJ ho hM hc hv]
end YM.CF.Rush
