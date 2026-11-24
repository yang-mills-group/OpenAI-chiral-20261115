import YM.CF.Rush.Port
/-! Literal free open arm differences. For arbitrary unbounded dilations. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rush
open Fir Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N F:Side}(G:Ratio N F)
variable (u:Bool)(j:ℕ)(L M : Side)(hj:1≤j)(hJ:Even j)(hL:Odd G.count.val)(hM:Odd M.val)
def sweep (L:Side)(D:List Axis)(p:Momentum):Stk L:=stack L (fun l=> listChip (aliasAt p l) D • 1)
include hL in
lemma sweep_pose (D): sentry G D=plates N fun p=> trident G.count p*sweep G.count D p*star (trident G.count p):=by
  induction D with
  | nil=>
    rw [sentry,List.map_nil,List.prod_nil, ← piles1]; apply pilesE; intro p hp hx; symm
    have ht(l:Site G.count): listChip (aliasAt p l) [] • (1:Op SpinIdx)=1:=by simp [listChip]
    simp only [sweep,ht, show stack G.count (fun _=> 1)=1 from stack_one _, mul_one]; exact (pointed _ _ hp.1).2
  | cons a D ih=>
    rw [show sentry G (a::D)=(solo G (echo a)-1)*sentry G D from rfl,blaze G hL, ih,pilesP]
    apply pilesE; intro p hp hv; let Z:=trident G.count p
    simp only [← mul_assoc]; rw [mul_assoc _ (star Z), show star Z* Z=1 from (pointed _ _ hp.1).1,mul_one, mul_assoc Z (stack _ _)]
    congr 2; rw [sweep,sweep,← stack_mul]; congr 1; funext l; simp [Pi.mul_apply,Matrix.smul_mul,listChip, smul_smul]; ring
def coverlet (u:Bool)(j:ℕ)(L M:Side)(D:List Axis)(p:Momentum): Stk L:= col L (fun r=>paint u j L M r D p)
lemma coverbelt (D p): trident L p*sweep L D p*tower u j L M p=coverlet u j L M D p:=by
  rw [mul_assoc, tower,sweep,stacked]
  ext ⟨r,a⟩ ⟨l,b⟩; rw [Matrix.mul_apply, Fintype.sum_prod_type]; simp only [coverlet,c_app]
  by_cases h:l=0; swap
  · simp [h]
  simp only [if_pos h,paint,Matrix.sum_apply]; refine sum_congr rfl fun i _=>?_
  simp [toll,trident,aliasBlock, Matrix.smul_mul,ite_mul,mul_comm,mul_left_comm]; ring
-- pay at fixed L, only single column weight from summing, but definition taps don't need stock dimension.
include hJ hj hM hL in
lemma rideD (D:List Axis)(hx:D.length+2≤j):
  let R:=plates N fun _=>peb G.count; let H:=cart N (tub (boards u j G.count M));
  sentry G D*(H*R)=cart N (tub (coverlet u j G.count M D)):=by
  intro R H; let L:= G.count; let Z:=trident L
  obtain ⟨-, -,-, -, h⟩:= sock G j M u hj hJ hM hL
  have he: H*R= _ :=h
  rw [he, sweep_pose G hL,pilesP]; symm
  have hw : Reads (tub (coverlet u j L M D)) (coverlet u j L M D):=by
    have he: Pay (fun _: Unit=> Real.sqrt L.val / (L.val:ℝ)^(D.length+2)) fun _ => coverlet u j L M D:=by
      unfold coverlet; apply col_quote L; intro i; exact portrait u j (fun _=> L) (fun _=> M) (fun _=>hL) (fun _=>hM) (fun _=>i) D hx
    exact paid he (fun _ p hp x ht=>by dsimp only [coverlet]; congr 1; ext1 i; exact spans _ _ _ _ _ _ hp x ht) ()
  rw [cart_traded hw]; apply pilesE; intro p hp hx; rw [←mul_assoc,mul_assoc _ (star (Z p)), (pointed L p hp.1).1,mul_one]; exact (coverbelt ..).symm
/-- ticker entry budget, all L,M. -/
lemma pricelet {ι:Type*} (L M:ι→Side)(hl:∀ i, Odd (L i).val)(hm:∀ i,Odd (M i).val)(r:∀ i, Site (L i)) (D:List Axis)(hx:D.length+2≤j): ∃ σ C : ℝ,0<σ∧0<C∧∀ i a b,
    Width σ (C*(Real.sqrt (L i).val / ((L i).val:ℝ)^(D.length+2))) (fun x=> tub (coverlet u j (L i) (M i) D) x (r i,a) (0,b)):=by
  obtain ⟨⟨σ,C,hσ,hC,H⟩, _⟩:= tub_bill (portrait u j L M hl hm r D hx) (fun i p hp x ht=> spans _ _ _ _ _ _ hp x ht)
  refine ⟨σ,C,hσ,hC,fun i a b=> ?_⟩
  convert H i a b using 1
  ext1 x; simp only [coverlet,tub,Matrix.of_apply,c_app, if_true]
end YM.CF.Rush
