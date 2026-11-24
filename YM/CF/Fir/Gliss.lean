import YM.CF.Fir.Cadent
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma swapsize {ι n:Type*}{f:ι→Momentum→Op n}{r:ℝ}(h:Pay (fun _=>r) f): Pay (fun _=>1) f:=by
  refine ⟨fun _=>zero_le_one,fun a b=>?_⟩; obtain ⟨η,C,hp,hC,H⟩:=h.tap a b; refine ⟨η,C*(1+|r|),hp,mul_pos hC (by positivity),fun i=>?_⟩; exact (H i).mono le_rfl (by rw [mul_one]; gcongr; grind)
variable (u:Bool)(j:ℕ)(L:Side){ι:Type*}(M:ι→Side)(hl:Odd L.val)(hm:∀ i,Odd (M i).val)(h:Even j)(he:1≤j)
include hl hm he in
lemma tower_tag : Pay (fun _:ι=>1) fun i p=> tower u j L (M i) p := by apply col_quote; intro l; exact swapsize (armPay u j he (fun _=> L) M (fun _=>hl) hm (fun _=>l))
include hl h in
lemma filter_tag: Pay (fun _:Unit=>1) fun _ p=> filterH u j L p :=by
  have hh:= (W_quote j L hl).times (Pay.const (tall u L)); simp only [one_mul] at hh
  have hx:= repay j L hl 0
  have hu:=hx.inv (moderateFirm _ hx (fun p hp H=>by have hs:=money_pos j L h hl hp; rw [H] at hs; exact lt_irrefl 0 hs)) (fun _=>one_pos)
  have hw:=((sprigPay j L hl).times ((Pay.const (peb L)).times hh)).scale hu; simp only [inv_one, one_mul] at hw
  exact hh.sub hw
include he hl hm in
lemma gate_tag : Pay (fun _:ι=>1) fun i p=> gate u j L (M i) p:=by
  apply stack_quote L; intro l; by_cases hn:l=0
  · simp_rw [if_pos hn]; exact Pay.const _
  simp_rw [if_neg hn]
  have hh:= zenBudget (fun _=>(side_pos L).le) _ (flarePay j he (fun _=>L) M (fun _=>hl) hm (fun _=>l) (fun _=>hn))
  have hs:= ((Pay.const 1).sub (swapsize hh)).times (Pay.const (angle u)); simpa only [one_mul] using hs
include he hl hm h in
lemma ticket: Pay (fun _:ι=>1) fun i p=>clockK u j L (M i) p:=by
  have ha:= tower_tag u j L M hl hm he
  have hk: Pay (fun _:ι=>1) fun i p=>grow u j L (M i) p:=by
    unfold grow spike; apply stack_quote L; intro i; by_cases he':i=0
    · simp_rw [if_pos he']; exact bent_budget u j he (fun i=>L*M i) (fun i=>hl.mul (hm i))
    simp_rw [if_neg he']; exact Pay.const _
  have hv: Pay (fun _:ι=>1) fun i p=>vine u j L (M i) p:= (Pay.const _).add hk
  have hr := ((gate_tag u j L M hl hm he).times ((filter_tag u j L hl h).reindex (fun _:ι=>())))
  have hw:=ha.times ((hk.times ((wood_quote j L hl h u).reindex (fun _:ι=>()))).times hr); simp only [one_mul] at hr hw
  have hx:= (((ha.add hr).sub hw).times hv); simp only [one_mul] at hx; exact hx
end YM.CF.Fir
