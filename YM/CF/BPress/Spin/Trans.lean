import YM.CF.BPress.Spin.Pledges
import YM.CF.BPress.Spin.Rows
set_option linter.unusedSectionVars false
/-! Column maps on the occupied spaces. Frame potentials from determinations as in B-op. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter NormedSpace Finset Fock Branch Dial Pledge
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
namespace Trans
variable {I X D: Type}[DecidableEq I][Fintype I][Nonempty I]

def gram (P S:Op I):= star S*S+(1-P)
def pinv (P S:Op I):= (gram P S)⁻¹*star S
def beam (P S:Op I):= S*pinv P S
structure Ready (a:ℝ)(P S:Op I):Prop where
 p: IsStarProjection P
 tag: S*P=S
 pos: 0<a
 gap: a • (1:Op I)≤gram P S
variable {a:ℝ} {P Q S:Op I}
namespace Ready
variable (h: Ready a P S)
include h
lemma live_G:IsUnit (gram P S):=(Gap_inv h.pos h.gap).1
lemma boundG: ‖(gram P S)⁻¹‖≤a⁻¹:=(Gap_inv h.pos h.gap).2
lemma tagS: P*star S=star S:=by have he:= congrArg star h.tag; rwa [star_mul,h.p.isSelfAdjoint] at he
lemma surround : gram P S*P=star S*S:=by simp only [gram,add_mul,mul_assoc,h.tag,sub_mul,one_mul,h.p.isIdempotentElem.eq,sub_self,add_zero]
lemma paid : pinv P S*S=P:=by rw [pinv,mul_assoc,←h.surround, ←mul_assoc,(live h.live_G).2,one_mul]
lemma Herm : IsSelfAdjoint (gram P S):= IsSelfAdjoint.of_nonneg ((smul_nonneg h.pos.le zero_le_one).trans h.gap)
lemma reflectG: IsSelfAdjoint (gram P S)⁻¹:=by
 have hg:= congrArg star (live h.live_G).1; rw [star_mul,h.Herm,star_one] at hg
 unfold IsSelfAdjoint; calc
  _ = (star (gram P S)⁻¹*gram P S)*(gram P S)⁻¹:= by rw [mul_assoc,(live h.live_G).1,mul_one]
  _ = _:= by rw [hg,one_mul]
lemma Self: IsSelfAdjoint (beam P S):=by rw [isSelfAdjoint_iff,beam,pinv,star_mul,star_mul,star_star,h.reflectG,mul_assoc]
lemma continuousSpace: beam P S*S=S:=by rw [beam,mul_assoc,h.paid,h.tag]
lemma starP : IsStarProjection (beam P S):=⟨show beam P S*beam P S=beam P S from by nth_rw 2 [beam]; rw [←mul_assoc,h.continuousSpace]; rfl,h.Self⟩
lemma trace : (beam P S).trace=P.trace:=by rw [beam,Matrix.trace_mul_comm,h.paid]
lemma move(U:UNI I):Ready a (twist U P) (twist U S):=by
 have ht(U:UNI I): a • (1:Op I)=twist U (a • (1:Op I)):=by rw [map_smul, map_one]
 constructor
 · exact ⟨show _ * _ = _ from by rw [← map_mul,h.p.isIdempotentElem.eq],show star _ = _ from by rw [← map_star, h.p.isSelfAdjoint]⟩
 · rw [←map_mul,h.tag]
 · exact h.pos
 have hx:= twist_mono U h.gap; rw [←ht,gram,map_add,map_sub,map_one,map_mul,map_star] at hx; exact hx
lemma inv_move(U:UNI I): pinv (twist U P) (twist U S) = twist U (pinv P S):=by rw [pinv,show gram (twist U P) (twist U S)= twist U (gram P S) by simp only [gram,map_add,map_mul,map_star,map_one,map_sub],inv_turn U _ h.live_G,←map_star,←map_mul]; rfl
lemma shine (U:UNI I): beam (twist U P) (twist U S)=twist U (beam P S):=by rw [beam,h.inv_move,←map_mul]; rfl
omit h in
lemma atSelf {P:Op I}(p:IsStarProjection P): pinv P P=P∧ beam P P=P:= by
 have hx:pinv P P=P:=by rw [pinv,gram,p.isSelfAdjoint,p.isIdempotentElem.eq,add_sub_cancel]; simp
 rw [beam,hx,p.isIdempotentElem.eq]; exact ⟨rfl,rfl⟩
end Ready
-- prices
variable {C r:ℝ}
def gramPrice (P S:Pledge):= (S.times S).plus (unary.plus P)
lemma value (a:ℝ)(h:0<a)(c:0≤C)(P S:Pledge) : ∃ R:Pledge,∀ {D I X:Type}[Fintype I][Fintype X][DecidableEq I][DecidableEq X][TopologicalSpace D][Nonempty I]{b:Stage X I D Empty}{f g: Raw D I}, Capacity b C→ (∀ x, Ready a (f x) (g x))→ P.Costs b f→ S.Costs b g→ R.Costs b (fun x=>gram (f x) (g x)) ∧ R.Costs b (fun x=>(gram (f x) (g x))⁻¹) ∧ R.Costs b (fun x=>pinv (f x) (g x)) ∧ R.Costs b (fun x=> beam (f x) (g x)):=by
 obtain ⟨U,H⟩:= (gramPrice P S).invertible c h; let K:= U.times S; let Y:=S.times K; let L:=gramPrice P S; refine ⟨L.bond (U.bond (K.bond Y)),?_⟩; intro D I X _ _ _ _ _ _ b f g M B F G
 let A(x:D):=gram (f x) (g x); have hx:L.Costs b A:=Costs.plus (Costs.mul (Costs.stalk G) G) (Costs.sub Costs.one F); have ht:= H M hx (fun x=>(B x).gap); have hu : K.Costs b (fun x=>pinv (f x) (g x)) := Costs.mul ht (Costs.stalk G); exact ⟨hx.up (bond_lel ..),ht.up ((bond_lel ..).trans (bond_ler ..)),hu.up (((bond_lel ..).trans (bond_ler ..)).trans (bond_ler ..)), (Costs.mul G hu).up (((bond_ler K Y).trans (bond_ler ..)).trans (bond_ler ..))⟩ -- tune

-- explicit path parameter budget; don't assume locality for arbitrary scalar multiplier.
structure Tune {X:Type}[Fintype X][DecidableEq X] [TopologicalSpace D] (b:Stage X I D Empty)(u:D→ℝ)(C:ℝ):Prop where
 costs : ∀ x, ‖u x‖ ≤C
 pos: 0<C
 smooth: Continuous u
 parameter: ∀ S:Seal X, S.Nonempty →∀ x y, ‖u x-u y‖ ≤ C*b.eval S x y
variable [Fintype X][DecidableEq X][TopologicalSpace D]{b:Stage X I D Empty}{u:D→ℝ}
lemma genre (C:ℝ)(h:Tune b u C): (unary.scales C).Costs b (fun x=> u x • (1:Op I)):=by
 let Y (i:I) : Seal X:= {b.home i}; let c (i j:I):ℝ:=if i=j then C else 0
 let f (i j:I) (x:D):ℂ:= if i=j then ↑(u x) else 0
 have he (i j:I):Expo b (Y i) i j (c i j) (f i j):=by
    by_cases s:i=j
    · subst j; unfold c f; simp only [ite_true]; refine ⟨h.pos.le,fun _=>⟨Grove.single _, mem_singleton_self _,mem_singleton_self _⟩,fun x=>?_,fun x y=>?_,Complex.continuous_ofReal.comp h.smooth⟩; rw [Complex.norm_real]; exact h.costs _; rw [←Complex.ofReal_sub,Complex.norm_real]; exact h.parameter _ (singleton_nonempty _) x y
    unfold c f; simp only [if_neg s]; exact nothing ..
 have hg : rent (unary.scales C).rate (Y (Classical.arbitrary I))*C ≤ (unary.scales C).price:= by
    simp only [rent,Y, card_singleton,scales,mul_one,Nat.cast_one]; rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right ..) unary.bought.le -- tune
 refine funds (J:=Unit) (A:=fun i j _=>Y i) (fun i j _=>he i j) (fun i=>?_) (fun i=>?_ ) fun x i j=>?_
 · unfold c; simp [rent,Y] at hg ⊢; exact hg
 · unfold c; simp [rent,Y] at hg ⊢; exact hg
 by_cases s:i=j <;> simp [f,s,Complex.real_smul]
lemma conducts {P:Pledge}{f:Raw D I} (p:Tune b u C)(h:P.Costs b f) : ((unary.scales C).times P).Costs b (fun x=> u x • f x):= by
 have ht:= Costs.mul (genre C p) h
 simp only [Algebra.smul_mul_assoc,one_mul] at ht; exact ht
end Trans
end YM.CF.BPress.Spin
