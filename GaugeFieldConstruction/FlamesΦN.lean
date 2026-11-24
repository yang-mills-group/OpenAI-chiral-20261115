import GaugeFieldConstruction.BlessedN
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.GaugeFieldConstruction.Flavor
open CF Matrix
open Finset
open scoped BigOperators Matrix Classical
open Matter
/-- finite phase hand for exact regulator assignment costs -/
def CompassN : Subgroup Flavor where
 carrier:=setOf (fun g:Flavor=>∀ b:Bool,∀ i:Generation,leg (g b) i=i)
 one_mem':=fun b i=>leg_one i
 mul_mem':=fun {a b} h p i j=> (leg_mul (a i) (b i) j).trans ((congrArg (leg (a i)) (p i j)).trans (h i j)) -- motive backward tune
 inv_mem':=fun {a} h i j=> (show leg (a i)⁻¹ j=leg 1 j from by rw [← inv_mul_cancel (a i),leg_mul,h i j]).trans (leg_one j)
local notation "ΦΓ"=> ↥CompassN
noncomputable instance : Fintype ΦΓ:= Fintype.ofFinite _
abbrev βbitN(g:ΦΓ)(i: FlavorIndex): Bool:= bit g.val i
abbrev βChiN(g:ΦΓ)(i: FlavorIndex):ℂ:=pay (βbitN g i) 1
abbrev hueBitN(g:ΦΓ)(i j:Bool × Generation):Bool:=(mark (g.val i.1) i.2)^^(mark (g.val j.1) j.2) -- tune
abbrev hueChiN(g:ΦΓ)(i j:Bool × Generation):ℂ:=pay (hueBitN g i j) 1
lemma streetN(g:ΦΓ)(i:Slot): sensor g.val i=i:=by unfold sensor; rw[g.property]
lemma chaseN(g:ΦΓ)(i:FlavorIndex): reprice g.val i=i:=by unfold reprice; rw [g.property,g.property]
lemma βMultipN (g h:ΦΓ)(i:FlavorIndex) : βChiN (g*h) i=βChiN g i*βChiN h i:=by
 unfold βChiN βbitN; rw [Subgroup.coe_mul,bit_mul,chaseN]; cases bit g.val i <;> cases bit h.val i<;>simp
lemma hueMultiN (g h:ΦΓ)(i j:Bool×Generation): hueChiN (g*h) i j=hueChiN g i j*hueChiN h i j:=by
 simp only [hueChiN,hueBitN,Subgroup.coe_mul,Pi.mul_apply,mark_mul,h.property i.1 i.2,h.property j.1 j.2]; cases mark (g.val i.1) i.2<;>cases mark (g.val j.1) j.2<;>cases mark (h.val i.1) i.2<;>cases mark (h.val j.1) j.2<;>simp
lemma peN(g:ΦΓ)(x: FlavorIndex): βChiN g x * βChiN g x=1:=by unfold βChiN; cases βbitN g x<;>simp
lemma weddingN(g:ΦΓ)(x:FlavorIndex)(y:Bool)(b:βbitN g x≠ y):βChiN g x * pay y (1:ℂ)= -1:=by unfold βChiN; revert b; cases βbitN g x<;> cases y<;>simp
lemma twiceBN (i j:Generation) : Signed.mirror i.castSucc * Signed.mirror j.castSucc∈ proper3:=by
 refine ⟨rfl,?_,by simp [signBit_mul]⟩
 simp only [Signed.mul_flip,Signed.mirror,Equiv.refl_apply,timeAxis]
 simp [show i.castSucc ≠  (3:Axis) from Fin.castSucc_ne_last i,show j.castSucc≠  (3:Axis) from Fin.castSucc_ne_last j] -- tune
abbrev duelN(i j: Generation) : proper3:= ⟨_,twiceBN i j⟩
def chooseN(b:Bool)(i j:Generation):ΦΓ:=⟨fun W=> if W=b then duelN i j else 1,fun W k=>by dsimp only; split_ifs; exact Fin.castSucc_inj.mp (cast_leg ..); exact leg_one k⟩
abbrev hueTabN(W:Bool)(i j k:Generation)(X:Bool):Bool:=if X=W then decide (k=i)^^ decide (k=j) else false
lemma paysBN (W b:Bool)(i j k:Generation): mark ((chooseN b i j).val W) k=hueTabN b i j k W:=by
 unfold hueTabN chooseN; dsimp only; split_ifs
 · simp [mark,Signed.mirror,eq_comm]
 exact mark_one k
abbrev CupidN(x:FlavorIndex)(i j:Bool×Generation): Prop:= i=(x.1,x.2.1)∧j=(x.1,x.2.2)∨i=(x.1,x.2.2)∧ j=(x.1,x.2.1)
set_option maxHeartbeats 420000 in
lemma judgeN :∀ W:Bool,∀ a b: Fin 3,a ≠ b→∀ (i j: Bool× Fin 3),(∀ G:Bool,∀ k l:Fin 3, ((hueTabN G k l a W) ^^ hueTabN G k l b W) = ((hueTabN G k l i.2 i.1) ^^ hueTabN G k l j.2 j.1)) → i=(W,a)∧j=(W,b)∨i=(W,b)∧j=(W,a):=by decide -- tune cost
lemma vigorN{x:FlavorIndex}{i j:Bool×Generation}(v:x.2.1≠x.2.2)(q:∀ g:ΦΓ,βbitN g x=hueBitN g i j): CupidN x i j:=by
 apply judgeN x.1 _ _ v; intro G k l; specialize q (chooseN G k l); unfold βbitN hueBitN bit at q; simp only [paysBN] at q; exact q
-- avoid character orthogonality systemic steps
lemma listN(C:ΦΓ→ℂ)(p:∀ g h,C (g*h)=C g*C h)(v:∃ g,C g≠1):∑ i:ΦΓ,C i=0:=by
 obtain ⟨g,q⟩:=v; by_contra! h; apply q; refine mul_right_cancel₀ h ?_; rw[mul_sum,one_mul]; simp_rw [←p]; exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun i=>rfl
lemma vaneN(x:FlavorIndex)(u:x.2.1≠x.2.2):∑ i:ΦΓ,βChiN i x=0:=by
 have v:¬ ∀ g:ΦΓ,βbitN g x=hueBitN g (x.1,x.2.1) (x.1,x.2.1):=fun h=> by have he:=vigorN u h; simp [CupidN,u] at he
 push Not at v; obtain ⟨i,g⟩:=v
 apply listN _ (fun i j=> βMultipN i j x); refine ⟨i,?_⟩; change pay _ _≠_; unfold hueBitN at g; simp only [Bool.xor_self,Bool.not_eq_false] at g; rw [g]; norm_num
lemma ClaraN(x:FlavorIndex)(u:x.2.1≠x.2.2)(i j:Bool × Generation)(k:¬ CupidN x i j): ∑ g:ΦΓ,βChiN g x*hueChiN g i j=0:=by
 have hp:¬∀ g:ΦΓ,βbitN g x=hueBitN g i j:=mt (vigorN u) k; push Not at hp; obtain ⟨g,h⟩:=hp
 refine listN _ (fun i' j'=> by simp only [βMultipN,hueMultiN]; ring) ⟨g,?_⟩
 rw [show βChiN g x*hueChiN g i j= _ from weddingN _ _ _ h]; norm_num
#print axioms ClaraN
end YM.GaugeFieldConstruction.Flavor
end
