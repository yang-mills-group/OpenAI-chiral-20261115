import Organdy.Hyssop
import YM.SU5.Exchange.Pilot.Bundle
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Tulip Lat Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive  Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU
variable (s:Sweep n)
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single n
local notation "Fz"=> FC (Dwell n)


local notation "Z"=>moldA s
local notation "E"=>exportQ s
lemma whirl_App (V:Bag n)(X:Aura n):whirlB s V (Z X)=E (V X):=by
   change E (V ((moldA s).symm (Z X)))=_; rw [Equiv.symm_apply_apply]
lemma whirl_α (X Y:Aura n):
    Z (Leaf.αK X Y)= Leaf.αK (Z X) (Z Y):=
    Subtype.ext (Finset.map_union ..)

lemma whirl_cPair (X Y:Bag n):
    whirlB s (regionW X Y)=regionW (whirlB s X) (whirlB s Y):=by
  funext W; obtain ⟨A,rfl⟩:=(Z).surjective W
  rw [whirl_App,regionW];unfold regionW Leaf.Ktw
  rw [map_sum]; refine sum_equiv Z (by simp) fun i _=>?_
  rw [map_sum]
  have hx(j:Aura n):j ∈ Cadre.blaze i ↔ Z j∈Cadre.blaze (Z i):=by
    simp only [mem_filter,mem_univ,true_and,Cadre.blaze]
    exact not_congr (Finset.disjoint_map _).symm

  refine sum_equiv Z hx fun j _=>?_
  have ht : Z A=Leaf.αK (Z i) (Z j) ↔ A=Leaf.αK i j := by
    rw [←whirl_α];exact (Z).injective.eq_iff
  by_cases v:A=Leaf.αK i j
  · rw [if_pos v,if_pos (ht.mpr v)]
    dsimp only; unfold cBump
    rw [whirl_App,whirl_App,map_sub,map_mul,map_mul]
  rw [if_neg v,if_neg (mt ht.mp v),map_zero]

local notation "Hz"=> Scree.Hub n
lemma hubEq_inj : Injective (moveHub s):=by
 intro i j h; apply Subtype.ext
 have ht:=congrArg Subtype.val h
 refine Prod.ext ((boxA s).symm.injective (congr_arg Prod.fst ht)) ?_
 exact Finset.map_injective (boxA s).symm.toEmbedding (congrArg Prod.snd ht)
abbrev whirl_H := Equiv.ofBijective (moveHub s) ⟨hubEq_inj s,Finite.surjective_of_injective (hubEq_inj s)⟩

variable {F:RegBudget n}
lemma whirl_L (u:IncX (fun _=>True) F p h a)(i:Hz)(z:Pane n):
    head_L F (moveHub s i) (flashA s z)=suit_Y s (head_L F i z):=by
 have k:=u.face s trivial _ (spinZ ..) i z
 exact (congrArg blind_E k).trans (sanct_E ..)

lemma whirlWeft (u:IncX (fun _=>True) F p h a)(i:Hz):
    E (wetPC p i (head_L F i))=wetPC p (moveHub s i) (head_L F (moveHub s i)):=by
  funext z
  let x:=flashA s⁻¹ z.1
  let y:=(moveHub s i).val.2
  have g :flashA s x=z.1:=by rw [show x=_ from (rfl:x=flashA s⁻¹ _),lights,inv_mul_cancel,rev1]
  have f:=Salt.glowA p.threshold i.val.2 s x -- tune
  change roll s (numbE p.threshold i.val.2 _ x).val=(numbE p.threshold y _ z.1).val
  -- rw ←g affects x? x now constant
  nth_rw 1 [←g]
  suffices k : numbE p.threshold y (head_L F (moveHub s i)) (flashA s x)=suit_Y s (numbE p.threshold i.val.2 (head_L F i) x) from congrArg Subtype.val k.symm
  unfold numbE
  by_cases l:pingS p.threshold i.val.2 x
  · rw [Set.indicator_of_mem (show flashA s x∈_ from f.mpr l),Set.indicator_of_mem (show x∈_ from l)]
    exact whirl_L s u i x
  rw [Set.indicator_of_notMem (show flashA s x∉_ from mt f.mp l),Set.indicator_of_notMem (show x∉_ from l),map_zero]

lemma whirlScald (u:IncX (fun _=>True) F p h a):
  whirlB s (scald p (head_L F))=scald p (head_L F):=by
  funext W
  obtain ⟨A,rfl⟩:=(Z).surjective W
  rw [whirl_App]
  unfold scald;rw [map_sum]
  refine sum_equiv (whirl_H s) (by simp) fun i _=>?_
  let g(i:Hz):Aura n:= ⟨i.val.2,i.val.1,i.property⟩
  have e: Z A=g (whirl_H s i) ↔ A=g i :=by
     change Z A=Z (g i)↔_
     exact (Z).injective.eq_iff
  change E (if A=g i then _ else _)=if Z A=g (whirl_H s i) then _ else _
  by_cases t:A=g i
  · rw [if_pos t,if_pos (e.mpr t)]; exact whirlWeft s u i
  rw [if_neg t,if_neg (mt e.mp t),map_zero]
lemma whirlTailor (u:IncX (fun _=>True) F p h a)(V:Bag n):
   whirlB s (tailor p F V)=tailor p F (whirlB s V):=by
  have w:cirrhose s (2:ℂ)⁻¹=(2:ℂ)⁻¹:=by unfold cirrhose cSignX; split <;> simp
  unfold tailor;dsimp only
  rw [map_add,map_add,whirl_cPair,whirlV,w,whirl_cPair,whirl_cPair,whirlScald s u]

variable {d₁ r z:ℝ}
lemma Glare.tailors {A : Support (More n)}{V:Bag n}
    (hF:IncX (fun _=>True) F p h z)
    (u:Glare p q A h V (r+d₁+d₁) a b)
    (i:Sectoral p q (scald p (head_L F)) h (r+d₁) c) (hx:0≤r)(w:0<d₁) :
    let T₀:=2*(spanV p.B*d₁⁻¹*a*c)
    let Δ:=T₀+(2:ℝ)⁻¹*(2*(spanV p.B*d₁⁻¹*T₀*c))
    Glare p q A h (tailor p F V) r (a+Δ) (b+Δ):=by
  intro T₀ Δ
  refine ⟨tailor_price p u.toBarrage i hx w,fun s=>?_⟩
  rw [whirlTailor s hF]
  let l:=uplift p.order
  let y:=2*(spanV p.B*d₁⁻¹*(l*a)*c)
  let R:= y+(2:ℝ)⁻¹*(2*(spanV p.B*d₁⁻¹*y*c))
  rw [mul_add,mul_add _ b,show uplift p.order * Δ=R from (by unfold Δ R T₀ y l;ring)]
  exact tailor_price p (u.also s) i hx w
end YM.CF.Organdy
