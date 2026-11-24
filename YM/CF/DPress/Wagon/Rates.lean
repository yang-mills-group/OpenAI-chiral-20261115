import YM.CF.DPress.Wagon.Pairing
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
namespace Race.Ribbon
variable {T:Race n L}(X:Ribbon T){b c:Bool}{n0 k:ℕ}(p: X.Frame k)
open Credit
local notation "P"=> X.stripe p
variable {a:ℤ}{x y:ℝ}
abbrev ρ (p:0<x)(q:0<y): Reward T X.full := ⟨fun b=> if b then y^X.P else x^X.P,(by intro b; split<;> positivity)⟩
def growth (X:Ribbon T)(x y:ℝ)(k:ℕ):= x^(X.mulT k)*y^(X.runB k)
def rent (v:0<x)(w:0<y): Reward T (X.stripe p):= ⟨fun _=>X.growth x y k,(fun _=>(by unfold growth; positivity))⟩
lemma rent_U (i:Reward T X.full) (a b:ℤ) : 0≤ i.cost []:= (i.cost_p []).le
lemma rent_p (v:0<x)(w:0<y) (Y:List Bool) : (X.rent p v w).cost Y=(X.growth x y k)^Y.length:= by induction Y with|nil=> simp [rent,growth,Reward.cost]| cons i Y ih=> rw [List.length_cons,pow_succ',←ih]; rfl
variable (L0: X.mulT k=X.P)(v:0<x)(w:0<y)
lemma billing (i:ℕ)(s:ℝ)(p0: 1 ≤ s):s^i≥ 1:= one_le_pow₀ p0
private lemma muG (U:ℝ) : (U^X.P)^k=U^X.runB k:=by rw [← pow_mul]; rw [runB,mul_comm X.P]
include L0 v w
-- At the terminal dyadic interval, no further reflection of the stripes needed to re-tile by P.
lemma term_one {V:Fixed.Test n} (h:(X.stripe p).part a b c V)(f:Bool):∃ S: List Bool, S.length=k+1 ∧ Credit X.full a f S V ∧ (X.ρ v w).cost S=X.growth x y k:=by
 by_cases i:c=b
 · subst c; let K:=List.replicate k true; let f':= X.arc_c (X.straightL p h) f; let Z:= (f'.companion (Credit.unitP X.full _ _ [false])); refine ⟨K++[false],(by simp [K]),mul_one V ▸ Z,?_⟩; exact show ((X.ρ v w).cost (K++[false]))=_ by
    rw [Reward.adds, show K= _ from Eq.refl (List.replicate k true),Reward.constant]; change (y^X.P)^k*(x^X.P*1)=_; rw [muG X,growth,L0,mul_one,mul_comm]
 have l:c=!b:=by cases b<;>cases c<;>simp_all
 subst c; refine ⟨false::List.replicate k true,(by simp),?_ ,?_⟩
 · rw [←one_mul V]; apply Credit.next (X.full.seed a f false); have he := X.straightR p h; apply X.arc_c; rw [L0] at he; exact he
 rw [show false::List.replicate k true =[false]++List.replicate k true from rfl,Reward.adds,Reward.constant]; change x^X.P*1*(y^X.P)^k=_; rw [muG X,mul_one,growth,L0]
lemma terminal (i:List Bool)(t:Bool){V:Fixed.Test n}(h:Credit (P) a b i V) :∃ a':List Bool,a'.length=(k+1)*i.length ∧ Credit X.full a t a' V∧ (X.ρ v w).cost a'=(X.growth x y k)^i.length:=by
 induction h generalizing t with
 | zero a b=> exact ⟨[],(by simp),Credit.zero _ _,by simp [Reward.cost]⟩
 | @next a b j V W i h t' IH=>
    obtain ⟨s,l,u,H⟩:=X.term_one p L0 v w h t; obtain ⟨e,m,he,hz⟩:= IH (turned s.length t); refine ⟨s++e,(by simp [l,m]; ring),u.companion ?_,?_⟩
    · rw [blockP,l]; change Credit _ (a+ (( ((k+1)*X.P:ℕ)):ℤ)) _ _ _; rw [show (k+1)*X.P= (X.stripe p).w by change _=X.runB k+X.mulT k; rw [L0,add_mul,one_mul]]; exact X.αturn he _
    rw [Reward.adds,H,hz,List.length_cons,pow_succ']
end Race.Ribbon
end YM.CF.DPress.Wagon
