import YM.SU5.Reconstruction.Crease.Reservoir
import YM.SU5.Reconstruction.Crease.Thicket
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Picket CrossedFrame Anvil OS Semigroup Real
open scoped BigOperators Topology InnerProductSpace ComplexOrder
variable {H K D:Hilbert}(C:Clasp K H D)
variable {a b: Axis}(r:b≠a) (S:OS.Semigroup H a)
variable (u t:ℝ)
def stern (a b:Axis)(u t:ℝ): E4:= Picket.move a b u (t • basis b)
local notation "y₀"=> stern a b u t
include r
lemma stern_p (h: 0<t): Scope a b (stern a b u t):= by
 unfold Scope stern; rw [eye_high r,eye_low r]; simp only [PiLp.smul_apply, show basis b b=1 from (by simp),show basis b a=0 from (by simp [r.symm]), smul_eq_mul]; ring_nf -- careful abs? simp
 have he:sinh u < cosh u:=by rw [sinh_eq, cosh_eq]; linarith [Real.exp_pos (-u)]
 have hv: -(sinh u)<cosh u:= by rw [sinh_eq,cosh_eq]; linarith [Real.exp_pos u]
 -- trace for norm
 apply abs_lt.mpr; constructor<;> nlinarith
lemma stern_opp : turn a b y₀= -y₀:= by
 ext1 i; rw [turn_at]; split_ifs with h; rfl
 replace h : i≠a ∧ i≠b:= not_or.mp h; unfold stern; rw [PiLp.neg_apply,others _ _ _ h.1 h.2]; simp [h.2]
local notation "P"=> C.plume
local notation "R"=> C.shadow
local notation "q"=> Picket.trans S (t • basis b)
local notation "U"=> Picket.boost C u
omit r in
lemma conducts (y:H) : P (Picket.boost C u y)=Picket.boost C u (P y)∧ R (Picket.boost C u y)=Picket.boost C u (R y):= by
 have ht:P (Picket.boost C u y)=U (P y):= DFunLike.congr_fun (C.transBeat u) y
 refine ⟨ht,?_⟩; change _- (P _) = U ( y- (P _)); rw [ht,map_sub]; rfl -- `_`
lemma courseGram (B:D.Op)(e:C.Pass q B)(v:IsSelfAdjoint B)(k:∀ x,U* trans S x= trans S (Picket.move a b u x)*U)(x y:H)(p:P y=R x) : P (Picket.trans S (-y₀) y)=R (Picket.trans S y₀ x):= by
 let V:= Picket.boost C (-u); let pC:= t • basis b; let V₁:= Picket.trans S (-pC)
 let M(x:E4):= Picket.move a b u x
 have hh : M (-pC)= - y₀:=by
     ext1 k; by_cases h:k=a ∨ k=b
     · rcases h with h|h <;> subst k<;> unfold M stern<;> simp only [PiLp.neg_apply,eye_high r,eye_low r]; all_goals ring
     have h':= not_or.mp h; unfold M stern; rw [others _ _ _ h'.1 h'.2, PiLp.neg_apply, PiLp.neg_apply,others _ _ _ h'.1 h'.2]
 have ht(w:E4): Picket.trans S (M w)= U*Picket.trans S w* V:=by rw [k,mul_assoc, show boost C u * V = boost C (u+ -u) from boost_thru C u (-u),add_neg_cancel, boost_first,mul_one]
 rw [← hh, show y₀=M pC from rfl,ht,ht]
 have hx:P (V y)= R (V x):= by rw [(conducts C (-u) _).1,(conducts C (-u) _).2,p]; -- r omitted
 have hq:= C.momentum q V₁ B e v (trans_star S (t • basis b)).symm (V x) (V y) hx
 simp only [mul_apply_eq_comp,(conducts C u _).1, (conducts C u _).2]; rw [hq]
end YM.BridgeClub
