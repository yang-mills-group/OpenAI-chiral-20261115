import YM.CF.Gloss.Move
import YM.CF.Gloss.Vein
import YM.CF.Skye.Can
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gloss
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire
attribute [local instance] opCStarAlgebra
variable {m B N:Side}
variable (x:Era m)
lemma setN (U V:Skin m B)(S: Support (Domain m B))(H:Agrees ↑(S.image (ψx B x)) U V):Agrees S (turnV _ x U) (turnV _ x V) :=by
 let z:=netB m B x; have hx(i): Skye.boxA z i=ψx B x i:=(ψX ..).symm
 apply Skye.flashD; rw [map_eq_image]; exact (show S.image (fun y=> Skye.boxA z y)= S.image (ψx B x) from image_congr fun i _=>hx i).symm ▸ H
lemma ξ_p(x:Era m)(B) (a:Index m): (room m B a).image (ψx B x)= room m B (ρx x a):=by ext i; obtain ⟨i,rfl⟩:= (ψx B x).surjective i; rw [matB]; simp
lemma ϕ_p(i): (faces m i).image (ρx x)= faces m (ρx x i):=by ext t; obtain ⟨k,rfl⟩:=(ρx x).surjective t; simp [faces,tx]
lemma ω_P(a:Era m) :a⁻¹.charge=a.charge ∧wageZ a⁻¹=wageZ a:=by
 refine ⟨rfl,?_⟩; have he:wageZ (1:Era m)= (wageZ a).xor (wageZ a⁻¹):=by nth_rw 1 [←mul_inv_cancel a]; unfold wageZ; change (a.charge.xor (a⁻¹.charge)).xor (detX (a.s*a⁻¹.s))=_; rw [det_p]; simp [Bool.xor_comm,Bool.xor_assoc,Bool.xor_left_comm]
 have hs:wageZ (1:Era m)=false:=by unfold wageZ; change false.xor (detX 1)=_; rw [det_i]; rfl
 rw [hs] at he; grind
lemma pay_u (a:Era m)(x:ℂ) : payZ a (payZ a x)=x:=by unfold payZ; rw [sign_seq,Bool.xor_self]; rfl
abbrev costG(m B: Side):= Era m × Stamp m B
def mot(x:Era m)(a:costG m B):costG m B:=(x⁻¹*a.1,a.2)
abbrev eQ(B:Side)(x:Era m):Equiv.Perm (costG m B):=(Equiv.mulLeft x⁻¹).prodCongr (Equiv.refl _)
local notation "uM"=> Fintype.card (Era m)
def rip(m:Side):ℝ:= (Fintype.card (Era m):ℝ)⁻¹
def workQ(a:costG m B)(f:Pack m B→ℂ)(U:Pack m B):ℂ:= rip m • payZ a.1 (f (vest B a.1 U))
def billP {v:Part m B} (Q:Scroll m B v)(a:costG m B):=workQ a (Q.term a.2)
def target(a: costG m B):= ρx a.1 (pinpoint m B a.2)
def cabinQ {c:Part m B}(W:Scroll m B c)(U:Pack m B):= ∑ i: costG m B,billP W i U
def seedQ {v:Part m B} (Q:Scroll m B v)(a:costG m B): Pack m B → ℂ:=workQ a (Q.leftover a.2)
variable {v:Part m B}(W: Scroll m B v)(i:costG m B)(U: Pack m B)
lemma pay_s (r:ℝ)(z:ℂ): payZ x (r • z)=r • payZ x z:=by unfold payZ; cases wageZ x <;>simp [cSignX]
lemma pay_a (z y:ℂ): payZ x (z+y)=payZ x z + payZ x y:=by unfold payZ; cases wageZ x <;>simp [cSignX]
lemma pay_m {I:Type}[DecidableEq I](V:Finset I)(f:I→ℂ):payZ x (∑ i∈ V,f i)=∑ i∈V,payZ x (f i):=by unfold payZ; cases wageZ x <;> simp [cSignX,star_sum]
lemma pay_t (a:Era m)(b:ℂ):‖payZ a b‖=‖b‖:=by unfold payZ; cases wageZ a<;> simp [cSignX]
lemma ch_h(A:Pack m B→ℂ): workQ (mot x i) A (vest B x U)=payZ x (workQ i A U):=by
 unfold workQ; simp only [mot,bake,mul_inv_cancel_left,pay_s]; apply congrArg; set f:=A _; rw [←warX x⁻¹ i.1]; unfold payZ; rw [(ω_P x).2]
lemma moot: target (mot x i)=ρx x⁻¹ (target i):=by unfold target mot; dsimp only; rw [ρXp]
lemma bill_s: billP W (mot x i) (vest B x U)=payZ x (billP W i U):= ch_h ..
lemma kilo_o(x:Era m):Continuous (payZ x):=by unfold payZ; cases wageZ x; exact continuous_id; exact continuous_star
lemma vest_p:Continuous (vest B x):=(show Continuous (fun U:Pack m B=> flashA (netB m B x) U.1) from (Skye.revM _).comp continuous_fst).prodMk ((ctS _).comp continuous_snd)
lemma pure: cabinQ W (vest B x U)=payZ x (cabinQ W U):=by unfold cabinQ; rw [←Equiv.sum_comp (eQ B x) (fun j=>billP W j (vest B x U)),pay_m]; exact sum_congr rfl fun i _=> bill_s ..
end YM.CF.Gloss
