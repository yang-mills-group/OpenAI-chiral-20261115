import Gingham.Ruff.Pike
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset RG Cube
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical
open Skye Scree
local notation "γ"=>SU.group
open Jet Rill Sour Lat Tulip
variable {N:Side}


open Drapes Fock Peaks Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

open Shells Fan
variable {n:ℕ}{a c e ρ b:ℝ} (X:Rialto n e ρ b)
    {A:Fob N e}
   {y:Site N}{u:Side}
variable (B:Plastron y u e (a/4) c A)
variable {l r:ℕ}{E:ℝ}{p: BudgetPoint}
  (G:Tagbill a E u l r p.B)
  (P: Parasols p ρ (p.B/10))

variable {U:Pane N} (g:Pinwax p (bouton y) (p.B/10) U)
variable {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y]


-- inked query shape for arbitrary Y.
def pitch (y:Site N)(p:BudgetPoint)(U:Pane N)
     (V:Y→Pane N)(T:Y→L[ℝ]tangD N):Prop:= ‖T‖≤1∧
    (∀ᶠ i in 𝓝 0, Agrees (belle y p.B)
            (increment U (p.threshold • T i)) (V i))

def devour (ρ:ℝ)(u:Side)(a c:ℝ):ℝ:= Interest u (a/4) c 2*(8/ρ)^2

/- Aggregate, no b loss: even before constant payment, all orders.
   Pitch uses agreement on belle (can weaken to active key union when needed). -/
include X B G P g


lemma hath (j:2≤n) 
   (V:Y→Pane N)(Z:Y→Tune N e)
   (q:∀ᶠ i in 𝓝 0,(Z i).val=Tulip.profile (V i))(T:Y→L[ℝ]tangD N)
   (d:pitch y p U V T):
   let L:=B.light (tenderb p.B)
   Allows n (fun i=>(L (Z i)).trace - hum X L 0) 0
      (devour ρ u a c*p.threshold^2):=by
 intro L
 let F:=tagLite (b:=p.B) B
 let v:= (8/ρ)*p.threshold
 have z:0≤v:=(mul_nonneg (div_nonneg (by norm_num) P.pos.le) p.threshold_pos.le)
 have vv: Interest u (a/4) (1*c) 2*v^2=devour ρ u a c*p.threshold^2:=by
   rw [one_mul,show v=(8/ρ)*p.threshold from rfl,mul_pow,←mul_assoc];rfl
 simp_rw [hum, show L=B.light (tenderb p.B) from rfl,aria_kernel X F,←sum_sub_distrib]
 apply Allows.mono _ ((tribute F u (show 0<a/4 from div_pos G.apos (by norm_num)) z 2).trans_eq vv)
 refine allows_sum fun S _=>?_
 -- dsimp
 by_cases t: blush (F.cost S)=0
 · simp only [blood,t,hush X F S t,sub_zero,zero_mul]
   exact allows_const 0 (by simp)




 obtain ⟨c0,h0⟩:=apple_positive F S t
 let m:= widthL u + 5*S.card
 have e0: m≤p.B/10:=by
   unfold tenderb at h0;have :=G.largeB;unfold m;omega
 have m0: liltCost p ρ m = v*walk u S.card:=by
   change p.threshold*(8*(1+(m:ℝ)))/ρ=v*(1+(m:ℝ))
   unfold v;ring
 unfold blood;rw [←m0]
 exact tty X (F.pass S) P j e0 c0 Z
   ⟨g,T,V,d.1,q,d.2.mono fun i h c a b=>
      h c (girder_i G S c0 h0 a) (girder_i G S c0 h0 b)⟩

#print axioms hath


open Pike
def fairy (a:ℝ)(b:ℕ):ℝ:=Real.exp (-a*(b:ℝ)/3200)
omit X P g in
lemma fairy_rich : waist a c (tenderb p.B)≤fairy a p.B*c:=by
 have s:= G.largeB
 have t:(p.B:ℝ)≤400*(tenderb p.B:ℝ):=by exact_mod_cast show p.B≤400*tenderb p.B by unfold tenderb;omega
 exact mul_le_mul_of_nonneg_right
    (Real.exp_monotone (show -(a/4-a/8)*(↑(tenderb p.B):ℝ) ≤ -a*(p.B:ℝ)/3200 by
      nlinarith [mul_le_mul_of_nonneg_left t G.apos.le])) (carrot_c B)

/-- Down payment, whenever full trace vanishes at 0. -/
lemma chorus (j:2≤n) (h:hum X A 0=0)
   (V:Y→Pane N)(Z:Y→Tune N e)
   (q:∀ᶠ i in 𝓝 0,(Z i).val=Tulip.profile (V i))(T:Y→L[ℝ]tangD N)
   (d:pitch y p U V T):
   let L:=B.light (tenderb p.B)
   Allows n (fun i=>(L (Z i)).trace) 0
      (devour ρ u a c*p.threshold^2 + fairy a p.B*c):=by
 intro L


 let B₂:=B.flightP (tenderb p.B) (show a/8≤a/4 by linarith [G.apos])
 have z:‖hum X L 0‖≤fairy a p.B*c:=by
   unfold hum at *
   rw [B.split_m (tenderb p.B) (pate X 0),Matrix.trace_add,add_eq_zero_iff_eq_neg] at h
   rw [show L=B.light (tenderb p.B) from rfl,h,norm_neg]
   exact ((sing X B₂ (show 0≤a/8 from div_nonneg G.apos.le (by norm_num))) 0 (by simp)).value.trans
     (fairy_rich B G)
 exact ((hath X B G P g j V Z q T d).add (allows_const _ z)).germ
   (Eventually.of_forall fun i=>sub_add_cancel ..)

