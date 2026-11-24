import YM.SU5.Selected.Cairn.Fruit
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
open Mint Lifted
namespace Giant
variable (A:Giant) {N:Side}
local notation "S" x:max=> modesIn N (park N x)
local notation "W" => A.Whistle
local notation "Π" => cutM (Tset N)
abbrev orderL := Attic.tideU A.rank+1
abbrev powerL := 2*A.orderL+2
variable (Z:A.Notes→basisRule) {T:Type}[Fintype T][DecidableEq T] (P:Society T)
def Year: Prop:= ∀ (N:Side) (u x:Site N)(s:SpinIdx)(i:A.Notes), exactU Z N u A.powerL (x,s) i≠0→s=0∧ ∃ a:ℕ,a≤ A.beams ∧ x=u-wrap N (Rail.pick a)
variable (c:A.Year Z)
include c
lemma shoreY : Contained (S A.ascY) (rootV Z (A.atPut N) A.powerL):=by
 apply (containedP ..).mpr; rintro ⟨⟨x,s⟩,j⟩ p ⟨k,i⟩; unfold rootV Screen; rw [Matrix.kronecker_apply]; by_contra t; obtain ⟨u,y,hv,z⟩:= c N (A.atPut N) x s k (left_ne_zero_of_mul t); apply p; rw [modes_at]; change node x∈park N A.ascY; rw [z,atPut,←map_sub,node_of]; exact mem_image_of_mem _ (A.ascW y hv)
lemma horn_y: Contained (S A.ascY) (Bass A Z P N A.powerL):= (shoreY A Z c).times _
omit c
variable (b:Bool)(i:A.Block)
local notation "E₀" => A.Sweet P N b
local notation "Z₀" => A.Bass Z P N A.powerL
lemma shoreX(a:Bool): Contained (S (A.Knot a)) (yoke (E₀) i a):=by
 apply (containedP ..).mpr; rintro ⟨⟨x,s⟩,t⟩ p ⟨z,d⟩; rw [sweet_l]; by_contra f; obtain ⟨_,h⟩:= exact_late W _ _ _ _ (right_ne_zero_of_mul (left_ne_zero_of_mul f)); apply p; rw [modes_at]; change node x ∈ _; rw [h,atPut,←map_add,node_of]; apply mem_image_of_mem; let v:A.Notes:= (a,i,embb P z); change A.markN (A.TourA.hilt b v).val∈ _; unfold v; cases a
 · exact A.knot_off _ rfl _
 exact A.knot_on _ rfl _
lemma shore_x : Contained (S A.ascX) (E₀):= by apply sovereign; intro i a; exact (shoreX A P b i a).grows (modes_monotone (image_subset_image (A.knot_x a)))
lemma pitchN: hand true Π* (E₀)=(E₀):=by unfold hand; rw [if_pos rfl]; unfold Sweet; rw [←Matrix.mul_assoc,spirit]
-- loft data, after d. pledge right.upper payroll. $η=d^-tid$. 
variable {M:Tulip.Male}{δ γ C:ℝ}(g:1≤C)
-- height x after boat.
def Down := (8*C:ℝ)⁻¹ -- implicit C from binder! Name φ(C)
def Up(C:ℝ):ℝ:= 8*C
def coastCap(C:ℝ):=100*C^ (2:ℕ)
lemma capCost (C)(p:1≤ C): 100 ≤ coastCap C:=by unfold coastCap; nlinarith
noncomputable def LHS (C:ℝ):= ((Up C)⁻¹:ℂ) • (E₀) -- casts meaning? Complex Inv or real? check
noncomputable def RHS (C:ℝ):= ((Up C):ℂ) • (Z₀)
noncomputable def RES (M:Tulip.Male) (C:ℝ):=(Up C:ℂ) • Horn A Z P M N A.powerL
local notation "A₀" c:max=> Up c
local notation "F"=> 1-spar 4 M (1: Pane N)
local notation "X"=> LHS A P b C (N:=N) -- syntax arg name spaces!
structure Pride (C δ γ:ℝ) (M:Tulip.Male) (N:Side):Prop where
 crop: Year A Z
 season: Loft Z A.n W A.TourA.blueprint δ γ C A.debt.val (tideU A.rank) A.orderL A.t M N
 stars: IsStarProjection (spar 4 M (1:Pane N))
variable (a:Pride A Z C δ γ M N)
local notation "Ω"=> paidX A.rank A.debt.val
local notation "R" => RES A Z P M C (N:=N)
local notation "u₀"=> marquee Z (A.atPut N) M A.powerL (park N A.Core)
lemma horns: Contained (S A.Core) (Horn A Z P M N A.powerL):= (rising _ (park N A.Core) _).times _
include a
#print Pride.mk
lemma yearly : ‖u₀‖≤ C ∧ ‖hiveX W A.n A.t (A.atPut N)‖ ≤ C ∧ ‖rootV Z (A.atPut N) A.powerL‖≤ C ∧ Π*u₀=rootV Z (A.atPut N) A.powerL ∧ ‖(hiveX W A.n A.t (A.atPut N))ᴴ*u₀-Screen (A.TourA.blueprint)‖≤ Ω ∧ ‖F*u₀‖ ≤ Ω:=by
 have t:= a.season.permit a.stars (A.atPut N) (park N A.Rad) (park N A.Core) ((A.shoreY Z a.crop).grows (modes_monotone (image_subset_image A.nut))) A.risk; obtain ⟨v,p,r,t,_,g,u⟩:= t; exact ⟨v,p,r,t,g,u⟩ -- parse parentheses F*u? notation low
lemma highPitch: Π * RES A Z P M C (N:=N)= RHS A Z P C (N:=N):=by
 unfold RES RHS Horn Bass; rw [Matrix.mul_smul, ←Matrix.mul_assoc, (yearly A Z a).2.2.2.1]
include g
lemma pays : Payroll F (X) R (1/4) (coastCap C /4) Ω (coastCap C * Ω):=by
 let H:= Horn A Z P M N A.powerL; let X':= hiveX W A.n A.t (A.atPut N); let q':= P0 A P; let b':=banquet A P b
 obtain ⟨f,v,_,he,u,t'⟩:= yearly A Z a; have ht:0<C:=zero_lt_one.trans_le g; have hp:0< Up C:=by unfold Up; positivity
 have hx: (Up C:ℂ) ≠0:=by exact_mod_cast hp.ne'
 have hv:‖H‖ ≤ C:= (portion_le _ _ (faithful A P)).trans f; constructor
 · unfold LHS; rw [norm_smul,norm_inv,Complex.norm_of_nonneg hp.le]; apply (mul_le_mul_of_nonneg_left ((charge_mul v (banquet_cost A P b)).trans_eq (mul_one _)) (inv_pos.mpr hp).le).trans; unfold Up; field_simp; linarith
 · unfold RES; rw [norm_smul,Complex.norm_of_nonneg hp.le]; apply le_trans (mul_le_mul_of_nonneg_left hv hp.le); unfold Up coastCap; nlinarith
 · unfold LHS RES; rw [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul, smul_smul,star_inv₀, show star ((Up C:ℝ):ℂ)= ((Up C:ℝ):ℂ) from Complex.conj_ofReal _, inv_mul_cancel₀ hx,one_smul]; change ‖(E₀)ᴴ* H-1‖≤ _; rw [show (E₀)ᴴ*H-1=b'ᴴ*(X'ᴴ*u₀-Screen (A.TourA.blueprint))*q' from ?_]; apply le_trans (charge_mul (charge_mul ((Matrix.l2_opNorm_conjTranspose b').trans_le (A.banquet_cost P b)) u) (mask_toll _ (A.faithful P))); simp
   unfold Sweet H Horn; rw [Matrix.mul_sub,Matrix.sub_mul,show b'ᴴ* Screen (A.TourA.blueprint)*q'= _ from A.tune_b P b]; rw [Matrix.conjTranspose_mul]; simp [H,Sweet,Horn,X',q',b',Matrix.mul_assoc] -- undo containment/unfold tune
 · unfold RES; rw [Matrix.mul_smul,norm_smul,Complex.norm_of_nonneg hp.le]; unfold Horn; rw [←Matrix.mul_assoc]; apply (mul_le_mul_of_nonneg_left ((portion_le _ _ (faithful A P)).trans t') hp.le).trans; gcongr
   unfold Up coastCap; nlinarith
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms pays
#print axioms highPitch
#print axioms shore_x
#print LHS
