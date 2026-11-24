import YM.CF.Sour.Seal
import YM.CF.Exa.Water
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
variable {κ:Type}[TopologicalSpace κ][Nonempty κ]
-- uniform.Inf.Gen power. six arrays.A.P. smallness K−Q₀. P & V royalties. post θ ratio lead.
variable (N:Side)
abbrev BeatL (N:Side):= Raw (Chin N) (Single N)
abbrev χL (N:Side)(κ:Type):= κ→ Op SU.Slot -- fix namespace SU.
variable (T S:BeatL N)(E:χL N κ)
abbrev κR(i:κ): Op (Single N):= -(Tap.plankP N (E i))
abbrev fC(i:κ)(x:Chin N):Op (Single N):=(1-S x)*κR N E i * (1+S x)
abbrev rood (Y:χL N κ)(U:κ→ Op (Single N))(X: BeatL N)(e a:ℝ):= (a+e) -- drop
local notation "Q'"=> κR N E
local notation "K"=> fC N S E
local notation "P'"=> T
local notation "C"=> tickA N
structure Piety {κ:Type}[TopologicalSpace κ](T S:BeatL N)(E:χL N κ)(a b u v d:ℝ): Prop where
 kX :Milli d N (fun i _=>κR N E i) u a
 bend:Milli d N (fun i x=> fC N S E i x-κR N E i) v a
 loan:Milli d N (fun i x=> Sault.tally (T x) (tickA N) (fC N S E i x) (κR N E i)) u a
 pX:Milli d N (fun i x=> T x*fC N S E i x) u a
 pY:Milli d N (fun i x=>fC N S E i x*(1-T x)) u a
 pZ:Milli d N (fun i x=>T x * fC N S E i x *(1-T x)) u a
variable {a r b c ε z:ℝ} (t: Milli r N (fun i(_:Chin N)=> κR N E i) (b*z) a)(p: Solo a b T r)(s: Solo a c S r)(hs: Solo a b (fun _=>tickA N) r)(hb:0≤b)(hc:0≤c)(hp:c≤b)(hz:0≤z)(ha:0 ≤ a)(h: a≤1)
include t p s hs hb hc hp hz ha h
abbrev sprigK (b:ℝ):=4*b+4*b*b
abbrev spiritK (b:ℝ):ℝ:= b+ sprigK b*b
abbrev tundra (c:ℝ):ℝ:= 4*b*c+c
abbrev qy_K(b:ℝ):ℝ:=2*spiritK b*(Real.exp 1+b)
abbrev loan_L (b c:ℝ):ℝ:= 4*b*c+c
abbrev χr(b:ℝ):ℝ:= b+ (loan_L b (spiritK b)+ loan_L b b)+2*b*(spiritK b)+ qy_K b + 2*(b*qy_K b)
abbrev σ:= 0
lemma ours :Piety N T S E a z (χr b*z) (sprigK b*c*z) r:=by
 let F:κ→Raw (Chin N) (Single N):=fun i x=> fC N S E i x-Q' i
 let HP(B:ℝ):=Milli r N F B a
 let Z:=spiritK b; let Z':=qy_K b; let X:=loan_L b; let H:=(Real.exp 1+b); let Ψ:= (sprigK b); let L:=Z*z; let L':= b*z
 have hP:0 ≤ Z:=by unfold Z spiritK sprigK; positivity
 have hT:0≤ Z' :=by unfold Z' qy_K spiritK sprigK; positivity
 have hp₁:0≤Ψ:=by unfold Ψ sprigK; positivity
 have hχ:0≤ loan_L b b:=by unfold loan_L; positivity
 have hf:0≤ loan_L b Z:=by unfold loan_L; positivity
 have hv:HP (Ψ*c*z):=by
    have ht: (fun i x=> F i x)=fun i x=> Q' i*S x-(S x*Q' i + S x*Q' i*S x):=by funext i x; unfold F fC; simp only [sub_mul,mul_add,mul_one,one_mul]; abel
    let S':= Exa.Vista.holds (κ:=κ) s; have htP:=t.mint S' ha; have hv:=S'.mint t ha; unfold HP; change Milli r N (fun i x=>F i x) _ _; rw [ht]; apply (htP.subtract (hv.plus (hv.mint S' ha))).tall
    unfold Ψ sprigK; nlinarith only [mul_le_mul_of_nonneg_left hp (show 0≤ b*c*z from by positivity)] -- hp shadows!
 have hk: Milli r N K L a:=by 
    have hh:= (show Milli r N (fun i x=> fC N S E i x-Q' i) _ a from hv).plus t; simp only [sub_add_cancel] at hh; apply hh.tall; unfold L Z spiritK; change _ ≤ (b+Ψ*b)*z; nlinarith [mul_le_mul_of_nonneg_left hp hp₁]
 let PA:= Exa.Vista.holds (κ:=κ) p; let Q:= Exa.Vista.holds (κ:=κ) hs
 have hh:Milli r N (fun i x=> fC N S E i x*(1-T x)) (Z'*z) a:= ((hk.mint ((Exa.Vista.holds (κ:=κ) (Crown.ident ..)).subtract PA) ha).tall ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add (Real.exp_le_exp.mpr h) le_rfl) (by unfold L; positivity)) (by positivity)).trans_eq (by unfold Z' qy_K L Z; ring))) -- tune
 have hx{T':BeatL N}{V:κ→ Raw (Chin N) (Single N)}{b':ℝ}(H':0≤ b')(p:Solo a b T' r)(q: Milli r N V (b'*z) a): Milli r N (fun i x=> Sault.rise (T' x) (V i x)) (loan_L b b'*z) a:=by
    let A:=Exa.Vista.holds (κ:=κ) p
    unfold Sault.rise; refine ((((A.mint q ha).plus (q.mint A ha)).subtract q).scaleC (2:ℂ)⁻¹).tall ?_
    refine (mul_le_of_le_one_left (by positivity) (by norm_num)).trans_eq ?_; unfold loan_L; ring -- check ℂ.norm
 let J:= χr b; have he:J=b+(loan_L b Z+loan_L b b)+2*b*Z+ Z'+2*(b*Z'):=rfl
 have hz':b ≤ J:=by rw [he]; nlinarith
 have hv':loan_L b Z+loan_L b b ≤ J:=by rw [he]; nlinarith
 have hw:2*b*Z ≤ J:=by rw [he]; nlinarith
 have hu:Z' ≤ J:=by rw [he]; nlinarith
 refine ⟨t.tall (mul_le_mul_of_nonneg_right hz' hz),hv,((hx hP p hk).subtract (hx (V:=fun i _=> Q' i) hb hs t)).tall ((add_mul ..).symm.le.trans (mul_le_mul_of_nonneg_right hv' hz)),((PA.mint hk ha)).tall (le_trans (le_of_eq (show 2*(b*L)=2*b*Z*z from (by unfold L; ring))) (mul_le_mul_of_nonneg_right hw hz)),hh.tall (mul_le_mul_of_nonneg_right hu hz),?_⟩
 rw [show (fun i x=> T x*K i x*(1-T x))=(fun i x=> T x*(K i x*(1-T x))) from funext (fun i=>funext fun x=> mul_assoc ..)]; apply (PA.mint hh ha).tall; rw [←mul_assoc b,←mul_assoc]; apply mul_le_mul_of_nonneg_right _ hz; change _ ≤ J; rw [he]; nlinarith
end YM.CF.Sour
