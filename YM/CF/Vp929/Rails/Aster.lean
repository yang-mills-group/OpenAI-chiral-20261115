import YM.CF.Yaw.Lotus
import YM.CF.Yaw.Year
import YM.CF.Yaw.Trust
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Yaw
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
open Scion PetalP
open scoped Classical
variable {ι A n M:Type}[Fintype ι][DecidableEq ι][Fintype A][DecidableEq A][LinearOrder n][Fintype n][LinearOrder M][Fintype M]
local notation "K"=> LeanV M
local notation "H₀"=> Crowd A
open Push.AbsoluteSums Push.AbsoluteSums.Trees Push.AbsoluteSums.Footprint RG
variable (X:ι→leaf A)(B:Raid (LeanV M))(Q:Urn.Twig n→ Track (Crowd A) ℝ)(U:ι→ PetalP (LeanV n))(L:ι→ PetalP (Oboe n))(W:ι→Raid (LeanV M))
lemma scale_dawn (C:ι→ℝ): dawnT X B Q U L (fun i=> C i • W i)=fun i=> C i • dawnT X B Q U L W i := by
 funext i; unfold dawnT beamZ; rw [crank_C,show Pi.single _ (joinV B (C i • _)) = C i • Pi.single (beamH (X i).val) (joinV B (W i)) from ?_,ray_p,crank_C]; funext j; rw [Pi.smul_apply]; simp only [Pi.single_apply]; split; · simp [joinV,mul_sum,mul_left_comm]
 rw [smul_zero]
lemma sum_dawn {I:Type}[Fintype I](W:I→ι→Raid K): dawnT X B Q U L (fun i=>∑ j:I,W j i)=∑ j,dawnT X B Q U L (W j) := by
 funext i; rw [Finset.sum_apply]; unfold dawnT beamZ; rw [crank_C,show (Pi.single (beamH (X i).val) (joinV B (∑ j:I,W j i)):Stilo.Track (Crowd A) ℝ) = ∑ j:I, Pi.single (beamH (X i).val) (joinV B (W j i)) from ?_,ray_s]; exact Finset.sum_congr rfl fun j _=>crank_C ..; rw [joinVsum]; funext j; rw [Finset.sum_apply]; by_cases b:j=beamH (X i).val<;>simp [Pi.single_apply,b]
lemma pay_cost (C:ι→ℝ)(R:ι→Track H₀ ℝ)(r:List ι): payH (fun i=> C i • R i) r=(r.map C).prod • payH R r:=by
 induction r with
 | nil=> rw [List.map_nil,List.prod_nil,one_smul]; rfl
 | cons i l ih=> rw [List.map_cons,List.prod_cons,mul_smul,show payH (fun i=> C i • R i) (i::l)=crank (C i • R i) (payH (fun i=> C i • R i) l) from rfl,ih,ray_p, crank_C,ray_p,crank_C (R i)]; rfl
lemma pay_dawn_price (C:ι→ℝ)(r:List ι): payH (dawnT X B Q U L (fun i=> C i • W i)) r=(r.map C).prod • payH (dawnT X B Q U L W) r := by rw [scale_dawn,pay_cost]
local notation "μ"=> Push.AbsoluteSums.Trees.currency
variable {V:Side}
/-- Pay for multiplying a rail by exponential of mandatory-support coverNumber. -/
lemma Strung.advance{X:Support V}{F:Track (Harper (Site V)) ℝ}{a γ:ℝ}{D:ℕ}(p:Strung X F D a γ){δ:ℝ}(h:0≤δ): Strung X (μ D δ X • F) D (a-δ) γ:= by
 refine ⟨smul_nonneg (Real.exp_pos _).le p.hand,fun i hf=> p.spear i (right_ne_zero_of_mul (show μ D δ X* F i≠0 from hf)),le_trans ?_ p.pay⟩
 apply Finset.sum_le_sum; intro i _; by_cases g:F i=0; · exact (by simp [g])
 rw [Pi.smul_apply,smul_eq_mul,←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (p.hand _); unfold Push.AbsoluteSums.Trees.currency; rw [←Real.exp_add]; apply Real.exp_monotone; rw [sub_mul]; have v:= Corona.cover_mono (p.spear _ g).1 D; have x:= mul_le_mul_of_nonneg_left (show (coverNumber D X:ℝ) ≤ _ from Nat.cast_le (α:=ℝ).mpr v) h; linarith
variable (X:ι→leaf (Site V))(Z:ι→Site V)
variable {I:Type}[Fintype I](R:I→ι→Track (Stilo.Harper (Site V)) ℝ)(C:I→ι→ℝ)
variable {p a u h ε c γ Δ d δ :ℝ}{D:ℕ}{L': Finset ι→List ι}
abbrev tallR(D:ℕ)(p δ:ℝ):ι→Track (Harper (Site V)) ℝ:= fun i=> μ D δ (X i).val • p • ∑ j:I,R j i
/-- Equation (*) via join convolution. Site price, no constants scaled by volume. -/
lemma uprootP (pA:∀ i j, Strung (X i).val (R j i) D a (C j i)) (e:∀ i, Z i∈ (X i).val) (v:∀ x,∀ j,(∑ i:ι with Z i=x,C j i) ≤ γ) (b:0≤p)(ht:0≤δ)(hu:0≤u)(dP:0<d) (r:∀ i,(L' i).toFinset=i)(l:∀ i,(L' i).Nodup)(g:reserve (a-δ) (u+d) 1 ε)(hv:payment 1 (6*(D+1)) 0 ε 1 (p*(Fintype.card I*γ)) (u+d) 0 ≤ c)(he:0<c)(hy:degreePrice D c d≤Δ)(h':Δ < 1)(n₀:ℕ)(x:Site V):(∑ i:Finset ι with Palot.outC n₀ i, invoiceB D u x (payH (tallR X R D p δ) (L' i))) ≤ c*Δ^n₀*(1-Δ)⁻¹:= by
 refine power_v X _ (fun i=>p*∑ j:I,C j i) Z (fun i=>((Strung.woven (D:=fun j=> C j i) (fun j _=>pA i j)).linear b).advance ht) e r l ?_ hu dP g hv he hy h' x (fun _=> le_rfl); intro x; rw [← mul_sum,sum_comm]; gcongr; calc
 (∑ x_':I,_) ≤ ∑ j:I,γ := Finset.sum_le_sum fun j _=> v x j
 _= _ := by simp
end YM.CF.Yaw
