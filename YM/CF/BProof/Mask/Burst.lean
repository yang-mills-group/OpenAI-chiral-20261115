import YM.CF.BProof.Mask.Gong
import YM.CF.BProof.Mask.Post
import YM.CF.BProof.Grid.Vertex
import YM.CF.BProof.Counter.Turn
import YM.CF.Ridge.Ply
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide.Mask
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Half
open Skye Taxi.Denn Py
open Cupboard Cupboard.Episode
variable {N L:Side}{r:ℕ} {R:Patch}
local notation "Λ"=>More N
variable (i:Axis)(Z: Zoned N r R)
variable {a k:ℕ}(X: ClockD R r a k)(P:BudgetPoint)(x:ℝ)
local notation "Xs" b:max=>shade N i b r
local notation "Γ"=> Z.val.val
abbrev storm (b:Bool):= Finset.univ.filter fun v:Cart.CubeP N => v.2∈Xs b
def income (b:Bool)(U:Pane N):= ∑ v∈storm (r:=r) i b, (Γ).mark x v P U
lemma under (b: Bool): LocalOn (shade N i b X.gF) (income i Z P x b):=fun U V h=> sum_congr rfl fun j u=> (Γ).mark_reads _ _ _ <| agrees_mono h (fun y v=>by obtain ⟨k,t,m⟩:= halo_spec.mp (show _∈ _ from v); rw [mem_singleton] at t; subst k; exact moveS i b (mem_filter.mp u).2 m (by have :=X.visor; omega)) -- tune
lemma payV(b:Bool): Envelope (income i Z P x b):= Envelope.sum _ _ (fun i=>⟨(Γ).mark_M _,_,fun U=>(Real.norm_eq_abs _).trans_le ((Γ).mark_pay _)⟩) -- choice infer bound above Pi etc
include X
lemma exhaustive (U:Pane N) : income i Z P x true U+income i Z P x false U= (Γ).PiZ P x U:=by
 have hx:0< r:=by have h:=X.visor; omega
 unfold income Taxi.Denn.Cart.PiZ; rw [←Finset.sum_union]; swap
 · exact Finset.disjoint_left.mpr fun j v g=> Finset.disjoint_left.mp (Half.splits (N:=N) i true hx) (mem_filter.mp v).2 (mem_filter.mp g).2
 apply Finset.sum_subset (subset_univ _); intro j _ p; have he : (Γ).w j.1 j.2=0:=by contrapose! p; rcases Finset.mem_union.mp (Z.property i _ _ p) with p|p; exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,p⟩); exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,p⟩)
 unfold Taxi.Denn.Cart.mark Taxi.Denn.Cart.kWh; rw [he]; simp
omit X
abbrev sZ:= Fixed.reflectSweep N i
lemma offer(b:Bool)(j:Cart.CubeP N)(U: Pane N): (let v:=(boxA (sZ (N:=N) i)).symm j.1; let z:=(boxA (sZ (N:=N) i)).symm j.2; (Γ).mark x (v,z) P (Fixed.reflConfig N i U)=(Γ).mark x j P U∧(z∈Xs (!b) ↔ j.2∈Xs b)):=by
 let s:=sZ (N:=N) i; intro v z; refine ⟨?_,?_⟩
 · rw [←Fixed.flash_reflect]; exact (Γ).mark_turn s (Z.val.property s ⟨0,by simp [s,sZ]⟩) _
 rw [←shade_carry i b]; simp [regionD, z, s]
lemma income_flip (U:Pane N): income i Z P x true (Fixed.reflConfig N i U)=income i Z P x false U:=by
 let e:= (boxA (sZ (N:=N) i)).symm; symm; unfold income; refine Finset.sum_equiv (e.prodCongr e) ?_ (fun i' _=>(offer i Z P x false i' U).1.symm); intro j; simp only [storm, mem_filter,mem_univ,true_and]; exact (offer i Z P x false j U).2.symm
abbrev device (i:Axis)(X:ClockD R r a k)(g: Pane N→ℝ) := ∃ F:Pane N→ℝ, Envelope F∧LocalOn (shade N i true X.gF) F∧∀ U,g U= F U* F (Fixed.reflConfig N i U)
include X
lemma deviceP : device i X (fun U=> Real.exp ((Γ).PiZ P x U)) :=by
 let F:= income i Z P x true; refine ⟨_,(payV i Z P x true).exp,fun U V p=>congrArg Real.exp (under i Z X P x true U V p),fun U=>?_⟩; dsimp only; rw [←Real.exp_add, ← exhaustive i Z X, income_flip]
end YM.CF.BProof.Bide.Mask
