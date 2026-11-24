import YM.CF.Buffered.PushMark
import YM.SU5.Reconstruction.Hygrometry.Libretto
/-! # finite plate. Spin capital used by a strict mark.
  number of legs retained through entire launch; footprint in gauge lattice.  -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Advance.Depths
open Function Fock NormedSpace SU Lat Lattice Spire Cube Finset MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree Vault Fir Peaks Drapes Tap Precision Tree Next.SectorChange Stencil
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Hygrometry
variable {I:Type*}[LinearOrder I][Fintype I]
structure CapLength (C:List I)(S: Finset I)(b:Bool)(κ:ℕ) : Prop where
 limbs : C.length ≤ κ
 touches : ∀ i∈ C,i∈ S
 color : wheat C=b
noncomputable def SpinLen (A S:Finset I)(b:Bool)(κ:ℕ):Submodule ℂ (FC I):=Submodule.span ℂ {v| ∃ C:List I,CapLength C S b κ ∧ rollC (think A).term C=v}
variable {A S T:Finset I} {b c:Bool}{κ κ':ℕ}
lemma caseSeed {C:List I}(p:CapLength C S b κ): rollC (think A).term C ∈ SpinLen A S b κ := Submodule.subset_span (Set.mem_setOf_eq ▸ ⟨C,p,rfl⟩)
lemma monotone (h:S⊆T)(t:κ≤κ'): SpinLen A S b κ ≤ SpinLen A T b κ':=by
 apply Submodule.span_le.mpr; rintro i ⟨C,⟨a,b,c⟩,rfl⟩; exact caseSeed ⟨le_trans a t,fun i v=>h (b i v),c⟩
lemma capOne : 1∈ SpinLen A S false κ:=by
 have hz:CapLength [] S false κ:=⟨Nat.zero_le _,by simp,rfl⟩
 exact caseSeed hz
lemma capTiny (i:I)(t:i∈S) : (think A).term i∈ SpinLen A S true 1:=by
 have he:=caseSeed (A:=A) (κ:=1) (b:=true) (S:=S) (C:=[i]) ⟨le_rfl,by simpa using t,rfl⟩; simpa [rollC] using he
private lemma longer(C D:List I): wheat (C++D)=(wheat C).xor (wheat D):= by induction C with
 | nil=> exact (Bool.false_xor _).symm
 | cons x C ih=> rw [List.cons_append,wheat,ih,wheat,Bool.xor_assoc]
lemma longerF {v u: FC I}(f:v∈ SpinLen A S b κ)(g:u∈SpinLen A S c κ'): v*u∈SpinLen A S (b.xor c) (κ+κ') := by
 let T:=SpinLen A S (b.xor c) (κ+κ'); change _∈ T
 refine Submodule.span_induction (p:=fun f _=>f*u∈T) (fun f v=>?_) (by rw [zero_mul]; exact T.zero_mem) (fun _ _ _ _ u v=> by rw [add_mul]; exact T.add_mem u v) (fun x y _ z=>by rw [Matrix.smul_mul]; exact T.smul_mem _ z) (show v∈ Submodule.span _ _ from f)
 refine Submodule.span_induction (p:=fun t _=>f*t∈T) (fun g w=>?_) (by rw [mul_zero]; exact T.zero_mem) (fun _ _ _ _ u v=> by rw [mul_add]; exact T.add_mem u v) (fun x y _ z=>by rw [Matrix.mul_smul]; exact T.smul_mem _ z) (show u∈ Submodule.span _ _ from g) -- refine leaves
 obtain ⟨X,⟨hx,X',rfl⟩,rfl⟩:= v; obtain ⟨Y,⟨hy,Y',rfl⟩,rfl⟩:=w; rw [←show rollC (think A).term (X++Y)=_ * _ from (by rw [rollC,List.map_append,List.prod_append]; rfl)]; exact caseSeed ⟨by simpa only [List.length_append] using Nat.add_le_add hx hy,fun i p=>(List.mem_append.mp p).elim (X' i) (Y' i),longer X Y⟩
lemma capValidC (C:List I)(p:∀ i∈ C,i∈ S): Fine A S (wheat C) (rollC (think A).term C):=by
 induction C with
 | nil=> exact Fine.one
 | cons i C ih=>exact (Fine.seed i (p _ (by simp))).grow (ih (fun i q=> p i (List.mem_cons_of_mem _ q)))
lemma capCreates (x:Ket I)(h:withinM A x)(v:withinM S x) : create x∈ SpinLen A S true 1:=by
 let W:=SpinLen A S true 1; change _∈W; rw [create_def]; refine W.sum_mem fun i _=>?_ ; by_cases p:i∈A; swap; · rw [(within_test ..).mp h i p,zero_smul]; exact W.zero_mem
 by_cases q:i∈ S; swap; · rw [(within_test ..).mp v i q,zero_smul]; exact W.zero_mem
 rw [←show (think A).term i=put i from if_pos p]; exact W.smul_mem _ (capTiny i q)
lemma capRemoves (x:Ket I)(h:withinM Aᶜ x)(v:withinM S x): Fock.remove x∈ SpinLen A S true 1:=by
 let W:=SpinLen A S true 1; change _∈W; rw [remove_def]; refine W.sum_mem fun i _=>?_; by_cases p : i ∈ Aᶜ; swap
 · rw [(within_test ..).mp h i p,star_zero,zero_smul]; exact W.zero_mem
 by_cases q : i ∈ S; swap
 · rw [(within_test ..).mp v i q,star_zero,zero_smul]; exact W.zero_mem
 have t: -takeF i∈ W:=(show (think A).term i= -takeF i from if_neg (mem_compl.mp p)) ▸ capTiny i q
 apply W.smul_mem; simpa using W.neg_mem t
variable {N P : Side} (G : Ratio N P) (A' : RG.StepData (More N) (More P))
variable (j : ℕ) (Q : Op SU.Slot) (M : Male) (ho : Odd G.count.val) (q : Chi) (d β : ℝ) (l : Loom N)
local notation "L" => G.count.val
variable {R w : ℕ} (p : LaurentRadius j G.count R)
variable (U:Support (More N)) (z:Nom N P)
local notation "W" a:max b:max => SpinLen (Tset P) (modesIn P (padded G U (clothRadius G.count R))) a b
include p ho
lemma longer_sub (v:FC (Single N))(h:v∈SpinLen (Tset N) (modesIn N U) b κ): subF G j Q M ho z v∈ SpinLen (Tset P) (modesIn P (padded G U (clothRadius G.count R))) b κ:=by
 set W' := W b κ
 refine Submodule.span_induction (p:=fun f _=> subF G j Q M ho z f∈W') (fun u v=>?_) (by rw [map_zero]; exact W'.zero_mem) (fun _ _ _ _ u v=>by rw [map_add]; exact W'.add_mem u v) (fun _ _ _ v=>by rw [map_smul]; exact W'.smul_mem _ v) (show v∈ Submodule.span _ _ from h)
 have he(C:List (Single N))(X:∀ i∈C,i∈ modesIn N U): subF G j Q M ho z (rollC (think (Tset N)).term C)∈ SpinLen (Tset P) (modesIn P (padded G U (clothRadius G.count R))) (wheat C) C.length:=by
    induction C with
    | nil=> change subF G j Q M ho z 1∈ W false 0; rw [sub_one]; exact capOne
    | cons i C ih=>
      have hp:=X i (by simp); have hk:=fun j' hx=>X j' (List.mem_cons_of_mem i hx)
      rw [wheat,  (show rollC (think (Tset N)).term (i::C)=(think (Tset N)).term i*rollC (think (Tset N)).term C from rfl),List.length_cons,add_comm, sub_mul G j Q M ho z (Fine.seed i hp) (capValidC C hk)]
      apply longerF _ (ih hk)
      have hz := mode_support G j Q M ho U p (z:=z) (within_basis _ i hp)
      by_cases g' : i∈ Tset N
      · rw [show (think (Tset N)).term i=put i from if_pos g', sub_put _ _ _ _ _ z _ g']; exact capCreates _ (carried_up G j Q M ho z true (within_basis _ i g')) (hz true)
      rw [show (think (Tset N)).term i= -takeF i from if_neg g', map_neg,sub_take _ _ _ _ _ _ _ g']; exact (W true 1).neg_mem (capRemoves _ (carried_down G j Q M ho z false (within_basis _ i (mem_compl.mpr g'))) (hz false))
 obtain ⟨C,e,rfl⟩:=v; rw [show W'= W b κ from rfl,←e.color]; exact Depths.monotone (Subset.refl _) e.limbs (he C e.touches)
omit ho p in
private lemma capIntegral {X:Type*}[MeasurableSpace X]{μ:Measure X}[IsProbabilityMeasure μ]{X':X→ FC I}(p:∀ x,X' x∈ SpinLen A S b κ): (∫ x,X' x ∂μ) ∈ SpinLen A S b κ:= by
 by_cases e:Integrable X' μ
 · let T:= (SpinLen A S b κ).restrictScalars ℝ; exact T.convex.integral_mem T.closed_of_finiteDimensional (show ∀ᵐ x ∂μ,X' x∈ T from Filter.Eventually.of_forall p) e
 rw [integral_undef e]; exact Submodule.zero_mem _
noncomputable def Keeps (N:Side)(κ:ℕ)(U:Support (More N))(b:Bool)(f: Mark N): Prop:=∀ X,f X∈ SpinLen (Tset N) (modesIn N U) b κ
lemma capPush {f:Mark N}(e:Keeps N κ U b f): Keeps P κ (padded G U (clothRadius G.count R)) b (pushMark G A' j Q M ho q d β l f):=by
 intro X; unfold pushMark linkLaw; apply capIntegral; intro V
 let T:= (W b κ).restrictScalars ℝ; apply T.smul_mem; unfold assembled; apply capIntegral; intro k
 apply T.smul_mem; exact T.sum_mem (fun i _=>longer_sub G j Q M ho p U _ _ (e (drawn l (V,k)))) -- verify nested restrict
omit p ho in
lemma increaseScope {f: Mark N}{S' T': Support (More N)} (p:S'⊆T')(v:Keeps N κ S' b f): Keeps N κ T' b f:= fun x => monotone (modes_monotone p) le_rfl (v x)

end YM.CF.Buffered.Advance.Depths
#print axioms YM.CF.Buffered.Advance.Depths.capPush
