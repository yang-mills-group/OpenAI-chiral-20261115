import YM.SU5.FiniteGaugeData.Nine.Oat
set_option autoImplicit false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Window.Pivot
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Tenant Fock Tulip Dial Fir Ember Buffered Skye Scree Nacre
attribute [local instance] opCStarAlgebra
variable {N:Side}(o:Cover)
open Brique Mir Phase RP Largo Spire
local notation "Μ"=> Single N
open Fock.Brique
open Fock.Brique
variable (k:ℕ)(M:Male)(g:SU.Slot) {h w:ℕ}{P': Finset (Single N)} {T:Support (More N)}(S:Finset (Site N))
local notation "F"=> funde k M N 1
local notation "D"=> Θ N (3:SpinIdx) g
local notation "U"=> Θ N (0:SpinIdx) g
local notation "Τ"=> cutM (U)
local notation "Η"=> cutM (D)
local notation "W"=> preF k M N g
local notation "L"=> (toolP k M N)
section pilot
-- sparse inverse finances. compress first by TWO slot id. A compression of full site estimate by projecting. 
def blossom : Finset Μ:= Θ N (3:SpinIdx) g∪ Θ N (0:SpinIdx) g
local notation "J"=> blossom g
@[simp] lemma blossom_pay(i:Single N):i∈ blossom g ↔ i.2=g∧ (i.1.2=3∨ i.1.2=0):=by rw [blossom,mem_union]; simp only [Θ, loci,mem_product,mem_univ,true_and,mem_singleton]; tauto
abbrev tribune (A:Op (Single N)):= cutM (blossom g)*A*cutM (blossom g)
-- enable at this cutoff h.heavy.
variable {c C v:ℝ} {X:Op (Single N)}
lemma seize (x: Site N)(p:1≤k)(u:0≤ v)(t:v≤1)(w:v ≤ rubra k N M)(h:v≤ villa k N M):‖implant {x} (tribune g (1-preF k M N g))‖ ≤ 1-v:=by
 let V:= implant {x} (tribune g (1-(W))); let A(i j:Single N):= if i=j then 1-v else 0
 let U₀:Μ:= ((x,0),g); let D₀:Μ:=((x,3),g); have he(i:Μ)(p:i∈blossom g)(v:x=i.1.1): i=U₀ ∨ i=D₀:=by obtain ⟨b,i'|i'⟩:= (blossom_pay g i).1 p; exact Or.inr (Prod.ext (Prod.ext v.symm i') b); exact Or.inl (Prod.ext (Prod.ext v.symm i') b)
 have hf(i j:Μ):‖V i j‖ ≤ A i j := by
    unfold V A; rw [implant_apply]; let e:= sub_nonneg.mpr t; -- branch bounds
    by_cases a:(i.1.1=x∧ j.1.1=x)
    · rw [if_pos (show _ from And.intro (mem_singleton.mpr a.1) (mem_singleton.mpr a.2))]; unfold tribune cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases i1:i∈blossom g <;> by_cases j1:j∈ blossom g
      · rw [if_pos i1, if_pos j1, one_mul,mul_one]; have hu:U₀≠ D₀:=fun t=> absurd (congrArg (fun i:Μ=>i.1.2) t) (by decide: (0:SpinIdx) ≠ 3); rcases he i i1 a.1.symm with rfl|rfl <;> rcases he j j1 a.2.symm with rfl|rfl -- rfl or rw
        · rw [Matrix.sub_apply, Matrix.one_apply_eq, (staple k M p g x), if_pos rfl]; exact hx u w (ax_top k N M).1
        · rw [Matrix.sub_apply, Matrix.one_apply_ne hu, stapleC k M p g, if_neg hu]; simp
        · rw [Matrix.sub_apply, Matrix.one_apply_ne hu.symm, stapleE k M p g, if_neg hu.symm]; simp
        rw [Matrix.sub_apply, Matrix.one_apply_eq, stapleB k M p, if_pos rfl]; exact hx u h (ax_top k N M).2
      all_goals simp [i1,j1]; intros; first| positivity| linarith
    simp only [mem_singleton,a,↓reduceIte,norm_zero]; split <;> linarith
 refine Branch.schur A V (1-v) (sub_nonneg.mpr t) hf ?_ ?_ <;> intro i <;> simp [A]
where hx {x y:ℝ}(h:0 ≤ x)(v:x ≤y)(z:y≤1): ‖1-(y:ℂ)‖ ≤ 1-x:= by rw [show 1-(y:ℂ)= ↑(1-y) by push_cast; rfl, Complex.norm_real,Real.norm_of_nonneg]; linarith; linarith
lemma near_buy {c w}(x:Liquid w (funde k M N 1) c)(u:1 ≤ k): Liquid (2*w) (tribune g (1-preF k M N g)) (opt c):=by
 have ht:= liq_inv x -- remove u
 have hv:‖L‖≤1:= (tool_proj k M u).norm_le _ -- tune
 exact liq_rT (liq_plus (blossom g) (liq_inv (liq_double ht ht hv hv (Θ N 3 g))))
local notation "Σ"=>implant S
local notation "B"=> tribune g (1-preF k M N g)
abbrev emU:= implant S (tribune g (1-preF k M N g))
lemma expensive (x:Liquid w (funde k M N 1) c)(u:1 ≤ k)(y: 2*opt c ≤ v/2)(z:0<v)(q:v≤rubra k N M)(t:v≤villa k N M)(p:Sparse (2*w) S): ‖implant S (tribune g (1-preF k M N g))‖ ≤ 1-v/2:= by
 obtain ⟨P,zL,w⟩:= near_buy k M g x u; have hv:v≤ 1:=q.trans ((ax_top k N M).1); have ht:= combined zL w p (sub_nonneg.mpr hv) (fun i _=> seize k M g i u z.le hv q t); linarith only [ht,y]
local notation "Ψ"=> (1-emU k M g S)⁻¹
abbrev peas : Finset Μ:= blossom g ∩ atSites S
abbrev volts : Finset Μ:= Θ N 0 g ∩ atSites S
local notation "E"=> cutM (peas g S)
local notation "P₀"=> cutM (volts g S)
lemma jewel_c : E * (1-W)* E=implant S (B) := by
 let K:= cutM (atSites S); let J':= cutM (blossom (N:=N) g); have he : cutM (peas g S)=J'*K∧cutM (peas g S)=K*J':= by
    unfold J' K; rw [cut_meet,cut_meet, inter_comm (atSites S)]; exact ⟨rfl,rfl⟩
 unfold implant tribune; change E*_ *E= K*(J'*_*J')*K; conv_lhs=>lhs; lhs; rw [he.2] -- `lhs` syntax term parentheses
 rw [he.1]; simp only [mul_assoc]; -- factor OK
lemma peas_more: volts g S⊆ peas g S:= inter_subset_inter (show Θ N 0 g⊆ blossom g from subset_union_right) le_rfl -- tuner implicit
lemma voltage : cutM (peas g S)*cutM (volts g S)= P₀:= by rw [cut_meet,inter_eq_right.mpr (peas_more ..)]
variable (u:IsUnit (1-emU k M g S))
include u
lemma moneyF (p:‖emU k M g S‖ ≤1-v)(q:0<v): ‖(1- emU k M g S)⁻¹‖ ≤ v⁻¹:= implant_inv S (B) u p q
lemma excite : Commute (cutM (peas g S)) ((1-emU k M g S)⁻¹):=by
 refine unit_com ?_ u; let T:= cutM (peas g S); let P₁:=emU k M g S; have ht:P₁ =T*(1-W)*T:= (jewel_c ..).symm
 change T*(1-P₁)=(1-P₁)*T; rw [sub_mul,mul_sub,mul_one,one_mul,ht, ←mul_assoc,←mul_assoc, (show T*T=T from (cutM_idp _).1),mul_assoc (T*_) T T,(show T*T=T from (cutM_idp _).1)]
#print axioms expensive
end pilot
end YM.CF.Window.Pivot
