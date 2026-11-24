import YM.SU5.FiniteGaugeData.Nine.Nuage
import YM.SU5.FiniteGaugeData.Mirage.Faint
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
local notation "P"=> volts g S
-- pick exactly knob
variable (σ: Window.Family)
abbrev bossColor (σ:Window.Family):=(knob (N:=1) 0 σ).2
lemma knobColor (x:Site N): (knob x σ).2= bossColor σ:=rfl
lemma bossC : family (bossColor σ)=σ:= ((is_cap ..).1 (knob_p σ (0:Site 1))).2.1
lemma bossPopulation : seedlings S σ= volts (bossColor σ) S:= by -- remove g
 ext v; obtain ⟨⟨x,i⟩,b⟩:= v; constructor <;> intro p
 · obtain ⟨z,t,e⟩:=mem_image.mp p
   have h:(x,i)=(z,0):=(Prod.mk.inj e).1.symm; obtain ⟨rfl,rfl⟩:= Prod.mk.inj h; have he:b=bossColor σ:= (Prod.mk.inj e).2.symm; simp only [volts, Θ, loci, mem_inter, sites_eq, t, he, mem_product, mem_univ, mem_singleton, and_self]
 refine mem_image.mpr ⟨x,(sites_eq ..).mp (mem_inter.mp p).2,?_⟩; let Q:= mem_product.mp (mem_inter.mp p).1; exact Prod.ext (Prod.ext rfl (mem_singleton.mp (mem_product.mp Q.1).2).symm) (mem_singleton.mp Q.2).symm
section wills
variable (T :Support (More N))(Q R:Finset (Single N)){H₁:Op (Single N)} {v c:ℝ}
local notation "A"=> localP k M g S T
local notation "B"=> localM o k M g S T
variable (p:1≤k)(e:Aptitude k N)(v0: IsUnit (1-emU k M g S))(x0:S.image node⊆ T)
def officeH := lodgeP (Tset N) (P) (localP k M g S T) (localM o k M g S T) Q
local notation "Ξ"=> officeH o k M g S T Q
lemma withinMinus (x:Ket Μ)(L':Finset Μ)(p:withinM L' x): withinM L' (-x):=by unfold withinM; rw [map_neg,p]
include p e v0 x0
lemma office_shape (g0:g=bossColor σ): Barque σ S (T\S.image node) (officeH o k M g S T Q-1) := by
 let X:=oasis A B Q; have hv(i:Μ):withinM (lumen σ (T\S.image node)) (acts (cutM (Tset N)ᶜ*X) (basisKet i)):=by
    rw [act_mul]; unfold X; by_cases t:i∈Q; · rw [stah A B Q i t,←act_mul]; exact gap_above o k M g S T v0 p e x0 (g0 ▸ bossC σ) _
    rw [stah2 A B Q i t,←act_mul,same_dual o k M g S p e,act_neg]; exact withinMinus _ _ (gap_above o k M g S T v0 p e x0 (g0 ▸ bossC σ) _)
 unfold officeH; rw [show (P)=seedlings S σ from (g0 ▸ (bossPopulation S σ).symm)]; exact lift_bar σ S _ X (fun i _=> hv i)
local notation "P₀"=> cutM (P)
omit p e v0 x0
lemma secure : P ⊆ Tset N:= fun i v=> (grade_one ..).2 ((mem_singleton.mp (mem_product.mp (mem_product.mp (mem_inter.mp v).1).1).2).symm ▸ (by decide : (0:SpinIdx)∈ plusHalf))
private lemma payMatter {D₀:Op Μ}(u: IsStarProjection D₀)(X:Op Μ)(p1:P₀ *X=P₀)(q₁:‖D₀*X‖ ≤ c)(s:cutM (modesIn N T)*X=X)(G:oasis A B Q* cutM R=X* cutM R)(t:R⊆volts g S): Mirage.Marble D₀ T R.card (Ξ) c:=by
 let U':= cutM R; let Z:= X*U'; have hp:X*U'*U'=Z:=by rw [mul_assoc X, show U'*U'=U' from (cutM_idp _).1]
 have hv:P₀*Z=U':= by unfold Z; rw [←mul_assoc, p1,cut_meet (volts g S) R, inter_eq_right.mpr t]; 
 have ht: U'*Z=U':=by nth_rw 1 [←(show U'*P₀=U' from cut_meet ..|>.trans (congrArg cutM (inter_eq_left.mpr t)))]; rw [mul_assoc,hv,(show U'*U'=U' from (cutM_idp R).1)] -- tune
 let Q':=Fock.Brique.Ortho Z; let he:= ortho_project Z; have hy : IsStarProjection Q':=he
 refine ⟨Q',ortho_cellar _ (by unfold Z; rw [←mul_assoc,s]),he,(tankL_trace Z U' hp ht).trans (trace_cut R),?_,?_⟩ -- tune
 · unfold officeH lodgeP; rw [star_star]; exact starMS t (secure g S) (mateK N) (touchP _ ▸ tickB _) ((mul_assoc _ _ _).trans hv) G -- tune
 rw [← norm_star,star_mul,u.2.star_eq,hy.2.star_eq]; nth_rw 1 [show Q'=Z*Q' from (tankL_quad Z U' hp ht).symm]; rw [←mul_assoc]; unfold Z; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (hy.norm_le _)).trans (by rw [←mul_assoc]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _)).trans q₁)))
-- burger choose exact R count smaller subset. witness missing.If P.count≥ n efficiency.
include p e v0
variable (L0:0<v)(v1:‖emU k M g S‖ ≤1-v)
include L0 v1
local notation "J_"=>piQu o N (funde k M N 1)
local notation "Q_D"=>opt c*v⁻¹
lemma pay_choice (x:Liquid w (funde k M N 1) c)(t:Lattice.halo (2*w) (S.image node)⊆T)(u:R ⊆ P) : (R ⊆ Q→ Mirage.Marble (funde k M N 1) T R.card (Ξ) (opt c*v⁻¹)) ∧ (Disjoint Q R→Mirage.Marble (J_) T R.card (Ξ) (opt c*v⁻¹)) := by
 have he:S.image node ⊆T:= (halo_subset ..).trans t; let HV:= PeakP_pro (N:=N) k M p; let R0:=Peaked o k M g S v0 p e he; let Q0:= lossUse o k M g S v0 p e L0 v1 x t; have hx:∀ X:Op Μ,let Y:=cutM (modesIn N T); Y*(Y*X)=Y*X:= fun X=> by intro Y; exact (mul_assoc ..).symm.trans (congrArg (fun v=>v*X) (show Y*Y=Y from (cutM_idp (modesIn N T)).1))
 exact ⟨fun hh=> payMatter o k M g S T Q R HV A R0.2.2 Q0.1 (hx _) (parkA hh) u,fun hh=> payMatter o k M g S T Q R (rot _ HV _) B R0.2.1 Q0.2 (hx _) (parkB hh) u⟩
lemma pay_norm : ‖(Ξ)‖ ≤ (1+2*v⁻¹)^ (P).card:= lodge_cost _ A B _ (inv_pos.mpr L0|>.le) _ _ (cost_here o k M g S v0 p e L0 v1).1 (cost_here o k M g S v0 p e L0 v1).2 -- nonempty implicit. u m positive
#print axioms pay_choice
#print axioms office_shape
end wills
end YM.CF.Window.Pivot
