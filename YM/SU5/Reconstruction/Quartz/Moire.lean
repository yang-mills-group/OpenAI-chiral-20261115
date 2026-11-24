import YM.SU5.Reconstruction.Quartz.HereThere
import YM.SU5.Reconstruction.Quartz.Felicity
import YM.SU5.Reconstruction.PilotLight.Clock
import YM.SU5.Reconstruction.Vermont.Benefit
-- # Graph recipe on this same law through any authentic Quarter
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open CrossedFrame
local notation "U"=>flank j 0∩flank z 0
local notation "Λ₁" i:max=>onceLens Y H V G C a χ i
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
local notation "Tm" i:max=> Picket.trans (S₀ i)
lemma growStencil (d t:Gt)(e:0<(d:ℝ))(v:0≤(t:ℝ))(x:Sky K)(A:(J₀ z).Op)(p': (Q z) (m₁ (eject z (-d)) x) t A) : (Q z) x (d+t) ((atEstate Y H V G.history G.clipped z false (C z) (w z) (eject z d))* A) := by
 let L₁:=ride Y H V G.history G.clipped z false (C z) (w z); let X':=(m₁ (eject z (-d)) x); have h:X'=(m₁ (eject z (-d)) x):=rfl; let P':=atEstate Y H V G.history G.clipped z false (C z) (w z); -- boxAfter ignores d? uses placement
 have h': (Q z) 1 0 1 := by
    have ht:= ChargeFrame.unitScore Y H V G z (C z) (w z) 0 le_rfl; simpa only [AddSubgroup.coe_zero, Real.toNNReal_zero,OS.Semigroup.eZero, show ContinuousLinearMap.id ℂ (J₀ z)=(1:(J₀ z).Op) from rfl] using ht
 have q:(Q z) X' t A:=p'
 have hh:= ChargeFrame.boxAfter Y H V G z (C z) (w z) (eject z d) (d+t) le_rfl v (show (0:Gt).val<(eject z d z).val from by simpa using e) (show ((eject z d z+t:Gt):ℝ)≤_ from by simp) h' q
 rw [one_mul, h, move_sum, selectRay, add_neg_cancel, eject_zero, move_by_zero,sub_zero,one_mul,selectRay,sub_self, show atEstate Y H V G.history G.clipped z false (C z) (w z) 0=1 from ?_, mul_one] at hh; exact hh
 rw [ChargeFrame.ensemble, ChargeFrame.charted_nil]; change L₁.E (Real.toNNReal ((0:Gt):ℝ))*1=1; rw [AddSubgroup.coe_zero,Real.toNNReal_zero,OS.Semigroup.eZero]; rw [mul_one]; rfl
include F
lemma paves (d:Gt)(x:(J₀ z).Op) : (Π z) (atEstate Y H V G.history G.clipped z false (C z) (w z) (eject z d)*x)= (Pr z) (eject z d)*(Π z) x:= by
 ext1 y; apply Subtype.ext; rw [carries_full Y H V G z (C z) (w z) (F.present z),mul_apply_eq_comp, mul_apply_eq_comp, estate_full,carries_full Y H V G z (C z) (w z) (F.present z)]
variable (u v:Axis→ marks (timeMesh Λ))
-- all uses real and THEIR original Photon clocks. Record on orientation b explicitly.
variable (A:(fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op) (x:ℕ→ Sky (tent Y H)) (h:ℕ → marks (timeMesh Λ))
local notation "s"=> u z+v z
-- joint autonomy keeps same actual Stamp purchase along all h, here b-output stated with padded left edge at 0. Limit d-fixed.
def AlongSight (Y':(G₀ z).Op):Prop:= ∃ B:ℕ→(J₀ z).Op,(∀ n,(Q z) (x n) (u z+v z) (B n)) ∧ Limited atTop (fun n=>(Π z) (B n)) Y'
include b p
lemma spinEcho (B:ℕ→ (J₀ j).Op)(d:0<(u z:ℝ))(d':0<(v z:ℝ))(S₁:Slip Y H V G C a χ j x h B A)(e:∀ n, x n∈ Ds (Tarp j (fun i=>(u i:ℝ)) (fun i=> (v i:ℝ)) (h n:ℝ)))(GB:ℕ→(J₀ z).Op)(q:Perpendicular Y H V G z (C z) (w z) (v z) (u z) x GB):∃ Y':(G₀ z).Op, Limited atTop (fun n=> (Pr z) (eject z (u z))*(Π z) (GB n)) Y' ∧ AlongSight Y H V G C a χ z u v x Y' ∧ Z.Pass (A*(Tm j) ((↑(u z+v z:Gt):ℝ) • basis z)) Y' := by
 let M':= atEstate Y H V G.history G.clipped z false (C z) (w z) (eject z (u z))
 let Q'(n):= M' * GB n; let k(n):=(Π z) (Q' n)
 have ht(n): k n=(Pr z) (eject z (u z)) *(Π z) (GB n):= paves Y H V G C a χ F z (u z) _
 obtain ⟨c,b₀⟩:= q.bounded
 have hb(n):‖k n‖≤c:= by rw[ht,bridge_time]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((S₀ z).shrinks _)).trans (b₀ n))
 let v':=(Tm j) (((u z+v z:Gt):ℝ) • basis z)
 let c'(n):= (Tm z) ((h n:ℝ) • basis j)
 have hh:Pearl atTop c' (1:(G₀ z).Op):= by
   rw [show (1:(G₀ z).Op)= Picket.trans (S₀ z) 0 from (S₀ z).unit.origin.symm]; refine Quartz.shouldFly z (S₀ z) _ _ _ ?_; simpa using S₁.short.smul (tendsto_const_nhds (x:=basis j))
 letI:=portrait Y H V G C a χ z
 have hx(n): (Q z) (x n) (u z+v z) (Q' n):= growStencil Y H V G C a χ z (u z) (v z) d d'.le _ _ (q.beyond _)
 have w₀(n): x n∈ Ds (Chambers.strip j 0 (h n:ℝ)∩ Chambers.strip z 0 (↑(u z+v z:Gt):ℝ)):= by
    apply domain_mono Y H G _ (e n); rintro i v; have hz:= v.2 z b.symm; exact ⟨v.1, (le_trans d.le hz.1), hz.2⟩ -- shadow v
 obtain ⟨Y',tg,g⟩:= Quartz.scene Z (A*v') _ k c' (S₁.propitious.toRight (Pearl.still atTop v')) hh ((norm_nonneg _).trans (hb 0)) hb (fun i=> herePass Y H V G C a χ F j z b Z p (x i) _ _ (B i) (Q' i) (S₁.stays i) (hx i) (S₁.phase i) (add_nonneg d.le d'.le) (w₀ i)) -- notation s casts in statement maybe macro fails
 simp_rw [← ht]; exact ⟨Y',g,⟨Q',hx,g⟩,tg⟩
-- loan receipt enough to couples, independence
structure Duet (B:(G₀ z).Op):Prop where
 posv : ∀ i,i ≠ j → 0 < (v i:ℝ)
 pose : 0< (u z:ℝ)
 uses: ∃ (x:ℕ→Sky (tent Y H))(h:ℕ→Gt)(Q':ℕ→ (J₀ j).Op)(T:ℕ→ (J₀ z).Op), Slip Y H V G C a χ j x h Q' A ∧ (∀ n, x n∈ Ds (Tarp j (fun i=>(u i:ℝ)) (fun i=>(v i:ℝ)) (h n:ℝ))) ∧ (∀ i,i≠j→∃ Tm':ℕ→ (J₀ i).Op, Perpendicular Y H V G i (C i) (w i) (v i) (u i) x Tm') ∧ Perpendicular Y H V G z (C z) (w z) (v z) (u z) x T ∧ Limited atTop (fun n=> (Pr z) (eject z (u z))*(Π z) (T n)) B
local notation "J"=>Duet Y H V G C a χ j z u v A
lemma bookedEcho (B:(G₀ z).Op)(q:J B): Z.Pass (A*(Tm j) ((↑(u z+v z:Gt):ℝ) • basis z)) B:= by
 obtain ⟨x,h,Y',X',a,g,-,i',k'⟩:=q.uses; obtain ⟨U',e,-,wθ⟩:=spinEcho Y H V G C _ χ F j z b Z p u v A x h _ q.pose (q.posv z b.symm) a g X' i'
 rw [show B=U' from ContinuousLinearMap.ext (fun t=>ext_inner_left ℂ (fun x=> tendsto_nhds_unique (k'.confirms ..) (e.confirms ..)))]; exact wθ
lemma awardEcho (e:0<(u z:ℝ))(p': Sight Y H V G C a χ j u v A) : ∃ Y':(G₀ z).Op,J Y' := by
 obtain ⟨q,h,x,B,t,v₀,p'⟩:=p'; obtain ⟨T,r⟩:=p' z b.symm; obtain ⟨Y',p₀,hA⟩:= spinEcho Y H V G C a χ F j z b Z p u v A x h B e (q z b.symm) t v₀ T r; exact ⟨Y',q,e,x,h,B,T,t,v₀,p',r,p₀⟩
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
