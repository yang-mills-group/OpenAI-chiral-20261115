import YM.CF.Cloak.Tale
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
section bound
variable {E X:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x₀:E}{U:E→ Config G f}{u v C D:ℝ}{T:E→X}[NormedAddCommGroup X][NormedSpace ℝ X]
local notation "m"=> SU.group.colorScale
open scoped Classical
variable {X₂:Support f}{U₀:Config G f}{A:Finset (Cell f)}{F:Forest S.ratio}{s:ℝ}
open Atala
lemma pong(n:ℕ)(C:ℝ)(hc:1≤C):∃ K v:ℝ,1≤K ∧m≤K ∧0<v∧ ∀{f:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G f)(X:E)(t:ℝ),0 ≤ t →t≤v→ Trow U X (C*t) n → ∀ z:Signed,Trow (pull z 0∘ U) X (K*t) n ∧ ∀ i:Cell f,Tender (fun y=>faceValue (pull z 0 (U y)) i) X (K*t) n:=by
 obtain ⟨p,V,h,hV,Y,T⟩:=joint_s n 4; have ht:0<C:=zero_lt_one.trans_le hc; refine ⟨V*C,p/C,one_le_mul_of_one_le_of_one_le Y hc,hV.trans (le_mul_of_one_le_right (zero_le_one.trans Y) hc),div_pos h ht,@fun f E _ _ U X t hx hp hv z=>?_⟩; let g(i:Site f)(w:Walk)(h:w.length≤4):Tender (fun y=> travel (pull z 0 (U y)) i w) X (V*(C*t)) n:= T U X _ (mul_nonneg ht.le hx) ((mul_comm ..).le.trans ((le_div_iff₀ ht).mp hp)) hv z i w h; rw [mul_assoc]; refine ⟨fun i=>?_,fun i=> g _ _ le_rfl⟩
 let W:= ([⟨i.2,false⟩]:Walk); apply (g i.1 W (by simp [W])).same; apply Eventually.of_forall; intro x; change SU.group.mat (travel (pull z 0 (U x)) i.1 W)=_; simp only [W,travel,Step.read,Step.used, Bool.false_eq_true,↓reduceIte,mul_one]; rfl -- tune
lemma ink(n:ℕ)(D s:ℝ)(hs:0<s)(h:m ≤ D):∃ K:ℝ,0≤K ∧∀{f:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G f)(X:E)(t:ℝ),0<t→t≤1 → Trow U X (D*t) n → (∀ i:Cell f,Tender (fun y=>faceValue (U y) i) X (D*t) n) →∀ (w:RG.Slot)(i:Site f),Pressure.toll (U X) (Work.F03.slotFace w i)≤ t→ Allows n (fun y=> w.atSite (U y) i) X (K*Real.exp (s*w.length)*t):=by
 have hm:=SU.group.colorScale_pos; have hD:0<D:= hm.trans_le h; obtain ⟨N,hN,H⟩:=travel_coupon G n D hD.le (half_pos hs); let fT:=curvatureCost G*D; let K:=m⁻¹*((2:ℝ)^n*((2:ℝ)^n*N*(m*fT))*N); have hF:0≤fT:=by exact mul_nonneg (curvature_nn G) hD.le -- tune
 refine ⟨K,by unfold K; positivity,@fun f E _ _ U X t hp ht hv hK w i he=>?_⟩; let j:=Work.F03.slotFace w i; let V(x):=faceValue (U x) j; have hu(a): grantB n (fun y=>U y a) X D := ((hv a).paid (d:=m) (le_of_eq ?_)).mono (max_le (mul_le_of_le_one_right hD.le ht) h) -- tune norm mat
 · have he': Allows n (fun y=>SU.group.curvature (V y)) X (fT*t):=by
      apply ((arc_b («G»:=SU.group) (faint_w t hp V (hK _) he h)).mono (Eq.le (mul_assoc _ _ _).symm)).germ; apply Eventually.of_forall; intro y; change curvatureL G (_-1)= curvatureL G (SU.group.mat (V y)); rw [map_sub, show curvatureL G 1=0 from ?_, sub_zero]; rw [← SU.group.mat_one]; apply norm_le_zero_iff.mp; exact (SU.group.curvature_norm _).trans_eq (SU.group.chord_one)
   have he:= adjointQ ((trekP _ U hu w.walk i w.length (Nat.le_add_right w.walk.length 4)).mono (H _)) he'; simp_rw [Work.F03.atSite_path]; apply he.mono; unfold K; rw [show Real.exp (s*w.length) =Real.exp (s/2*w.length)*Real.exp (s/2*w.length) from by rw [←Real.exp_add]; congr 1; ring]; ring_nf; rfl
 · change ‖SU.group.mat _‖ = _; simp only [Gauge.unitary_frob (SU.group.mat_mul_star _)]; rfl -- tune
end bound
end YM.CF.Cloak
