import GaugeFieldConstruction.Limber
/-! A tightened Footmark for F3. Uses actual coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 52000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
open AnalyticBridge VerifiedReset Taxi Lenten Flot Lenten.ModuleB
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove
open MultiNext.SignedSource PhysicalNext.JointLoad Analysis Siete Banjo
namespace Axon
open Prism
variable {n:Side}{P: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c s B b V:ℝ}{g:Finset (Dwell n) → ℝ}{m:ℕ}
local notation "αₚ"=> X.val.1
local notation "C'"=> X.val.2
-- tailored Ball, permits coarse coefficients 
structure Tips(P:BudgetPoint)(X:Scree.Hub n)(A:ℝ)(f:Wheel Axis SU.group.Color)(i:tangD n):Prop where
 identified : Agrees X.val.2 i (camW X.val.1 f)
 cash(k:Axis) : ‖f k 0‖ ≤ A*P.threshold

def PollenG(P:BudgetPoint)(X:Scree.Hub n)(A:ℝ)(i:tangD n) (l:ℕ):Prop:=∃ f:Wheel Axis SU.group.Color,Tips P X A f i ∧ (∀ k,Paper l (f k)) ∧ ∀ k j,‖advance k (f j) 0‖≤ A*P.threshold
lemma PollenG.foot {i:tangD n}(p:PollenG P X s i m):Blade m X i:=by obtain ⟨f,h,t,e⟩:=p; exact ⟨f,t, fun i v p=>(h.identified i v p).symm⟩
-- using breadth
abbrev bitU(P:BudgetPoint)(X:Scree.Hub n): ℕ:=4*Heir.breadth P X.val.2
abbrev αSpring(P:BudgetPoint)(X:Scree.Hub n)(A:ℝ):= A*P.threshold*bitU P X
abbrev tideV(P:BudgetPoint)(X:Scree.Hub n)(A:ℝ):= A*P.threshold*(1+2*(bitU P X:ℝ))*bitU P X
lemma roof_lot (i:Skye.Seat n)(p:i∈ X.val.2): lateral (stem αₚ i) ≤ bitU P X:= (stem_t _ _).trans (Nat.mul_le_mul_left _ (Heir.close_enough X.property (mem_union_left _ p)))
-- deduced gradient certificate on X. 
def Glass(X:Scree.Hub n)(x:tangD n)(b:ℝ):Prop:=∃ g:Skye.Seat n → SU.group.Color, Agrees X.val.2 x (VerifiedReset.gradient g)∧ ∀ i∈X.val.2, ‖g i‖≤b
variable (u:Nonwrapping X.val.2 X.val.1)(e:10≤(More n).val)
include u e
lemma G2k' {a:ℝ} (i:tangD n)(b:Cover→SU.group.Color)(v:b 0=0)(w:Agrees X.val.2 i (camW X.val.1 (fun j=> advance j b))) (h:∀ j:Cover,lateral j≤bitU P X → ∀ k,‖advance k b j‖≤a): Glass X i (a*bitU P X) := by
 refine ⟨b∘stem X.val.1, extX _ _ i u e (fun k=>rfl) w,fun j p=>?_⟩; have hf := roof_lot (P:=P) j p; have hh:0 ≤ a:= (norm_nonneg _).trans (h 0 (by rw [lateral_zero]; omega) (0:Axis))
 exact (loom_smaller b _ hf v (fun t l i _=> h t l i)).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hf) hh)
lemma G1k' {a:ℝ}(i:tangD n)(t:PollenG P X a i 1) : Glass X i (αSpring P X a):=by
 obtain ⟨f,p,g,x⟩:=t; obtain ⟨z,b,v⟩:=direction0 g; let Y:= fun i=>z i-z 0
 have hg(i): advance i Y= advance i z:=by funext x; unfold FlightFlux.advance Y; abel
 have he: f=fun i=> advance i Y:=funext fun i=> (v i).trans (hg i).symm
 apply G2k' u e i Y (sub_self _) (he ▸ p.identified)
 intro j w k; rw [hg,←v]; rw [show f k j=f k 0 from tear ..]; exact p.cash k -- tune
 apply fun _=> paper_start.mp (paper_leg.mp (g k) _) -- tune at
omit u e
lemma mouth_B {A:ℝ} (f:Wheel Axis SU.group.Color)(g:∀ k j,‖advance k (f j) 0‖≤ A) : ‖mouthV f‖ ≤ 2*A:=by
 have hx:0 ≤ A:=(norm_nonneg _).trans (g (0:Axis) (0:Axis)); have hA:0 ≤ 2*A:=by positivity
 change ‖(mouthV f).val‖ ≤ _; apply (pi_norm_le_iff_of_nonneg hA).2; intro i; apply (pi_norm_le_iff_of_nonneg hA).2; intro j
 exact (norm_sub_le ..).trans ((add_le_add (g i j) (g j i)).trans_eq (two_mul A).symm)
include u e
lemma G2k {a:ℝ}(i:tangD n)(t:PollenG P X a i 2):∃ A:ComG,‖A‖≤2*a ∧ Glass X (i-gateC αₚ P.threshold A) (tideV P X a) := by
 obtain ⟨f,p,g,x⟩:=t; obtain ⟨z,b,v⟩:=direction1 g; let Y:= fun i=>z i-z 0; have hg(i): advance i Y=advance i z:=by funext x; unfold FlightFlux.advance Y; abel
 let B:=mouthV f; let H:=P.threshold; let w:= i-camW X.val.1 (formC B); let D:= a*H; have hD:0 ≤ D:=(norm_nonneg _).trans (p.cash (0:Axis))
 have ht:0 < H:=P.threshold_pos; have hb := mouth_B f x; change ‖B‖≤ 2*D at hb; refine ⟨P.threshold⁻¹ • B, ?_, ?_⟩; · rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr P.threshold_pos.le),inv_mul_le_iff₀ ht]; exact hb.trans_eq (by unfold D H; ring)
 rw [show gateC _ _ _ = _ from (show gateC _ _ _= _ from (Ξ_share (P:=P) B))]; have hv:Agrees X.val.2 w (camW X.val.1 (fun j=> advance j Y)):=by intro k l i; unfold w; rw [Pi.sub_apply, p.identified k l i]; unfold B; generalize hX:mouthV f=B'; have he:= v k.2; rw [hX] at he; unfold camW; simp only [he,Pi.add_apply,hg]; abel -- f shadows tactic i
 change Glass X w (a*H*(1+2*(bitU P X:ℝ))*bitU P X); apply G2k' u e w Y (sub_self _) hv
 intro j h' k; rw [hg]; have he: advance k z j= f k j-formC B k j:=by rw [show f k = formC B k + advance k z from v k, Pi.add_apply]; abel
 rw [he]; apply (norm_sub_le ..).trans; let T:ℝ:=bitU P X; have hx:(lateral j:ℝ)≤T:= Nat.cast_le.mpr h'
 have ht:‖f k j‖≤ D+T*D:=by
    rw [show f k j= f k 0+ slope (fun i=> advance i (f k) 0) j from (((congrFun (dock_sewn _ (g k)) j)).symm)]
    exact (norm_add_le ..).trans (add_le_add (p.cash _) ((slope_est _ _ D hD fun i=>x i k).trans (mul_le_mul_of_nonneg_right hx hD)))
 apply (add_le_add ht ((formC_norm B k j).trans (c:= (1/2:ℝ)*T*(2*D)) ?_)).trans_eq; swap; · gcongr -- tune
 unfold T D H; ring
-- mast reverse Hess complex
omit u e
lemma mast_v (v:PressB P X Q h c)(x y:tangD n): mastX Q 0 ![x,y]= mastX Q 0 ![y,x]:=by
 ext i j; let T:=portE Q i j
 have hp:= slake_g v i.1 j.1 i.2 j.2; change ContDiffAt ℝ 2 T 0 at hp
 have hv(L:ℂ→L[ℝ]ℝ): L (mastX Q 0 ![x,y] i j)= L (mastX Q 0 ![y,x] i j):=by
    have he:ContDiffAt ℝ 2 (L ∘ T) 0:= L.contDiff.contDiffAt.comp _ hp; have hx(i:Fin 2→ tangD n): L (iteratedFDeriv ℝ 2 T 0 i)= iteratedFDeriv ℝ 2 (L ∘ T) 0 i:= (DFunLike.congr_fun (L.iteratedFDeriv_comp_left hp (i:=2) (by decide)) i).symm; exact (hx _).trans ((Work.F03.hessian_symmetric he _ _).trans (hx _).symm)
 exact Complex.ext (hv Complex.reCLM) (hv Complex.imCLM)
end Axon
end YM.CF.TableF
end
