import GaugeFieldConstruction.Zol
import YM.CF.Prism.Homic
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.PMOM
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 45000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open FlightFlux Fluxim
open Labels Source Source.Drops Analysis MultiNext.SignedSource Mom Pattern
open Cube
namespace Axon
local notation "GS"=> SU.group
open AnalyticBridge VerifiedReset Next.Foundations Taxi Lenten Flot
variable {n:Side} {P: BudgetPoint}{X:Scree.Hub n}{Q:InkD n}{T:tangD n}{a c:ℝ}{p w m:ℕ}
-- polynomial representative property local. 
def Blade (k:ℕ)(V:Scree.Hub n)(x:tangD n):Prop:=∃ v: Wheel Axis SU.group.Color, (∀ i, Paper k (v i)) ∧ Agrees V.val.2 (camW V.val.1 v) x
lemma blade_pay (u:m ≤3) (p:0 < m)(v:Blade m X T): screen X.val.2 T∈Maps X.val.1 X.val.2 m:=by
 obtain ⟨L,f,g⟩:=v
 choose F hV hv using fun i=>panels (m-1) (show m-1≤2 by omega) (L i) ((show m-1+1=m by omega).symm ▸ f i)
 refine ⟨F,hV,fun i=>?_⟩; rw [screen_at]; split; rename_i t; · rw [←g i t.1 t.2]; exact (congrFun (hv i.2) _).symm
 rfl
lemma blade_X {v:tangD n}(u:m ≤3)(p:0 < m)(t:v∈Maps X.val.1 X.val.2 m): Blade m X v:=by
 obtain ⟨L,h,g⟩:=t; refine ⟨fun j=> L j ∘ Pattern.xyz,fun i=> (show m-1+1=m by omega) ▸ toE4 (m-1) (by omega) (L i) (h i), fun i e v=>?_⟩; rw [g,if_pos (show needed X.val.2 i from ⟨e,v⟩)]; rfl
lemma extX (f:Wheel Axis SU.group.Color)(i:Cover→SU.group.Color)(e:tangD n)(h:Nonwrapping X.val.2 X.val.1)(p:10 ≤ (More n).val) (x:∀ j, f j=advance j i)(v:Agrees X.val.2 e (camW X.val.1 f)) : Agrees X.val.2 e (VerifiedReset.gradient (i ∘ stem X.val.1)):=by
 intro j a b; rw [v j a b]; unfold camW; rw [x]; unfold advance VerifiedReset.gradient; simp only [Function.comp_apply,stem_f X.val.1 j.1 j.2 (h _ a) p]; rfl -- tune
lemma Ξ_share (x:ComG): gateC X.val.1 P.threshold (P.threshold⁻¹ • x)= camW X.val.1 (formC x):=by
 rw [map_smul]; change P.threshold⁻¹ • (P.threshold • camW _ _)= _; rw [inv_smul_smul₀ P.threshold_pos.ne']
lemma ξT_share(x:Sut)(y:ComT): gateT X.val.1 P.threshold (P.threshold⁻¹ • y)=camW X.val.1 (formT y):=by
 rw [map_smul]; change P.threshold⁻¹ • (P.threshold • camW _ _)= _; rw [inv_smul_smul₀ P.threshold_pos.ne']
variable (p₀:PressB P X Q a c)(z:0≤a)(uX:Nonwrapping X.val.2 X.val.1)(uH:10 ≤ (More n).val)
include p₀ z uX uH
local notation "Xp"=> X.val.2
local notation "o"=> X.val.1
lemma ζball (i:tangD n)(p:Blade 1 X i)(j): ploy Q i j=0:=by
 obtain ⟨u,v,h⟩:=p; obtain ⟨x,y,e⟩:= direction0 v; exact ploy_nil p₀ z (x ∘ stem X.val.1) _ _ (extX u x i uX uH e (fun i v p=> (h i v p).symm))
lemma twoC (i:tangD n)(p:Blade 2 X i): ∃ A:ComG,∀ j:tangD n, ploy Q i j=ploy Q (gateC o P.threshold A) j:=by
 obtain ⟨u,v,h⟩:=p; obtain ⟨x,y,e⟩:= direction1 v
 let A:= mouthV u; let z':= P.threshold; let V:=z'⁻¹ • A; refine ⟨V,fun j=>?_⟩
 have hp: Agrees Xp (i-camW o (formC A)) (VerifiedReset.gradient (x∘ stem o)):=by
    apply extX (fun i=>advance i x) _ _ uX uH (fun i=>rfl); intro j v w; rw [Pi.sub_apply,← h _ v w]; unfold camW; rw [e,Pi.add_apply]; abel
 apply sub_eq_zero.mp; rw [←ContinuousLinearMap.sub_apply,← map_sub,show gateC o P.threshold _=_ from (show gateC o P.threshold V= _ from Ξ_share A)]; exact ploy_nil p₀ z _ _ _ hp -- tune clm.sub_apply
lemma threeC (i:tangD n)(p:Blade 3 X i): ∃ (A:ComG)(B:ComT),∀ j:tangD n, ploy Q i j=ploy Q (gateC o P.threshold A) j+ploy Q (gateT o P.threshold B) j:=by
 obtain ⟨u,v,h⟩:=p; obtain ⟨x,y,e⟩:= direction2 v
 let A:= letterV u; let B:= mouthT u; let z':= P.threshold; let V:= z'⁻¹ • A; let W:=z'⁻¹ • B; refine ⟨V,W,fun j=>?_ ⟩
 have hp: Agrees Xp (i-(camW o (formC A)+camW o (formT B))) (VerifiedReset.gradient (x∘ stem o)):=by
    apply extX (fun i=>advance i x) _ _ uX uH (fun i=>rfl); intro j v w; rw [Pi.sub_apply,Pi.add_apply,← h _ v w]; unfold camW; rw [e,Pi.add_apply, Pi.add_apply]; change _- (formC _ _ _+ formT _ _ _)=_; abel
 apply sub_eq_zero.mp; rw [← ContinuousLinearMap.add_apply,← map_add,← ContinuousLinearMap.sub_apply,←map_sub,show gateC o z' V=_ from Ξ_share A,show gateT o z' W=_ from ξT_share 0 B]; exact ploy_nil p₀ z _ _ _ hp
structure VanishGE(Q:InkD n)(p:BudgetPoint)(Φ:Skye.Seat n)(w:ℕ):Prop where
 unit :lifeH Q 1=0
 κnull :4 ≤ w→ fave p Φ Q=0 -- w largest vanish grade
 znull :5 ≤ w → claw p Φ Q=0
variable (H:VanishGE Q P X.val.1 w)
include H
lemma neckT2 (t:4≤w)(i j:tangD n)(e:Blade 2 X i)(h:Blade 2 X j): ploy Q i j=0:=by
 obtain ⟨A,p⟩:=twoC p₀ z uX uH i e; obtain ⟨B,g⟩:=twoC p₀ z uX uH j h; rw [p, ploy_herm p₀ z,g]; change luke o Q P B A=0; rw [plating_Z p₀ z,H.κnull t]; exact sum_eq_zero fun _ _=>rfl
lemma neckT3(t:5≤w)(i j:tangD n)(e:Blade 3 X i)(h:Blade 2 X j): ploy Q i j=0:=by
 obtain ⟨A,U,p⟩:=threeC p₀ z uX uH i e; obtain ⟨B,g⟩:=twoC p₀ z uX uH j h;
 rw [ploy_herm p₀ z,g,ploy_herm p₀ z,p,ploy_herm p₀ z (gateT o P.threshold U)] -- tune
 change luke o Q P A B + klem o Q P B U=0; rw [plating_Z p₀ z,plating_X p₀ z,H.κnull (by omega),H.znull t]; simp
lemma perch(i j:tangD n)(a b:ℕ)(p:2≤a)(q:2≤b)(t:a+b ≤ w)(P:w ≤ 5)(u:i∈Maps o Xp a)(e:j∈Maps o Xp b) : ploy Q i j=0:=by
 have he: Blade a X i:= blade_X (by omega) (by omega) u; have hg:Blade b X j:=blade_X (by omega) (by omega) e
 rcases show (a=2∧b=2)∨(a=3∧b=2)∨(a=2∧b=3) by omega with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ -- tune orientation subst
 · exact neckT2 p₀ z uX uH H (by omega) i j he hg
 · exact neckT3 p₀ z uX uH H (by omega) i j he hg
 exact (ploy_herm p₀ z _ _).trans (neckT3 p₀ z uX uH H (by omega) _ _ hg he)
end Axon
end YM.CF.TableF
end
