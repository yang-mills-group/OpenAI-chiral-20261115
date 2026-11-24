import YM.CF.Vp929.Contour.Form
import YM.CF.Vp929.Contour.Germs
import YM.CF.Vp929.Contour.Display
import YM.CF.Vow.Move
import YM.CF.Ione.Lean
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate
open Forge Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Vow Salt
open Ione Beau Haro Cascade
open scoped Mew
open Mew
variable {X Y:Type*}{n:Side}{P:BudgetPoint}{h v w:ℝ}{F:RegBudget n}{K:ForceBudget n}{t:Cusp n}
namespace Display
open Jet
variable {H:Submodule ℝ (X→ℝ)}{A:Type}[NormedAddCommGroup A][NormedSpace ℝ A]{L:X→tangD n→ℂ}{V:X→A→ℂ}
lemma signs (o:Seat n)(T:∀ (j:ℕ),j≤P.order→∀ d:Fin j→ tangD n,∀ p:ℂ→L[ℝ]ℝ,(fun x=> p (iteratedFDeriv ℝ j (L x) 0 d))∈ H): Display H (fun x=> Signs P o (L x)):=by
 let B(j:ℕ): Set (Fin j→tangD n):={v|∀ i,P.dirBound o (v i)}
 let U:= (j:Fin (P.order+1))× B j.val; let F(t:U)(x):=iteratedFDeriv ℝ t.1.val (L x) 0 t.2.val
 refine (Display.sup fun a:U=> captures (F a) fun p=> T a.1.val (Nat.le_of_lt_succ a.1.isLt) a.2.val p).hull _ ?_
 rintro x ⟨c,b⟩ u; exact ⟨fun h=> ⟨h.grade,fun t=> h.token t.1.val (Nat.le_of_lt_succ t.1.prop) t.2.val t.2.prop⟩,fun ⟨v,w⟩=>⟨v,b.paid,fun j hj z hz=> w ⟨⟨j,Nat.lt_add_one_of_le hj⟩, z,hz⟩⟩⟩
lemma tins {k:ℕ}(z:A)(T:∀ (i:ℕ),i≤k→∀ v:Fin i→A,∀ p:ℂ→L[ℝ]ℝ,(fun x=> p (iteratedFDeriv ℝ i (V x) z v))∈ H): Display H (fun x=> Pence k (V x) z) := by
 let U(x)(i:Fin (k+1)):=iteratedFDeriv ℝ i.val (V x) z; let W(i:Fin (k+1)) :ℝ:=1^(i:ℕ) / i.val.factorial
 have hw(i):0≤W i:= by unfold W; positivity
 have hv (i:Fin (k+1)): Display H (fun x b=> ‖U x i‖≤ b):= by
    let D(v:Fin i.val→ A):= ∏ j:Fin i.val, ‖v j‖
    let F(v)(x):= (D v)⁻¹ • U x i v; have hu(v): 0 ≤ D v:= by unfold D; positivity
    refine (Display.sup fun v=> captures (F v) fun p=>?_ ).hull _ ?_
    swap
    · rintro x _ b; constructor; · intro h; refine ⟨(norm_nonneg _).trans h,fun v=>?_⟩; have a0:= (U x i).le_opNorm v; unfold F; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (hu v))]; by_cases he:D v=0; rw [he, inv_zero,zero_mul]; exact (norm_nonneg _).trans h; exact (inv_mul_le_iff₀ (Ne.lt_of_le (Ne.symm he) (hu v))).mpr (a0.trans (by unfold D; rw [mul_comm _ b]; exact mul_le_mul_of_nonneg_right h (hu v)))
      rintro ⟨s,g⟩; refine ContinuousMultilinearMap.opNorm_le_bound s fun v=>?_ ; specialize g v; unfold F at g; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (hu v))] at g; by_cases he:D v=0; simpa [show ∏ j:Fin i.val, ‖v j‖=0 from he] using (U x i).le_opNorm v; exact (inv_mul_le_iff₀ (Ne.lt_of_le (Ne.symm he) (hu v))).mp g |>.trans_eq (mul_comm ..)
    exact T i.val (Nat.le_of_lt_succ i.isLt) v (p.comp ((D v)⁻¹ • ContinuousLinearMap.id ℝ ℂ))
 apply (drug hv (fun (_:Unit) i=> W i) (fun _ i=> hw i)).hull; rintro x ⟨u,v⟩ b; have hp: potash 1 k (V x) z= ∑ i, W i *‖U x i‖:= (Fin.sum_univ_eq_sum_range (fun i=> noble 1 i (V x) z) (k+1)).symm; refine ⟨fun u=>⟨fun i=> ‖U x i‖,fun i=>le_rfl,fun _=>hp ▸ u.earned⟩, fun ⟨y,p,t⟩=>⟨v.smooth,hp.trans_le ((sum_le_sum (fun i _=> mul_le_mul_of_nonneg_left (p i) (hw i))).trans (t ()))⟩⟩
variable (A0:Scree.Hub n){Z:X→InkD n}{W:X→ Copy n}(J:Force n)(Y D:Support (More n))(T:Set (Pane n))(u:0 < h)
-- Uniform representations of charges.
abbrev regPrice (H:Submodule ℝ (X→ℝ))(Z:X→InkD n)(p:BudgetPoint):Prop:=∀ U∈ T,∀ i:Finset (Dwell n),∀ (j:ℕ), j≤ p.order → ∀ v: Fin j→tangD n,∀ y:ℂ→L[ℝ]ℝ,(fun x=> y (iteratedFDeriv ℝ j (fun d:tangD n=> crumb (Z x (increment U d)).val i) 0 v))∈ H
abbrev markPrice (H:Submodule ℝ (X→ℝ))(W:X→ Copy n)(p:BudgetPoint)(K: Set (Orbit n))(press:Orbit n→ tangD n→ Pane n) := ∀ U∈ K,∀ i:Finset (Dwell n),∀ (j:ℕ),j≤p.order → ∀ v:Fin j→ tangD n, ∀ y:ℂ→L[ℝ]ℝ,(fun x =>y (iteratedFDeriv ℝ j (fun d:tangD n=>crumb (W x (press U d,U.2)).val i) 0 v)) ∈ H
abbrev Rink (p:BudgetPoint)(X: Support (More n)):= {U: Pane n | pingS p.threshold X U}
local notation "D'"=> Finset (Dwell n)
include u
lemma rolls (p: regPrice (Rink P A0.val.2) H Z P): Display H (fun x=> PressB P A0 (Z x) h):=by
 let V:=Rink P A0.val.2; let o:= A0.val.1; let F(U:V)(i:D')(x:X):= fun d:tangD n=> crumb (Z x (increment U.val d)).val i
 refine (drug (fun i=> Display.sup fun u:V=>Display.signs (L:=F u i) o (p u.val u.prop i)) (fun (_:Unit)=> Scree.tariff P o h) (fun _ i=>by unfold Scree.tariff; positivity)).hull _ ?_
 rintro x ⟨c',v⟩ b; refine ⟨fun k=> ?_, fun ⟨g,r,h'⟩=> {v with worth:=⟨g,fun i=>(r i).1,fun U vT i=> (r i).2 ⟨U,vT⟩,h' ()⟩}⟩; obtain ⟨c,h,f,v⟩:=k.worth; exact ⟨c,fun i=> ⟨h i,fun t=> f _ t.prop i⟩,fun _=> v⟩
abbrev Fink(p:BudgetPoint)(X:Support (More n)):= {U:Orbit n| U.1∈ Rink p X}
lemma rarest (p:markPrice H W P (Fink P (J.val.1.val.2 \ J.val.2)) (fun U d=> increment U.1 (openG P J.val.2 d))) : Display H (fun x=> ForceB P J (W x) h):=by
 let V:= Fink P (J.val.1.val.2\J.val.2); let o:= J.val.1.val.1; let F(U:V)(i:D')(x:X):= fun d:tangD n=> crumb (W x (increment U.val.1 (openG P J.val.2 d),U.val.2)).val i
 refine (drug (fun i=> Display.sup fun u:V=>Display.signs (L:=F u i) o (p u.val u.prop i)) (fun (_:Unit)=> Scree.tariff P o h) (fun _ i=>by unfold Scree.tariff; positivity)).hull _ ?_
 rintro x ⟨c',v⟩ b; refine ⟨fun k=> ?_, fun ⟨g,r,h'⟩=> {v with costP:=⟨g,fun i=>(r i).1,fun U vT i=> (r i).2 ⟨U,vT⟩,h' ()⟩}⟩; obtain ⟨c,h,f,v⟩:=k.costP; exact ⟨c,fun i=> ⟨h i,fun t=> f _ t.prop i⟩,fun _=> v⟩
open Wray
lemma award (p:∀ T:Support (More n),D⊆T→ markPrice H W P (Fink P (Y\D)) (fun U d=>pressQ P T U.1 d)) : Display H (fun x=> Medal P Y D (W x) h):=by
 let V:= Fink P (Y\D); let I':= ↥V × { T:Support (More n)// D⊆T}; let F(U:I')(i:D')(x):= fun d:tangD n=> crumb (W x (pressQ P U.2.val U.1.val.1 d,U.1.val.2)).val i
 refine (drug (fun (i:D')=> Display.sup fun j:I'=> tins (k:=P.order) (V:=F j i) 0 (p j.2.val j.2.prop j.1.val j.1.prop i)) (fun (_:Unit) i=> stake h i) (fun _ i=>by unfold stake; positivity)).hull _ ?_
 rintro x ⟨c',v⟩ b; refine ⟨fun k=> ?_, fun ⟨g,r,h'⟩=> ⟨v.toThemeR,g,fun i=> (r i).1,?_,h' ()⟩⟩
 · obtain ⟨c,h,f,v⟩:=k.pays; exact ⟨c,fun i=>⟨h i,fun j=> (f j.1.val j.1.prop j.2.prop).haveP i⟩,fun _=> v⟩
 intro U u T d; obtain ⟨k,t,p,_⟩:=v.pays; exact ⟨(p U u d).own,fun i=> (r i).2 (⟨U,u⟩,⟨T,d⟩)⟩
end Display
end YM.CF.Py.Rate
