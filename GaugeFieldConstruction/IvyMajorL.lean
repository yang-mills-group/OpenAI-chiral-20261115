import GaugeFieldConstruction.CasimirMars
/-!
# Detecting prices of any U4 cold readers directly

 No rotational conclusions needed. Only same-U4 probes applied. phrase in Test costs so ports align true plenum budgets.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S)
open Wick Mirror Invoice Raster
local notation "l₄"=> Calibration.lift four
def ProbeIvL : Type := Foil × ΧiMars
lemma billboardL (x y:ΧiMars): silky (l₄ x) (l₄ y)=boast (couples (shells four x) (shells four y)):=by
 change boast (couples (shells five _) (shells five _))=_ -- tune
 rw [show shells five (l₄ x)=shells four x from LinearMap.congr_fun (shell_lift four) x, show shells five (l₄ y)=shells four y from LinearMap.congr_fun (shell_lift four) y]
def prismColdL: ΧiMars→ₗ[ℂ] ProbeIvL→ ℂ:= LinearMap.pi fun x=> survey x.1 ∘ₗ silky (l₄ x.2) ∘ₗ l₄
lemma rainColdL : Injective prismColdL:=by
 apply (detect _).mpr; intro x h
 have t(b:ΧiMars) : couples (shells four b) (shells four x)=0:= empt (fun j=> by
    change boast _ _=0; rw [← billboardL]; exact h (j,b))
 by_contra! e; have hp:= mirror_positive four x e; rw[t,map_zero] at hp; simp at hp
noncomputable def DawnSheetL (S:City)(Q:Carat): ΧiMars→ₗ[ℂ] ProbeIvL→ ℂ:= LinearMap.pi fun x=> survey x.1 ∘ₗ lunar S Q (l₄ x.2) ∘ₗ l₄
lemma springSheetL {X: Type*} {ℱ: Filter X}{q:X→Carat}(v: Views S ℱ q): Scores ℂ ℱ prismColdL (fun k=> DawnSheetL S (q k)):=fun k i=> v.pair ..
lemma stampSheetL {X:Type*}[Nonempty X]{ℱ:Filter X}[ℱ.NeBot]{q:X→Carat}(v:Views S ℱ q)(x:ΧiMars)
    (h:∀ (f:Foil) (t:ΧiMars), S.spot (other (l₄ t)) front (l₄ x) f.p=0): x=0:=by
 obtain ⟨z,H⟩:= (insight rainColdL (springSheetL v)).1.exists
 apply ((q z).G four).c.symm.injective; rw [map_zero]; refine (detect _).1 H _ (fun b=>?_); rcases b with ⟨o,i⟩
 change lunar S _ (l₄ i) _ _=_; rw [lucid,Carat.include_,Carat.include_,LinearEquiv.apply_symm_apply]; exact h ((q z).u.rolled o) (((q z).G four).c i)
open FirstPackMars
-- Cyrus formulas shared beyond p where T other Table. Build compact register here. let n.Name
abbrev CloudsL := ∀ n:ℕ,Points n → MultilinearMap ℂ (fun _:Fin n=> ΧiMars) ℂ
noncomputable def CloudMeanL : CloudsL:= fun i x=> if e: x∈conf i then linearGownMoon p Y _ e else 0
lemma CoronaPL (F:Fin n→ΧiMars)(x:Points n)(h:x∈conf n):CloudMeanL p Y n x F=TerraMars p Y F x:=by rw [CloudMeanL,dif_pos h]; rfl
-- detector from both selected & mean paired costs; enough for W rank
abbrev tastePairL (Z:CloudsL)(f: ΧiMars) (b: ΧiMars): Points 2→ℂ:= fun x=> Z 2 x ![b,f]
def uncloudL (Z:CloudsL): Prop:= ∀ f: ΧiMars,(∀ (b:ΧiMars),EqOn (tastePairL Z f b) 0 (conf 2)) → f=0
lemma sunnyProbeL (V: Views S atTop u) : uncloudL (CloudMeanL p Y):=by
 intro f h; apply stampSheetL V; intro t b
 rw[spot_cost,show update (other (l₄ b)) front ((l₄) f)= l₄ ∘ ![b,f] from ?_]
 · rw [BillingMars p Y]; exact ((YM.Test.weak_null (TerraSm _ _ _).continuousOn).mpr fun x e=>(CoronaPL p Y _ _ e).symm.trans (h b e)) _
 ext1 i; fin_cases i <;> simp [front,other]
#print axioms sunnyProbeL
end YM.GaugeFieldConstruction.Ember.Volumetric
