/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.ContrastDeriv
import GaugeFieldConstruction.StencilGlyph
import GaugeFieldConstruction.EurekaΛL
set_option autoImplicit false
set_option synthInstance.maxSize 10050
set_option maxHeartbeats 280000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open NSF.Boundary NSF.Boundary.WOrder NSF.Work.C20
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n:ℕ}{S:City}{P:Axis→Empire.Across}{L:Sheds S P}{Cu:Supplies L}{u:ℕ→Carat}
open FirstPackMars Loft Cell
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)(U:GlyphSt)
variable (q:DerivativeFontSt (fun n V x=> Z n x V) U)
variable {Y:NSF.Boundary.Surface (SurfRimL A)}{D:∀ i, NSF.Boundary.Blanket i}{F:NSF.Boundary.Waves (SurfRimL A)}{N:Y.Aurora D}
variable (hz:F.Region (SurfRimL Z))(hv:N.FullBody F)(hN:NSF.Bid.cones Y)(uN:F.NonTangentialFree Y)
variable (V:Fin n→ΧiMars)(k: Fin n)(a:Axis)(I:UV three)
local notation "γ" => (Wickγ a)
include G hz hv q
lemma priceFullGlyphSt{x:NSF.Boundary.Full n}(u:x∈NSF.Boundary.tube n): TouchMΛ H (N:=N) (Function.update V k (Go3PV I)) k a x= γ * ΑΛL H (N:=N) (Function.update V k (U a I)) x:=by
 let J:= TouchMΛ H (N:=N) (Function.update V k (Go3PV I)) k a;let L:=ΑΛL H (N:=N) (Function.update V k (U a I)); apply sub_eq_zero.mp;apply ΛLaneL (X:= J-γ • L) (AnalyticOnNhd.sub (ΥFeelΛL H hv _ _ _) (analyticOnNhd_const.mul (ΑSenseΛL H hv _))) _ u
 intro x h; change TouchMΛ H (N:=N) _ k a _-γ * ΑΛL H (N:=N) _ _ = 0; rw [PhasePressΛL H G hz hv _ _ _ h, ΥLiveΛL H G hz hv _ h, show Z _ x (Function.update V k (U a I))= _ from q n k V a I (ΜConfΛL h),sub_self]
local notation "cX" => H.TinCanL
include hN uN
lemma worldGlyphSt :
 γ • Y.W n (cX ∘ Function.update V k (U a I))= -(Y.W n (cX ∘ Function.update V k (Go3PV I)) ∘L DriftΛL (mirDirYL k a)):=by
 exact (tube_contrast ((Carries_W hv hN uN _).scale γ) ((Carries_W hv hN uN _).mink (mirDirYL k a))).1 (fun _ w=>(priceFullGlyphSt H G U q hz hv V k a I w).symm)
lemma worldMovesSt (V:Fin n→NSF.Boundary.Letter (SurfRimL A))(f: Test4):
  γ * Y.expect (List.ofFn (Function.update V k (cX (U a I),f))) = - Y.expect (List.ofFn (Function.update V k (cX (Go3PV I),ΦshiftΛ (basis a) f))) :=by
 simp_rw [NSF.Work.C29.expectOfFn,Function.comp_update]
 let v:= (cX).symm ∘ (Prod.fst∘ V)
 have he(b:ΧiMars): Function.update (Prod.fst∘ V) k (cX b)= cX ∘ (Function.update v k b):=by ext1 i; by_cases h:i=k <;> simp [*,v]
 let f':= Function.update (Prod.snd ∘ V) k f
 change γ * Y.W n (Function.update (Prod.fst∘ V) k (cX (U a I))) (Joint.materialize n f')=-(Y.W n (Function.update (Prod.fst∘ V) k (cX (Go3PV I))) (Joint.materialize n (Function.update (Prod.snd∘ V) k (ΦshiftΛ (basis a) f))))
 rw [he _,he _]; have ht:= DFunLike.congr_fun (worldGlyphSt H G U q hz hv hN uN v k a I) (Joint.materialize n f');change γ * Y.W n (cX ∘ Function.update v k (U a I)) (Joint.materialize n f')= -(Y.W n (cX ∘ Function.update v k (Go3PV I)) (DriftΛL (mirDirYL k a) (Joint.materialize n f'))) at ht; rw [ht,show DriftΛL _ _=_ from spotTestΛL a f' k]; simp [f']
omit G hz hv q hN uN in
private lemma glyphInsertSt {m n : ℕ} {α : Type*} (v : Fin m → α) (w : Fin n → α) (x y : α) :
    Function.update (Fin.append v (Fin.cons x w)) (Fin.natAdd m 0) y = Fin.append v (Fin.cons y w) := by -- C29 argument
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have h : Fin.castAdd (n+1) i ≠ Fin.natAdd m 0 := by
      apply Fin.ne_of_lt
      exact (show i.val < m + 0 by simp)
    simp [h]
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.natAdd_inj]
lemma uptoGlyphSt (x y:Sentence (SurfRimL A))(f:Test4): γ * Y.expect (x++(cX (U a I),f)::y) = - Y.expect (x++(cX (Go3PV I),ΦshiftΛ (basis a) f)::y):=by
 let L : Letter (SurfRimL A):= (cX (U a I), f)
 have h:= worldMovesSt H G U q hz hv hN uN (Fin.natAdd x.length 0) a I (Fin.append x.get (Fin.cons L y.get)) f; simpa only [glyphInsertSt,List.ofFn_fin_append,List.ofFn_cons,List.ofFn_get] using h
lemma fieldGlyphSt {R:Fields (SurfRimL A)}(e:R.Total)(J:StarOp (SurfRimL A))(d:R.sharpPair J)(m:R.realizes Y)(f:Test4):
 R.field (cX (U a I)) f = - γ ⁻¹ • R.field (cX (Go3PV I)) (ΦshiftΛ (basis a) f):=by
 apply DrivesΛL R e; intro l; apply ΓEyesΛL R e; intro k
 change inner ℂ (R.evaluates k) (R.evaluates ((cX (U a I),f)::l)) = inner ℂ (R.evaluates k) ((-γ⁻¹) • R.evaluates ((cX (Go3PV I),ΦshiftΛ (basis a) f)::l))
 have hzzy (l): inner ℂ (R.evaluates k) (R.evaluates l)=Y.expect (Sentence.rev J k ++ l):= R.general Y m J d k l
 rw [inner_smul_right,hzzy,hzzy,neg_mul]; linear_combination (norm:=field_simp [wickLiveL]<;> ring) (γ)⁻¹*(uptoGlyphSt H G U q hz hv hN uN a I (Sentence.rev J k) l f)
#print axioms fieldGlyphSt
end YM.GaugeFieldConstruction.Ember.Volumetric
end
