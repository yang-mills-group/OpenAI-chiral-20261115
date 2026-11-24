import GaugeFieldConstruction.StencilEuForecast
import GaugeFieldConstruction.RaysMercuryMars
import GaugeFieldConstruction.StencilFontWorld
/-!
 # SO4 covariance of the descendant label. Not for free inferred from
 covariance of the gauge-sector UV calculation. Only after transporting the
 derivatives on ALL these costs, THEN using rank/spectrum to resolve.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 270000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
variable {n:ℕ}{g:SO}{k:Fin n}{p:Ticket u C}
open FirstPackMars Stage.PlaneL
variable {H:CloudsL} (W:SurfCheckL H) (B:SurfCheckL.boisterL p H)
private abbrev costΞst (H:CloudsL)(Z:Fin n→ΧiMars)(x:Points n):ℂ:= H n x Z
local notation "FΣ"=> costΞst H
local notation "Mκ"=> compassPiMars p g
local notation "MΩ"=> motionMoonMars g
local notation "ρμ"=> parcelMars g.val
variable (p g k)(Z:Fin n→ΧiMars)(x:Points n)(hx:x∈conf n)
include W B hx
lemma cellCostSt (i:Axis): Analysis.D (mirDirYL k i) (costΞst H Z) x=∑ a:Axis,ρμ a i* Analysis.D (mirDirYL k a) (costΞst H (((Mκ)) ∘ Z)) (motionMoonMars g x):=by
 let L:=VoyageMars (n:=n) g; let R:= FΣ ((Mκ) ∘ Z); rw[GermD _ (show FΣ Z=ᶠ[𝓝 x](R ∘ L) from ((conf_open _).eventually_mem hx).mono (fun i t=>(B _ Z i t g).symm))]; unfold D; rw [fderiv_comp x (show DifferentiableAt ℝ R (L x) from ((W.sm ((Mκ) ∘ Z) _ (NSF.Points.move_in _ hx)).contDiffAt ((conf_open _).mem_nhds (NSF.Points.move_in _ hx)) ).differentiableAt (by simp)) L.differentiableAt,ContinuousLinearMap.comp_apply,L.fderiv]; unfold L; rw [show VoyageMars g (mirDirYL k i) =_ from mrColumnMars ..,map_sum]; apply sum_congr rfl; intro j _; rw[map_smul]; exact Complex.real_smul ..
variable {T: GlyphSt}{σ:Axis→UV three}{Λ:Axis→ UV four}(q:DerivativeFontSt (fun n Z x=> H n x Z) T)(h:∀ i,Λ i=Go3PV (σ i))(t:∀ g:SO,∀ i:Axis,compassPiMars p g (Λ i)=∑ b:Axis,parcelMars g.val b i • (Λ b))
noncomputable abbrev ZenAngle_st (T:GlyphSt)(σ:Axis→UV three):UV four:=∑ i:Axis,T i (σ i)
local notation "Aτ"=> ZenAngle_st T σ
include t q h
private lemma orbit_branchSt : H n x (Function.update Z k (ZenAngle_st T σ))= H n (MΩ x) (Function.update (Mκ ∘ Z) k Aτ):=by
 let F':Fin n→ΧiMars:=Mκ ∘ Z
 let B':=((H n (MΩ x)).toLinearMap F' k); let T'(j i:Axis):=B' (T j (σ i))
 have ht:MΩ x∈ conf n:= NSF.Points.move_in _ hx
 let U i:=Function.update Z k (Go3PV (σ i))
 have hm(i:Axis): H n x (Function.update Z k (T i (σ i)))= ∑ a:Axis,∑ b:Axis,(ρμ a i*ρμ b i)*T' a b:=by
    have hp:= (q n k Z i (σ i) hx).trans (cellCostSt g k p W B _ x hx i) -- order!
    let A₁:= ∑ b:Axis,ρμ b i • σ b
    have he:(Mκ ∘ U i)=Function.update F' k (Go3PV A₁):=by
       funext z; unfold U F'; by_cases u:z=k
       · subst z; simp only [Function.comp_apply,Function.update_self]; rw [←h,t]; unfold A₁; rw [map_sum]; simp_rw [map_smul,h]
       simp only [Function.comp_apply, Function.update_of_ne u]
    rw [show ((Mκ) ∘ Function.update Z k (Go3PV (σ i)))=_ from he] at hp
    refine hp.trans (sum_congr rfl fun j _=>?_); change ρμ j i * D _ _ _= _; have hc:= q n k F' j A₁ ht; rw [show D _ (costΞst H (Function.update F' k (Go3PV A₁))) (MΩ x)=_ from hc.symm]; change ρμ j i * (B' (T j A₁))=_; unfold A₁ T'; simp_rw[map_sum,map_smul,smul_eq_mul,mul_sum,mul_assoc]
 change (H n x).toLinearMap Z k Aτ = B' Aτ
 unfold ZenAngle_st; rw [map_sum,map_sum]; change (∑ a:Axis,H n x (Function.update Z k (T a (σ a))))=∑ a:Axis,T' a a
 simp_rw [hm]
 rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_comm]; rw [sum_eq_single a]; swap; -- clarity swap tactic might reorder? update
 · intro b y p
   have hz:(∑ i:Axis,ρμ a i*ρμ b i)=0:= by
      let s:Ortho:=g.val; let A:Matrix Axis Axis ℂ:= fun i j=> ρμ i j
      calc _ = parcelMars (s*s⁻¹) a b := by change _= ofReal ((s.val*(s⁻¹).val) a b); rw [Matrix.mul_apply,Complex.ofReal_sum]; exact sum_congr rfl fun i _=>(Complex.ofReal_mul _ _).symm
           _= _:=by rw [mul_inv_cancel]; simp [parcelMars, Ne.symm p]
   rw [← sum_mul,hz,zero_mul]
 · have hz:(∑ i:Axis,ρμ a i*ρμ a i)=1:= by
      let s:Ortho:=g.val
      calc _ = parcelMars (s*s⁻¹) a a := by change _= ofReal ((s.val*(s⁻¹).val) a a); rw [Matrix.mul_apply,Complex.ofReal_sum]; exact sum_congr rfl fun i _=>(Complex.ofReal_mul _ _).symm
           _= _:=by rw [mul_inv_cancel]; simp[parcelMars]
   rw [← sum_mul,hz,one_mul]
 simp
omit hx
lemma orbitGuideSt : Mκ (ZenAngle_st T σ)= ZenAngle_st T σ:=by
 apply sub_eq_zero.mp; apply W.radar; intro b x hx'; let Z:=![b,Aτ]; let F':=compassPiMars p g⁻¹ ∘ Z; let x':=motionMoonMars g⁻¹ x
 have hF:Mκ ∘ F'=Z:=PiFlowCancelMars g Z
 have ht:x' ∈ conf 2:= NSF.Points.move_in _ hx'
 have hz:= orbit_branchSt g 1 p W B F' x' ht q h t
 rw [show motionMoonMars _ x'=x from (by unfold x'; simpa using LunarwayMars g⁻¹ x),hF,show Function.update Z 1 Aτ=Z from (by ext1 i; fin_cases i <;> simp [Z])] at hz
 change FirstPackMars.CloverRule.sepCost H x _ _=0; rw [← CloverRule.sepPay, map_sub]; apply sub_eq_zero.mpr; rw [CloverRule.sepPay,CloverRule.sepPay]
 apply Eq.trans _ hz; have b₁:= B _ (Function.update F' 1 Aτ) x' ht g
 have ha:Mκ ∘ Function.update F' 1 Aτ=![b,Mκ Aτ]:=by
    funext i; fin_cases i
    · simp only[Function.update_of_ne (show (0:Fin 2)≠1 by decide),Function.comp_apply,Matrix.cons_val_zero]; exact congr_fun hF 0
    · simp [Function.comp_apply,Matrix.cons_val_one]
 rw [show motionMoonMars _ x'=x from (by unfold x'; simpa using LunarwayMars g⁻¹ x),ha] at b₁; exact b₁
-- The K entries of the one-point surface remain zero everywhere. Not just at stage/pads.
omit B p h t
private lemma aloneOneAngle_st {b:ΧiMars}(x:Points 1): H 1 x ![b]=H 1 0 ![b]:=by
 have hf:=W.even (x 0) ![b] (0:Points 1) (show (0:Points 1)∈conf 1 from fun x y _=>Subsingleton.elim x y); rw [show NSF.Points.across (x 0) (0:Points 1) = x from (by apply PiLp.ext; intro b; fin_cases b; exact zero_add ..)] at hf; exact hf
lemma ZenAngleVoid_st (x:Points 1) : H 1 x ![Aτ]=0:=by
 let L:= (H 1 x).toLinearMap ![0] 0; have he(b:ΧiMars){Z:Fin 1→ΧiMars}: Function.update Z 0 b=![b]:=by ext1 i; fin_cases i; rfl
 have hL(b:ΧiMars): H 1 x ![b]= L b:=by change _=H 1 x (Function.update _ _ _); rw [he]
 rw [hL]; unfold ZenAngle_st; rw [map_sum]; apply sum_eq_zero; intro i _; let f:Fin 1→ΧiMars:=![Go3PV (σ i)]; let F:= FΣ f; have hf:= q 1 0 f i (σ i) (x:=x) (show x∈conf 1 from fun _ _ _=>Subsingleton.elim ..)
 rw [he,he] at hf; rw [←hL]; refine hf.trans ?_
 rw [Analysis.D]; change fderiv ℝ F x _=0; rw [show F=fun _:Points 1=> F 0 from funext fun i=>aloneOneAngle_st W q i]; simp
#print axioms ZenAngleVoid_st
#print axioms orbitGuideSt
end YM.GaugeFieldConstruction.Ember.Volumetric
end
