import GaugeFieldConstruction.AeneidΛL
import GaugeFieldConstruction.ToneVestRT
import GaugeFieldConstruction.VenusΛL
/-!
 # Aperture. Wick on noncoincident strict.
 # Label & order of p's and κ insert clock sign under original salve.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface NSF.Work.C20 Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
local notation "N"=> τNearRT k
-- permutation route
noncomputable def slipTRt : Equiv.Perm (Fin (n+1)) where
 toFun:= addXRT k (fun i=>i.succ) 0
 invFun:= Fin.cases k.castSucc k.castSucc.succAbove
 left_inv i:=by cases i using Fin.succAboveCases k.castSucc <;> simp [addXRT]
 right_inv i:=by cases i using Fin.cases <;> simp [addXRT]
noncomputable def slipΓTRt (g:Bool): Equiv.Perm (Fin (n+1)):= if g then (N).s.trans (slipTRt k) else slipTRt k
lemma slipBornRt {α:Type*}(g:Bool)(V:Fin n→α)(b:α): Fin.cons (α:=fun _=>α) b V ∘ slipΓTRt k g= (if g then addXRT k V b ∘ (τNearRT k).s else addXRT k V b):=by
 have h: Fin.cons (α:=fun _=>α) b V ∘ slipTRt k = addXRT k V b:=by
    ext1 i; cases i using Fin.succAboveCases k.castSucc <;>simp [slipTRt,addXRT]
 cases g; exact h; exact congrArg (fun V:Fin (n+1)→α=> V ∘ (N).s) h
noncomputable abbrev SlipZRt (k:Fin n)(g:Bool)(v:E4)(p:Points n):= NSF.Points.rearrange (slipΓTRt k g) (YM.Points.cons (p k+v) p)
lemma slipMoveRt (v:E4)(p:Points n): SlipZRt k false v p=κMoverRT k (v,p):= by
 rw [motionKnownRT]; ext1 i; change Fin.cons (α:=fun _=>E4) (p k+v) p.ofLp (slipTRt k i)=_; exact congrFun (slipBornRt k false p.ofLp (p k+v)) i
lemma slipTiltRt (v:E4)(p:Points n): SlipZRt k true v p= (N).switch (SlipZRt k false v p):= by
 ext1 i; rfl
noncomputable abbrev PαXRT (c: ℝ)(o:Full n):= ((c:ℂ)*I,o)
lemma pαDayRT (v:Space3)(s:ℝ)(p:Points n): wickSlice (n+1) (SlipZRt k false (position v s) p) = QchIRt k false (PαXRT s (wickSlice n p)) v:=by
 let o: Points n:= place (NSF.Boundary.trace p) 0; let ν:= κMoverRT k (position v s,p)
 have he(x:Points n)(q:E4): NSF.Boundary.trace (κMoverRT k (q,x))=WithLp.toLp 2 (addXRT k (fun i=>spatial (x i)) (spatial (x k)+spatial q)):=by
    ext1 i; rw [motionKnownRT]; cases i using Fin.succAboveCases k.castSucc <;>simp [NSF.Boundary.trace, addXRT]
 have h: place (NSF.Boundary.trace ν) 0=κMoverRT k (position v 0,o):=by
    unfold ν o; -- trace eq place
    rw [he,motionKnownRT]; ext1 i
    cases i using Fin.succAboveCases k.castSucc <;> refine Mink.ext_by ?_ ?_ <;>simp [addXRT,place,NSF.Boundary.trace]
 have ht: dawn (readings ν)=κMoverRT k (position 0 s,dawn (readings p)):=by
    unfold ν; rw [motionKnownRT,motionKnownRT]; ext1 i; cases i using Fin.succAboveCases k.castSucc <;>refine Mink.ext_by ?_ ?_ <;> simp [addXRT,place,readings,dawn]
 rw [slipMoveRt k,χBornRT, wick_glow,wick_glow]; simp only [mul_I_re,ofReal_im,neg_zero,re_glow,im_glow,mul_I_im,ofReal_re,← ht]; rw [show place (NSF.Boundary.trace ((κMoverRT k) (position v s,p))) 0=_ from h]
lemma pαMoonRT (v:Space3)(s:ℝ)(p:Points n)(g:Bool): wickSlice (n+1) (SlipZRt k g (position v s) p)= QchIRt k g (PαXRT s (wickSlice n p)) v :=by
 cases g; exact pαDayRT ..; rw [slipTiltRt,← wick_name,pαDayRT]; rfl
lemma WKTRiseRT (p:Points n)(t:wickSlice n p∈tube n): p∈ordered n:=by
 rw [wick_glow] at t; change shade _∈fields _ at t; rw [im_glow] at t
 change readings p∈east n
 intro i j h; -- in-order
 have he:= PlushFieldsΛL t i j h; simpa [inside,dawn,place,sub_eq_add_neg] using he
#print axioms pαMoonRT
end YM.NSF.Boundary
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Analysis MeasureTheory Complex Finset YM.Boundary
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20 Metric PortRT
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
variable {Y:NSF.Boundary.Surface (SurfRimL A)}{D:∀ i, NSF.Boundary.Blanket i}{F:NSF.Boundary.Waves (SurfRimL A)}{N:Y.Aurora D}
variable (hz:F.Region (SurfRimL Z))(hu:F.NonTangentialFree Y)(hv:N.FullBody F)
variable (e: PathUL (TotalStarsMars p) (fun n V x => Z n x V))
variable {n:ℕ}(V:Fin n→ΧiMars)
local notation "M_ν" => H.TinCanL
local notation "Φ_H"=> H.TinCanL ∘ V
local notation "Τh" => TouchMΛ H (N:=N)
local notation "Ξ"=> CoffΜΛ H p
local notation "$ΐ"=> RespiteΛL H (N:=N)
variable (k:Fin n)(a:Axis)(i:Axis)
lemma electorTRt (g:Bool): CabinTRt k (TxRT k (CoffΜΛ H p) (H.TinCanL ∘ V) a i) g= H.TinCanL ∘ ((Fin.cons (SkylineΜΛ p i a) V) ∘ (slipΓTRt k g)):=by
 let B:= Fin.cons (α:=fun _=>ΧiMars) (SkylineΜΛ p i a) V
 rw [CabinTRt,TxRT,← slipBornRt]; change (Fin.cons _ _ ∘ _) = _
 rw [← Function.comp_assoc]; congr 1; ext1 b; cases b using Fin.cases <;> rfl
include G hz hv
lemma reactorTRt (g:Bool)(x:Points n)(s:ℝ)(u:Space3)(h:QchIRt k g (PαXRT s (wickSlice n x)) u∈NSF.Boundary.tube (n+1)): RespiteΛL H (N:=N) (Fin.cons (SkylineΜΛ p i a) V) (YM.Points.cons (x k+position u s) x)= TapCoreRt (X:=N) k (CoffΜΛ H p) (H.TinCanL ∘ V) a g (PαXRT s (wickSlice n x)) i u:=by
 rw [← pαMoonRT] at h; let q:= YM.Points.cons (x k+position u s) x; let P:= SlipZRt k g (position u s) x
 have e:P∈NSF.Work.C20.ordered _:= WKTRiseRT P h
 have he:q∈conf (n+1):=by
    intro a b ht; let T:= slipΓTRt k g
    have h(a:Fin (n+1)): P (T.symm a)=q a:=by change q (T (T.symm a))=_; simp
    exact T.symm.injective ((show Injective P.ofLp from ΜConfΛL e) ((h a).trans (ht.trans (h b).symm))) -- tune
 rw [αRespiteΛL H G hz hv _ _ he,← G.symmetry (slipΓTRt k g) _ _ he,← ΥLiveΛL H G hz hv _ e]
 unfold TapCoreRt OriΛTRt; rw [Function.comp_apply,← pαMoonRT]; change _=N.emit (CabinTRt _ _ _) _; rw [electorTRt]
#print axioms reactorTRt
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
