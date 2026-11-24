import GaugeFieldConstruction.Persimmon
/-!
# Weak transfer limit of products
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6800
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy Empire Fathom Payroll Function Filter Set TopologicalSpace YM.Analysis MeasureTheory Points Bulb Palace Module RawBank Stage Row
open Floor Wick Invoice Gap Sailing
open scoped Topology BigOperators ContDiff
open Phys Flux.One
attribute [local instance] iG iF iX iU iT2 iW2 iV iS

lemma pure_x (a b : Bundle) (i k): Calibration.deriv i ((totalIx (a*b)).val.val k)= packΘ a.1 a.2 (basis i) ((totalIx b).val.val k):= by
  let v:=(totalIx b).val.val k; let u:=(totalIx (a*b)).val.val k
  let j:= Calibration.deriv i v
  have he:∑ x: Axis,((basis i x:ℝ):ℂ) • Calibration.deriv x=Calibration.deriv i:=by
    simp only [basis_eq, apply_ite, ite_smul, Complex.ofReal_one,Complex.ofReal_zero,one_smul,zero_smul]; simp
  let Q:= packΘ a.1 a.2 (basis i) v; unfold packΘ; rw [he,LinearMap.comp_apply];
  apply Prod.ext; rfl
  apply Prod.ext
  · apply Subtype.ext; change P_g i (u.2.1.val)= a.1 • P_g i v.2.1.val
    have hp : u.2.1.val=a.1 • v.2.1.val := by change (a.1*b.1) • bead.val k=a.1 • b.1 • _; rw [smul_smul] -- adjust
    rw [hp,map_smul]
  apply Prod.ext; ext1 x; apply Subtype.ext
  · change P_f i (u.2.2.1 x).val=a.2 x.1 • P_f i (v.2.2.1 x).val
    have t (w:SymT) : (w.val k).2.2.1= Flavor.bundle_ (fun j=> (w.val k).2.2.1 (j,0,0)):= faded (V:=UF four) (w.val k).2.2.1 fun g=>congr_arg (fun p:UV four=>p.2.2.1) ((w.property.1 k).2 g)
    have hp:(u.2.2.1 x).val=a.2 x.1 • (v.2.2.1 x).val:= by
      unfold u v; rw [t,t (totalIx b).val]; unfold Flavor.bundle_; split_ifs
      · change (a.2 x.1*b.2 x.1) • strand.val k = a.2 x.1 • b.2 x.1 • strand.val k; rw [smul_smul]
      exact (smul_zero _).symm
    rw [hp,map_smul]
  ext1 x; apply Subtype.ext; change Row.P_x i (u.2.2.2 x).val=(0:J Row.x)
  have h:= (Submodule.mem_bot ℂ).1 (u.2.2.2 x).property; rw [h,map_zero]

variable {X : Type*} {ℱ : Filter X} {S : City} {q:X→Carat}
    (H : Blush S ℱ q) {P:Axis→Across} {L : Sheds S P} (C:Supplies L)
local notation "Ls"=> Tot S P L

variable (g : Scope L) 
def trade (Q : Carat) (x y:Ls): Ls:= Q.κ⁻¹^4 • C.heart g x y

def earning (Q:Carat): Ls→ₗ[ℂ] SymT := Q.t.symm.toLinearMap ∘ₗ (Ls).subtype
lemma earned (Q:Carat) {t:Ls} : (Q.t (earning Q t))=t.val:=Q.t.apply_symm_apply t.val
lemma earnsC (Q:Carat) (x : Tot S P L): earning Q (sbar L x)=tbar (earning Q x):= by
  apply Q.t.injective; rw [earned,← Q.tbar_c,earned]; rfl
lemma ex_out (Q:Carat) (x y:Ls) (i j): levelP P Q i ((earning Q (trade C g Q x y)).val j)= hip C Q x i ((earning Q y).val j):= by
  apply (lens Q five).injective
  rw [show lens Q five=(Q.G five).c from rfl,vert]; unfold hip; rw [vert]
  suffices E:P i _=C.theta (Q.κ⁻¹ ^4 • x) i _ from congr_arg (fun p:UV five=> Q.κ • p) E
  rw [← Q.t_pay,←Q.t_pay,earned,earned]; change P i (Q.κ⁻¹^4 • (C.heart g x y).val.val j)=_; rw [map_smul, C.wanted, map_smul]; rfl
private instance : Module.Finite ℂ ↥SymT:=finiteInvariant ..

def atp (A : Across): SymT→ₗ[ℂ] Raw.Sym→ UV five := LinearMap.pi fun i=> A ∘ₗ LinearMap.proj i ∘ₗ SymT.subtype

lemma bill_true (i:Axis): Injective (atp (Calibration.deriv i)) := by
  apply LinearMap.ker_eq_bot.mp; refine LinearMap.ker_eq_bot'.mpr fun x h=> solo_d i x ?_; intro v
  have H: Calibration.deriv i (x.val v)=0:= congr_fun h v; rw [H,map_zero,map_zero]
variable [ℱ.NeBot]
include H
lemma beats (x y:X→Ls) (a b) (v : Dips ℂ ℱ (fun k=> earning (q k) (x k)) (totalIx a).val) (w : Dips ℂ ℱ (fun k=> earning (q k) (y k)) (totalIx b).val) : Dips ℂ ℱ (fun k=> earning (q k) (trade C g (q k) (x k) (y k))) (totalIx (a*b)).val := by
  let T k:= earning (q k) (trade C g (q k) (x k) (y k))
  let V k:=earning (q k) (y k)
  let i : Axis:=0
  have ht k:Dips ℂ ℱ (fun p=>atp (levelP P (q p) i) k) (atp (Calibration.deriv i) k) := dots (h:=fun a=>dept L H.toViews i (k.val a))
  apply (ringed ht (bill_true i)).2 T
  apply dots; intro j
  change Dips ℂ _ (fun k=> levelP P (q k) i ((T k).val j) ) (Calibration.deriv i ((totalIx _).val.val j)); unfold T; simp_rw [pure_x,ex_out]
  refine trav (pledge H C x a v i) (fun k=> (V k).val j) ((totalIx _).val.val j) ?_
  exact maps w (LinearMap.proj j ∘ₗ SymT.subtype)
lemma survives (x:X→ Tot S P L) (Z) (p:Dips ℂ ℱ (fun k=> earning (q k) (x k)) Z): divergence Z=0:= by
  apply Sailing.individual (trav (downstairs L H.toViews) _ _ p) (show Dips ℂ ℱ _ 0 from ?_) -- check order
  refine constant (fixed (0:OneW)) (Eventually.of_forall fun k=>?_)
  change 0=left₃ L (q k) (earning (q k) (x k)); unfold left₃; change _=(q k).κ • (q k).w.symm (Bend.sum _ L.toBend ((q k).t _)); rw [earned,show Bend.sum P L.toBend (x k).val=0 from (x k).property,map_zero,smul_zero]
end YM.GaugeFieldConstruction.Ember
