import YM.SU5.FiniteGaugeData.LocalLimit.Local.Projection
import YM.CF.Continuum.CanalTwo
/-!
# Mirror coordinates back to cover-local paper

At positive buffered support both endpoints of each considered link matter.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Push.GridApprox.BoxGauge
open RG Lattice Wilson Filter MeasureTheory Function Finset CF.Window CF CF.Lat CF.Cube
open scoped Topology BigOperators Classical
variable {G:Gauge}(r:ℕ) {t:Side}(P:Patch)(s:Axis)
local notation "J" => reach P
local notation "M" => More t
local notation "g" => SU.group
section signed
variable (k:Signed)(e:Tab r)
local notation "s'" => k.act e.val.1
local notation "u" => (posDir e.val.2).rotate k
private lemma walk_len : k.act (e.val.1+step e.val.2)= s'+ (u).vec:=by rw [Step.vec_rotate,Step.vec_pos,k.act_add]
def bi :Tab r:= ⟨((posDir e.val.2).rotate k).used (k.act e.val.1),by
 have h : s'∈ box r:=by rw [←box_covariant r k]; exact mem_image_of_mem _ (in_range r e).1
 have he : k.act (e.val.1+step (S:=ℤ) e.val.2)∈ box r:=by rw [←box_covariant r k]; exact mem_image_of_mem _ (in_range r e).2
 rw [walk_len r k e] at he
 generalize u = d at *
 rcases d with ⟨i,a|a⟩; · exact mem_filter.mpr ⟨mem_product.mpr ⟨h,mem_univ _⟩,he⟩
 rw [show (Step.mk i true).vec= -step i from Step.vec_neg (R:=ℤ) i, ←sub_eq_add_neg] at he
 exact mem_filter.mpr ⟨mem_product.mpr ⟨he,mem_univ _⟩, show s'-step i+step i∈box r from (by rw [sub_add_cancel]; exact h)⟩ ⟩

def pivot (U : Space G r) : Space G r := fun e=> if ((posDir e.val.2).rotate k).neg then (U (bi r k e))⁻¹ else U (bi r k e)
private lemma revolve : Continuous (pivot r (G:=G) k):= continuous_pi fun i=> by unfold pivot; split; exact (continuous_apply _).inv; exact continuous_apply _
lemma spin_pivot (g':Cover→ G.El)(x:Space G r) : pivot r k (coversSpace r g' x)= coversSpace r (g' ∘ k.act) (pivot r k x):= by
 funext e; let z: Step:= (posDir e.val.2).rotate k
 simp only [pivot,coversSpace,comp_apply]; rw [walk_len r k e,show (bi r k e).val=z.used (k.act e.val.1) from rfl]
 change (if z.neg=true then _ else _) = _ * (if z.neg=true then _ else _) * (g' (k.act e.val.1+z.vec))⁻¹
 generalize h:z = h' at *; rcases h' with ⟨i,a|a⟩ <;> simp [Step.vec, Step.used,sub_eq_add_neg,mul_assoc]
private lemma wraps (t:Side)(x:Cover)(d:Step): let j:= d.used x; d.used (wrap t x)=(wrap t j.1,j.2):=by
 intro j; cases d with | mk i a=> cases a <;> simp [j,Step.used]
lemma real_pivot (x:Config G t): pivot r k (tabulate r t x)=tabulate r t (Lattice.pull k 0 x):=by
 funext e; unfold tabulate pivot Lattice.pull; simp only [comp_apply]; unfold Step.read base; rw [show (bi r k e).val= ((posDir e.val.2).rotate k).used (k.act e.val.1) from rfl]; simp only [affine,wrap_signed,add_zero]; rw [wraps]

def reflected (F:paper G r):paper G r:= ⟨star ∘ (F.val ∘ pivot r k),by
 let t:= paid r F; exact ⟨(t.1.comp_env (revolve r k).measurable).starC,fun g' x=> congrArg star (by unfold comp; rw [spin_pivot,t.2 ..])⟩ ⟩
lemma mirror (A:paper g r) : paint r t (reflected r (Signed.mirror s) A) = θBack s (paint r t A) := by
 ext i:1; apply congrArg star; exact congrArg A.val (real_pivot ..)
end signed

variable (V: paper g r)
def Sees : Prop := ∀ (x y : Space SU.group r),
 (∀ i:Tab r,(reach P:ℤ) < i.val.1 s → (reach P:ℤ) < (i.val.1+step i.val.2 : Cover) s → x i = y i) → V.val x=V.val y
lemma m_gate (p:r+J<t.val)(z:Sees r P s V): ξTape s P t (paint r (More t) V) :=by
 let Y:= buffered s P t
 have he (x:Cover)(v:x∈ Lattice.box r)(h:(reach P:ℤ)< x s): wrap (More t) x∈ Y:= by
    have ht:= (box_test.mp v).2 s; have hp:0≤x s:=by omega
    have hu:(wrap M x s)=((x s).toNat: ZMod (M).val):=by change ((x s:ℤ): Per M)=_; rw [←Int.cast_natCast, Int.toNat_of_nonneg hp]
    refine mem_filter.mpr ⟨mem_univ _,?_⟩; rw [hu, ZMod.val_natCast_of_lt (by change _<t.val*2; omega)]; omega
 let A:= within (t:=More t) r V
 refine ⟨A.gauge,A.borel,fun k' t h=>?_ ,A.cost⟩
 exact z _ _ (fun i p q=> h (base r _ i) (he i.val.1 (in_range r i).1 p) (by simpa [base] using he _ (in_range r i).2 q))
end YM.Push.GridApprox.BoxGauge
