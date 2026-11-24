import YM.CF.Buffered.MidRoll
/-! # One reflection of arbitrary mark configuration -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 530000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered Cin Stripe Tile Traversed Stack Bays Saddle
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast Function
attribute [local instance] opCStarAlgebra
variable {n v B l m p:Side} {δ:Axis→Side}{i:Axis}{ζ:TStem i}
namespace Stampu
variable (V:Traversed ζ δ n) (t:Fin n.val)
abbrev FaceM (δ:Axis→Side) := Rail δ → Bool
def half (t:Fin n.val)(x:Fin n.val):Bool:= decide ((x-t).val<n.val/2)
def mirrored (t:Fin n.val)(x:Fin n.val) := (x-t).rev + t
def pivot (V:Traversed ζ δ n)(t:Fin n.val)(x:Rail δ):= loc V (mirrored t (lead V x)) (tail V x)
def base (s:Bool)(Z:FaceM δ)(x:Rail δ):= if half t (lead V x)=s then Z x else Z (pivot V t x)
lemma pivot_across (x:Fin n.val)(c:Car ζ) : pivot V t (loc V (t+x) c)=loc V (t+x.rev) c:=by unfold pivot mirrored; rw [lead_loc, tail_loc,add_sub_cancel_left,add_comm]
lemma pivot_twice (x:Rail δ) : pivot V t (pivot V t x)=x:=by unfold pivot mirrored; rw [lead_loc, tail_loc,add_sub_cancel_right,Fin.rev_rev,sub_add_cancel,V.parts]
lemma pivot_alt (h:Even n.val)(x: Rail δ) : half t (lead V (pivot V t x))= !(half t (lead V x)):=by
 unfold pivot half mirrored; rw [lead_loc,add_sub_cancel_right, Fin.val_rev]; obtain ⟨p,e⟩:=h; have ht:= (lead V x-t).isLt; have hs:0<n.val:=n.property; rw [← decide_not]; congr 1; ext; omega
lemma painted (h:Landing δ)(S:Badge v B)(x:Rail δ): S.reflected (pivot V t x)=(S.reflected x).reflect i:=by
 nth_rw 1 2 [← V.parts x]; let v:=(lead V x-t); let c:= tail V x; have he:t+v=lead V x:=by unfold v; abel
 change S.reflected (pivot V t (loc _ (lead V x) c))=(S.reflected (loc _ (lead V x) c)).reflect i; rw [← he,pivot_across]; unfold Badge.reflected; rw [pigment, pigment];
 have hv : (t+v.rev).val%2=1 ↔ ¬(t+v).val%2=1:=by have ht:=h i; rw [← V.own] at ht; obtain ⟨g,h⟩:=ht; rw [Fin.val_add_eq_ite,Fin.val_add_eq_ite,Fin.val_rev]; have hl:= v.isLt; split_ifs <;> omega -- tune
 split_ifs <;> first|tauto|rw [Badge.stencil_at (p:=tint_off c),Badge.back]|rw [Badge.stencil_at (p:=tint_off c)]

variable {e x:ℝ} (K: Ticket m v B p e x) (Z: Badge v B) (q:Clip)(β u:ℝ)
local notation "C" => Car ζ
local notation "N" => Rail δ
local notation "U" => curve v B V
local notation "Q" => fluid ζ v B
local notation "d" => EdgePorts ζ v B
local notation "Xq" => Wet ζ v B
local notation "A" => FaceM δ

def paint (f:FaceM δ)(i:Rail δ): Badge v B:= if f i then Z.reflected i else 1
-- use half(t) true = retain pos, choose unflipped interior for pos orientations (may not be odd-even but ∫ unchanged)
def formT (S:A) :=record K (paint Z S) q β u V (fun k=> half t k) -- positive=true e
section price
variable [MeasurableSpace (EdgePorts ζ v B)] [DiscreteMeasurableSpace (EdgePorts ζ v B)]
local notation "η" k => Measure.prod (Measure.count : Measure (Film.Leaf (k+1) d)) Q

def powerK (S:FaceM δ)(k:ℕ)(z: Fin n.val): Kern (η k):= Batch.transfer (formT V t K Z q β u S z) Q Q (upper ζ v B) k
variable (L:Landing δ)(v':0 ≤ u) (S:FaceM δ)
include L v'
local notation "τ" => n.val

lemma casting (S: FaceM δ) : Tendsto (fun k=> Kern.τ (Kern.roll (recur (powerK V t K Z q β u S k)) τ)) atTop (𝓝 (prism δ K (paint Z S) q β u)):=by
 rw [at_batch K _ _ _ u V (half t) L v']; refine (Batch.support_layer _ U Q Q).congr ?_; intro j; exact Batch.is_total _ U _ _ j (V.own.symm ▸ landing_ge L i) -- tune
private lemma fareK :
 let U'(S:FaceM δ)(k):= powerK V t K Z q β u S k; let F:=base V t true S; let G:=base V t false S
 ∀ k, ‖Kern.τ (Kern.roll (recur (U' S k)) τ)‖^2 ≤ ‖Kern.τ (Kern.roll (recur (U' F k)) τ)‖*‖Kern.τ (Kern.roll (recur (U' G k)) τ)‖:=by
 intro f P T k; let a: A→ Fin n.val→ C → Badge v B:=fun S x=> paint Z S ∘ loc V x
 have same (X Y:A)(i:Fin n.val)(x:a X i= a Y i): f X k i=f Y k i:=by
    unfold f powerK formT record; rw [show paint Z X ∘ _= paint Z Y ∘ (loc V i) from x]
 have vp:Even n.val:= V.own.symm ▸ L i
 refine Kern.reflect_rect _ _ _ vp t (l:=n.val/2) ?_ ?_; · obtain ⟨x,h⟩:=vp; omega
 intro i' h
 let x:= t+i'; let y:= t+i'.rev
 have hp : half t x=true:=by unfold half x; simpa using h
 have hv : half t y=false:=by
    let u:Rail δ:=loc V x 0; have he:= pivot_across V t i' 0; have t:=pivot_alt V t vp u; rw [show pivot V _ u=loc V y 0 from he,lead_loc,show lead V u=x from lead_loc ..,hp] at t; exact t
 have hf(v:C):(pivot V t (loc V x v))=loc V y v:= pivot_across ..
 have hg(v:C):(pivot V t (loc V y v))=loc V x v:=by rw [←hf]; apply pivot_twice
 have look (v₁ v₂:Fin n.val)(B':A)(g:∀ i:C, B' (loc V v₁ i)= S (loc V v₂ i))(h:∀ i:C,loc V v₁ i=pivot V t (loc V v₂ i))(e:half t v₁= !(half t v₂)): f B' k v₁ = star (f S k v₂):=by
    unfold f powerK formT record; dsimp only; rw [e]; refine Batch.is_reverse _ _ Q Q (Saddle.backwards K (a S v₂) q β u _ V L (a B' v₁) ?_) (upper ζ v B) upper_v _
    intro r z; unfold a paint; simp only [comp_apply,g r]; split_ifs; swap; · exact (theta_one _).symm
    rw [h r,painted V t L Z, Badge.thus]
 refine ⟨same P S x (funext fun j=>?_),look y x P (fun j=> ?_) (fun j=> (hf j).symm) (hv.trans (by rw [hp]; rfl)),same T S y (funext fun j=> ?_),look x y T (fun j=> ?_) (fun j=>(hg j).symm) (hp.trans (by rw [hv]; rfl))⟩ <;> simp [a,P,T,hp,hv,paint,base,V.lead_loc,hf,hg]
lemma cauchy : let h (S:FaceM δ):= ‖prism δ K (paint Z S) q β u‖
 h S^2≤ h (base V t true S)* h (base V t false S):= le_of_tendsto_of_tendsto' ((casting V t K Z q β u L v' S).norm.pow _) (((casting V t K Z q β u L v' _).norm).mul (casting V t K Z q β u L v' _).norm) (fareK V t K Z q β u L v' S)
end price
end Stampu
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Stampu.cauchy
