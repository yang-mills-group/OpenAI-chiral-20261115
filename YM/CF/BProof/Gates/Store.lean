import YM.CF.BProof.Gates.Permit

/- non-y choices. Purchase sufficient mark tides & healthy (Stew). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gates
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing
open scoped Topology BigOperators Classical MatrixOrder Matrix
local notation "G"=> SU.group
variable (K:Chart G)(P: Pub G)
-- closed gaps measure uses tax caps on Filed and Θ, not chart-space licenses. make one struct.
def charter (F:Face.Design) (v C:ℝ) : Prop := ∀ᶠ y:ℝ in atTop,∀ {s:Side} (S:Hall s)(a : Per s) (l:ℕ), S.K=K→ S.X=F→ Face.Sized v S.g y S.k → F.k₀≤ S.k → sizeP y≤2*(l:ℝ) →
    ∀ U:Config G s,∀ b:Eyes s,lifts a l y S U b →
      let r:= Face.blendR F K S.g; let m:= C*mA y; (∀ i,Face.Firm S.K (outlook a l S U b i) r m) ∧ r≤ S.K.size ∧ max (qoriz (r:=r) (m:=m) S) (qnorm (r:=r) l S)+4*xi y ≤ thresh y/2
structure Scene (K:Chart G)(F:Face.Design) where
 size : ℝ -- Lf
 target : 1≤size
 costM : ℝ
 cost_pos : 0<costM
 firm : charter K F size costM
 charge : ℝ
 mono : 0<charge
 home : ∀ᶠ y:ℝ in atTop,∀ i:TAxis, group.chord (Mag.comm y (Mag.f₁ i) (Mag.f₂ i)) + 4*xi y ≤ charge*mA y ∧ charge*mA y ≤ thresh y/2
 C : ℝ -- healthy labels price at distance-four disks
 true_p : 0<C
 view : ∀ᶠ y:ℝ in atTop, ∀ (s:Side)(U:Face.Sheet s)(p:Space s), (∀ i, cd G (Mag.comm y (Mag.f₁ i) (Mag.f₂ i)) (Face.read U p i)≤ 4*wc y) → ∀ i, Face.Mood K y U p (Face.orient K y U p i) ∧ cd G (Face.orient K y U p i) (Mag.center i) ≤ C*Face.fine y
lemma render (F:Face.Design) : Nonempty (Scene K F):= by
 obtain ⟨v,h,C,hC,K₁⟩:=(price_N K F).exists; obtain ⟨t,ht,H⟩:= calm_D_p K; obtain ⟨a,b,p⟩:= Face.launch_face K (D:=4) (by norm_num); exact ⟨v,h,C,hC,K₁,t,ht,H,a,b,p⟩ -- name center before

structure Stage (c:Clip)(w R v:ℝ) where
 W : 0<w
 T : 0≤R
 V : 0≤v
 K : Chart G
 P : Pub G
 F : Face.Design
 scene : Scene K F
 κ : ℝ
 κ_pos : 0<κ
 margin : κ< 1/16
 tiny : K.C*κ ≤1
 height : ℝ -- Taylor error constant
 ink : ∀ᶠ y:ℝ in atTop,Ink K height y
 ms : ℝ
 cost : 0<ms
 license : ∀ᶠ y:ℝ in atTop, ∀ p:BudgetPoint,p.threshold=thresh y→ ValidR c p (Charge.reach ms y)
 uniform : NPL (fun y=> Weights.rent y (Charge.reach ms) R w v)
-- chart may come from Grace but unrelated. static.
lemma fix (F:Face.Design)(c:Clip)(w R v:ℝ)(h:0<w)(u:0≤R)(e:0≤v): ∃ S:Stage c w R v,S.K=K∧ S.F=F∧ S.P=P:= by
 obtain ⟨p⟩:=render K F; obtain ⟨d,⟨hp,he⟩,hq⟩:=(Eventually.and (store_valid c) (rates_buy w R v h u e)).exists; obtain ⟨b,hb⟩:=(ink_w K).exists
 let t:= min (K.C)⁻¹ (1/32); have ht:0<K.C:= one_pos.trans_le K.C_one; exact ⟨⟨h,u,e,K,P,F,p,t,lt_min (inv_pos.mpr ht) (by norm_num), (min_le_right ..).trans_lt (by norm_num),(mul_le_mul_of_nonneg_left (min_le_left ..) ht.le).trans_eq (mul_inv_cancel₀ ht.ne'), b,hb,d,hp,he,hq⟩,rfl,rfl,rfl⟩ -- tune r of store_valid
end YM.CF.BProof.Gates
