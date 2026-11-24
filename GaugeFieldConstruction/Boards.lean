import GaugeFieldConstruction.Nubs
import GaugeFieldConstruction.Centre

/-!
# Inputs to a triangle. All the intertwiners in the f stress (97).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Cauchy Row Phys Function Submodule U1 Calibration Floor Raw Gap Wick
open scoped BigOperators
open Matter (Slot FlavorIndex)

abbrev PW := J Pen
abbrev FW := J Mode
abbrev sectionG (c : Pig) (i j : Axis) := Phys.atop c (F i j)
abbrev sessionF (c : Slot) (i : Spin) := Phys.atop c (C i 0)
abbrev rad (s : Slot) := Flavor.tagged s.2
lemma one_income (i j : Slot) (p : Bool→ℂ) : Matter.coeffs (Flavor.bundle_ p) i j = if i=j then p (rad i) else 0 := by
  rw [Flavor.wear]; unfold Flavor.bundle_; split_ifs with h x y <;> try simp_all
  all_goals grind
lemma tale (p : Bool → J f): graph_f (Flavor.bundle_ p)=∑ i:Slot,sD i i (p (rad i)) := by
  ext1 ⟨⟨a,i⟩,⟨c,d⟩⟩
  rw [Finsupp.finsetSum_apply]; have ht:= pocket_f a c i d (Flavor.bundle_ p); rw [test,Finsupp.lapply_apply] at ht; rw [ht]
  have h (u:Slot) : sD u u (p (rad u)) ((a,i),(c,d)) = if u=i ∧ u=d then p (rad u) (a,c) else 0 := by simpa only [test,Finsupp.lapply_apply] using bank_f i d a c u u (p (rad u));
  simp_rw [h]
  have he : (fun k=> (Flavor.bundle_ p k) (a,c))= Flavor.bundle_ (fun i=> p i (a,c)) := by funext k; unfold Flavor.bundle_; split_ifs <;> rfl
  rw [he,one_income]; simp [ite_and]

/-- Preserve both allocations for the uncolored pair. -/
lemma gPalette (i j : Axis) : graph_g (Gauge97.bill i j)=(1/2:ℂ) • ∑ p : Pig, ∑ l : Axis,
    (times' (sectionG p i l) (sectionG p j l)+times' (sectionG p j l) (sectionG p i l)) := by
  simp_rw [Gauge97.bill,Gauge97.bill.P_pair,Bose,graph_g,LinearMap.smul_apply,LinearMap.sum_apply,map_sum,map_add,yD,straps]

lemma lout (i : Slot) (a : Axis) (x y:CJet) : sD i i (L a (times' x y))=
    times' (atop i x) (stride true a (atop i y))-times' (stride false a (atop i x)) (atop i y) := by
  rw [L,split_legs,map_add,sD,straps,straps]; unfold stride; rw [← here,← here]; simp only [LinearMap.neg_apply,map_neg]; abel
lemma degreeP (i) (a b : Axis) : sD i i (L b (B a)) =∑ k:Spin,∑ l:Spin,Hij a k l •
    (times' (sessionF i k) (stride true b (sessionF i l))-times' (stride false b (sessionF i k)) (sessionF i l)) := by
  simp_rw [B,map_sum,map_smul,lout]

abbrev plain (i j ac V) := dress (shells four ((stress ac V).val (ordered i j))) -- Order arg types?
lemma pin₁ (i j ac V) : (plain i j ac V).1=0:= rfl
lemma pin₂ (i j ac V) : (plain i j ac V).2.2.2=0:= by
  rw [plain,dressX]; let x:= (stress ac V).val (ordered i j)
  have h : (shells four x).2.2.2=0:= funext fun v=> (Submodule.mem_bot ℂ).mp (x.2.2.2 v).property -- adjust
  rw [h,map_zero]

def gStress (c : ℂ) (i j : Axis) := c • graph_g ((1/4:ℂ) • Gauge97.recorded i j)
def fStress (V : Bool→ℂ) (i j : Axis) := ∑ k:Slot,V (rad k) • ((-1/64:ℂ) • sD k k (L j (B i)+L i (B j)))
lemma pinG (i j ac V) : (plain i j ac V).2.1=gStress ac i j := by
  rw [plain,dressG]; unfold gStress; rw [← map_smul,← Gauge97.ordered_bill]; rfl
lemma pinF (i j ac V) : (plain i j ac V).2.2.1=fStress V i j := by
  rw [plain,dressF]; let f (b : Bool) := V b • ((-1/64:ℂ) • (U1.Spin97.element i j))
  let z:= shells Floor.four ((stress ac V).val (ordered i j))
  let t := (stress ac V).val (ordered i j)
  have h : z.2.2.1=Flavor.bundle_ f := by
    have he g := congr_arg (fun p : UV four=>p.2.2.1) ((stress ac V).property.1 (ordered i j) |>.2 g)
    have hv:= faded (V:=UF four) t.2.2.1 (fun g=>he g)
    funext k
    change (t.2.2.1 k).val= _; conv_lhs=> rw [hv]
    unfold Flavor.bundle_; split_ifs
    · have ht: ((liftF (stress ac V) k.1).val (ordered i j))=(t.2.2.1 (Calibration.first k.1)).val := rfl
      change (t.2.2.1 (Calibration.first k.1)).val=_
      rw [← ht,lift2]
      change V k.1 • ((-1/64:ℂ) • (Spin97.Root _))=f k.1; rw [Spin97.element_o]
    rfl
  rw [h,tale]; apply Finset.sum_congr rfl; intro k _; unfold f Spin97.element; rw [add_comm,map_smul,map_smul]

end YM.GaugeFieldConstruction.Flux.One
