import GaugeFieldConstruction.Fleck
import GaugeFieldConstruction.Horizon
import GaugeFieldConstruction.Stars

/-!
# Q2 statuses for transfer. Point-space in one frame. Rank witnesses in
 real theory produced later by the scaled-comparison theorem. Complex
 bilinear on complexifications (Q2 permits this extension).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6500
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy Row LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Module Record
open Floor
open scoped Topology BigOperators ContDiff
local instance iG (d : Floor) : AddCommGroup (UG d):= @Submodule.addCommGroup ℂ (J g) _ _ _ _
local instance iF (d : Floor) : AddCommGroup (UF d):= @Submodule.addCommGroup ℂ (J f) _ _ _ _
local instance iX (d : Floor) : AddCommGroup (UX d):= @Submodule.addCommGroup ℂ (J x) _ _ _ _
local instance iU (d : Floor) : AddCommGroup (UV d):= inferInstanceAs (AddCommGroup (Prod _ _))
local instance iT2:AddCommGroup ↥SymT:= @Submodule.addCommGroup ℂ (Raw.Sym→UV four) _ _ _ _
local instance iW2:AddCommGroup ↥OneW:= @Submodule.addCommGroup ℂ (Axis→UV five) _ _ _ _
local instance iV : AddCommGroup ↥BothV:= @Submodule.addCommGroup ℂ (Raw.VS → UV five) _ _ _ _
local instance iS (P : Axis→Across) (u : Bend P): AddCommGroup ↥(LinearMap.ker (Bend.sum P u)):= @Submodule.addCommGroup ℂ _ _ _ _ _
variable {n : ℕ}
abbrev City := Palace (UV five)
variable (S : City)
local notation "l4" => Calibration.lift Floor.four
abbrev pens (t : SymT) := fun (i j : Axis)=> t.val (ordered i j)
def prints (t : SymT) : placard (UV five) := fun i j=> l4 (pens t i j)
lemma printing (t : SymT) (i j:Axis) : prints t i j=prints t j i:=by rw [prints,prints,pens,pens]; rw [ordered_swap i j] -- check
structure Sheds (S : City) (P : Axis→Across) extends Bend P where
  money (i:Axis) (b : UV four) (n : ℕ) (x:Fin n→UV five) (k:Fin n) : S.spot x k (P i b)=paid k i (S.spot x k (l4 b))
  realD i b: shade _ (P i b)=P i (shade _ b)
  /- Need possibly also grade3 preservation. Not used to deliver full exterior stress generator U4/5 property. May refine lift. -/

abbrev Tot (P : Axis→Across) (p : Sheds S P) := LinearMap.ker (Bend.sum P p.toBend)
variable {S} {P : Axis→ Across} (p : Sheds S P)
lemma stand (x : Fin n→UV five) (t : Tot S P p) : Conserves (S.armed (prints t.val) x) where
  maps i j:= by simp only [armed,printing _ i j]
  levy j:= by
    have ht : ∀ i :Axis,paid 0 i (S.armed (prints t.val) x i j)= S.tagged x (P i (pens t.val i j)) := fun i=> (p.money i (pens t.val i j) _ (Fathom.add 0 x) 0).symm
    have he : (Bend.sum P p.toBend t.val).val j=0:=congr_fun (congr_arg Subtype.val (show Bend.sum P p.toBend t.val=0 from t.property)) j
    simp_rw [ht]; rw [← map_sum, show (∑ i:Axis,P i (pens t.val i j))=0 from (Bend.payW _ _ _).symm.trans he, map_zero]

-- charge conjugation of stress. no notational `star` instance. T subtype.
def tbar : SymT →ₛₗ[Cauchy.Conj.bar] SymT where
  toFun t:= ⟨fun i=> shade four (t.val i), by
    constructor
    · intro i; constructor
      · change Cauchy.Conj.bar (t.val i).1=0; rw [(t.property.1 i).1,map_zero]
      intro g; change flavors _ g (shade _ _)=_; rw [← color_s, (t.property.1 i).2 g]
    intro i s; change spinFrame four s (shade _ _) = _; rw [← comp_s,t.property.2]
    change shade _ (pay _ _)=pay _ (shade _ _); cases symAct.cost s i <;> simp⟩
  map_add' _ _:= Subtype.ext (funext fun _=> map_add ..)
  map_smul' a x:= Subtype.ext (funext fun i=>LinearMap.map_smulₛₗ _ a (x.val i))
def sbar (p : Sheds S P): Tot S P p→ₛₗ[Cauchy.Conj.bar] Tot S P p:= (tbar ∘ₛₗ (Tot S P p).subtype).codRestrict _ (fun t=>by
  rw [LinearMap.mem_ker]; apply Subtype.ext; ext1 j; rw [Bend.payW]; change (∑ i:Axis,P i (shade _ _))=(0:UV five)
  simp_rw [← p.realD]; rw [← map_sum,← Bend.payW p.toBend]; change shade five ((Bend.sum P p.toBend t.val).val j)=0; rw [ show Bend.sum P p.toBend t.val=0 from t.property]; exact (shade _).map_zero)
lemma sbar_cost (t : Tot S P p) (i): (sbar p t).val.val i=shade _ (t.val.val i):=rfl
lemma sbar_twice t: sbar p (sbar p t)=t:=Subtype.ext (Subtype.ext (funext fun i=>clear (d:=four) (t.val.val i)))

structure Supplies (p : Sheds S P) where
  theta : Tot S P p→ₗ[ℂ] Axis→Across
  Y (d : Floor): Tot S P p→ₗ[ℂ] (Ortho.Skew→ₗ[ℝ] (Module.End ℂ (UV d))) -- replace smul inferred
  /- Obtain symbol representations from (89). -/
  bend t : Bend (theta t)
  reality i t b: shade _ (theta t i b)= theta (sbar p t) i (shade _ b)
  law t b i: Reaches S (prints t.val) (postage i) (l4 b) (theta t i b)
  decree (d Ω t b): Reaches S (prints t.val) (rpm Ω) (Calibration.lift d b) (Calibration.lift d (Y d t Ω b))
  -- Q2 normalizations and H-action. fill later in furnishing, only need 4/5.

variable (S) in
def check (v : Fin n→UV five) (k : Fin n): (OneW×BothV)→ₗ[ℂ](Axis × Axis)→Bond n:= LinearMap.pi fun x=>
  ((∑ i:Axis,paid k i ∘ₗ S.spot v k ∘ₗ LinearMap.proj ((x.1,ordered i x.2):VS)) ∘ₗ BothV.subtype ∘ₗ LinearMap.snd ..) - paid k x.1 ∘ₗ S.spot v k ∘ₗ LinearMap.proj x.2 ∘ₗ OneW.subtype ∘ₗ LinearMap.fst ..
lemma audit (S:City) (v : Fin n→UV five) (k) (A : OneW × BothV) (b j:Axis): check S v k A (b,j)= (∑ i:Axis,paid k i (S.spot v k (A.2.val (b,ordered i j))))-paid k b (S.spot v k (A.1.val j)) := by
  change (∑ i:Axis,paid k i ∘ₗ S.spot v k ∘ₗ (LinearMap.proj ((b,ordered i j):VS))) A.2.val - _=_ -- infer
  rw [LinearMap.sum_apply]; rfl
def around (P : Axis→Across) (q : Bend P) : SymT →ₗ[ℂ] (OneW×BothV) := LinearMap.prod (Bend.sum P q) (Bend.cents P q)
lemma trail (v : Fin n→UV five) (k): LinearMap.range (around P p.toBend)≤LinearMap.ker (check S v k):= by
  rintro _ ⟨w,rfl⟩; rw [LinearMap.mem_ker]; ext1 ⟨b,j⟩; rw [audit]
  change _-_= (0: Bond n); apply sub_eq_zero.mpr
  change (∑ i: Axis, paid k i (S.spot v k (P b (pens w i j))))=paid k b (S.spot v k ((Bend.sum P p.toBend w).val j))
  rw [Bend.payW,map_sum,map_sum]; exact Finset.sum_congr rfl fun i _=>by rw [p.money,p.money,both]

/-- Microscope requests *just* one other field, any plenum pair test p keeping room for shell including three nested cutoffs. Set second slot as address x. Prove there's many; scaling will take a packet to packet. -/
abbrev front : Fin 2 := (1:Fin 2)
abbrev other (w: UV five) :Fin 2 → UV five := ![w,0]

structure Foil where
  p : Test 2
  plen : tsupport p ⊆ generic 2
  a : Bulb
  b : Bulb
  c : Bulb
  u : Works a p front
  v : Works b p front
  w : Works c p front
  q : Before b a
  r : Before c b
  luck (x : Points 2) : x∈ tsupport p → ∀ z : E4,z ∈ a.run → ∀ i:Axis,x 0 i≠ z i
abbrev Probe := Foil×UV five
section
variable (S)
def survey (f : Foil) : Bond 2 →ₗ[ℂ] ℂ := LinearMap.applyₗ f.p -- check
def readTest : (OneW×BothV) →ₗ[ℂ] Probe→Axis×Axis→ℂ := LinearMap.pi fun a=> LinearMap.pi fun k=> survey a.1 ∘ₗ LinearMap.proj k ∘ₗ check S (other a.2) front
end
lemma read_v (f : Foil) (w) (x : OneW × BothV) (i j): readTest S x (f,w) (i,j)=check S (other w) front x (i,j) f.p :=rfl
lemma kernelChain : LinearMap.range (around _ p.toBend) ≤ LinearMap.ker (readTest S):= fun x hx=> by
  rw [LinearMap.mem_ker]; ext1 ⟨q,w⟩; ext1 ⟨i,j⟩
  have ht:= trail p (other w) front hx; rw [LinearMap.mem_ker] at ht; rw [read_v,ht]; rfl
-- desired result of transfer on same S unselected.
structure Scope (p : Sheds S P) : Prop where
  /- all follow from Rank hypotheses on the survey with Wick pricing. -/
  first (k : Axis) (t : SymT): (∀ i,P k (t.val i)=0) → t=0
  second (k : Axis) (t : SymT): (∀ i v (f:Foil), paid front k (S.spot (other v) front (P k (t.val i))) f.p=0)→t=0
  short (x : UV five): (∀ v (f:Foil), S.spot (other v) front x f.p=0) →x=0
  rank : 59 ≤ Module.finrank ℂ (LinearMap.range (readTest S))
  diverg : 4 ≤Module.finrank ℂ (LinearMap.range (Bend.sum P p.toBend))
lemma precedes (u:Scope p): Injective (around P p.toBend) := by
  intro t w h; apply sub_eq_zero.mp; apply u.first 0; have ht : Bend.cents _ p.toBend (t-w)=0:= by rw [map_sub]; exact sub_eq_zero.mpr (congr_arg Prod.snd h)
  intro i
  exact congr_fun (congr_arg Subtype.val ht) (0,i)
private instance : Module.Finite ℂ ↥SymT := finiteInvariant ..
private instance : Module.Finite ℂ ↥BothV := finiteInvariant ..
private instance : Module.Finite ℂ ↥OneW := finiteInvariant ..
lemma kernel_full (u : Scope p) : LinearMap.ker (readTest S)=LinearMap.range (around _ p.toBend) := by
  have ht:= LinearMap.finrank_range_add_finrank_ker (readTest S)
  have he:= u.rank
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_le (kernelChain p)
  rw [LinearMap.finrank_range_of_inj (precedes p u),sym_count]; rw [Module.finrank_prod,vector_count,pair_count] at ht; omega
lemma counts (u : Scope p): 1 ≤ Module.finrank ℂ (Tot S P p) ∧ Module.finrank ℂ (Tot S P p) ≤3:=by
  have he:= u.diverg; have ht:= LinearMap.finrank_range_add_finrank_ker (Bend.sum _ p.toBend)
  have hp:= Submodule.finrank_le (LinearMap.range (Bend.sum _ p.toBend)); rw [sym_count] at ht; rw [vector_count] at hp; unfold Tot; omega
end YM.GaugeFieldConstruction.Ember
