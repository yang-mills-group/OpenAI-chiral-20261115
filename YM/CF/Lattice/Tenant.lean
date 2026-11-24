import YM.CF.Support.Fleet
import YM.CF.Cubes.Refine
import YM.Corona.Fill

/-! Raw inputs and supports on the *refined* torus. -/
set_option autoImplicit false
set_option maxRecDepth 8000
noncomputable section
namespace YM.CF.Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter NormedSpace SU Lat Lattice Branch Cube
attribute [local instance] opCStarAlgebra
variable {N : Side}

def terr (N : Side) : Branch.Field (Site N) := ⟨separation,separation_self,separation_comm,separation_triangle⟩
lemma tract (x : Site N) (i : ℕ) : bay (terr N) x i=halo i {x} := by ext y; rw [bay_mem, halo_spec]; simp [terr]
lemma glen (x : Site N) (i : ℕ) : Grove (terr N) (bay (terr N) x i) := by
  rw [tract]; let B := halo i ({x} : Support N); have hx : x∈B := halo_subset i {x} (mem_singleton_self x)
  apply trunk hx; intro y hy
  have he : Corona.Ships {x} (i+i+1) := fun a ha b hb=> by rw [mem_singleton.mp ha,mem_singleton.mp hb]
  exact Corona.ship_halo i he _ hx _ hy
lemma reach (x : Site N) (m : ℕ) : ((bay (terr N) x m).card:ℝ) ≤ 16*((m:ℝ)+1)^4 := by
  rw [tract]; have he : (halo m ({x}:Support N)).card ≤ (m+m+1)^4 := (Corona.halo_size _ _).trans (by simp)
  have hk : ((halo m ({x}:Support N)).card:ℝ) ≤ ((m:ℝ)+m+1)^4 := by exact_mod_cast he
  exact hk.trans (by rw [show (16:ℝ)*((m:ℝ)+1)^4=(m+m+2:ℝ)^4 by ring]; gcongr; norm_num)
lemma needle : Injective (node (N:=N)) := fun x y h=> (assembly N).embed_injective (add_right_cancel h)
def quota := (16:ℝ)*(Fintype.card (SpinIdx×Slot))
lemma quota_bound : 16≤quota := by
  unfold quota; have h : (1:ℝ) ≤ (Fintype.card (SpinIdx×Slot):ℝ) := by exact_mod_cast Fintype.card_pos
  linarith
abbrev carrier (N : Side) : Model N → Site (More N) := node ∘ Prod.fst
lemma norm_care {Y D G : Type*} (b : Stage (Site (More N)) (Model N) D G) (h : b.F=terr (More N)) (u : b.home=carrier N) : Capacity b quota := by
  refine ⟨?_,?_,?_⟩ <;> intro i j <;> rw [h]
  · exact glen ..
  · exact (reach ..).trans (mul_le_mul_of_nonneg_right quota_bound (by positivity))
  let S := bay (terr (More N)) i j
  let T := board b S
  let A : Finset (Site (More N)×(SpinIdx×Slot)) := S×ˢuniv
  let f := fun x:Model N=>(carrier N x,x.2)
  have he : Injective f := fun _ _ h=> Prod.ext (needle (congrArg Prod.fst h)) (congrArg (fun t:Site (More N)×(SpinIdx×Slot)=>t.2) h)
  have hg : T.card≤A.card := by
    rw [←card_image_of_injective _ he]; apply card_le_card; intro x hx; obtain ⟨t,gt,rfl⟩ := mem_image.mp hx
    apply mem_product.mpr; refine ⟨?_,mem_univ _⟩; change carrier N t∈ S; rw [←u]; exact (mem_filter.mp gt).2
  unfold A at hg; rw [card_product,card_univ] at hg
  apply le_trans (show (T.card:ℝ)≤ S.card*(Fintype.card (SpinIdx×Slot):ℝ) by exact_mod_cast hg)
  rw [quota,mul_right_comm 16]; exact mul_le_mul_of_nonneg_right (reach i j) (by positivity) -- tune unfold

abbrev Input (N : Side) := Bkg (More N) × (Bool→ Site N →Vect)
structure TenantK {N : Side} (x : Input N) : Prop where
  paid : PlaqBound matter (links x.1) (1/60)
  unit : ∀ j y, ‖x.2 j y‖=1
  snug (j) : Slow (links x.1) (x.2 j) compressible.choose
  gap : ‖Cfield (x.2 false)-Cfield (x.2 true)‖ ≤ 1/4
abbrev Own (N : Side) := Subtype (TenantK (N:=N))
def rough (N) (x : Own N) : Bkg N := links x.val.1
def snow (N : Side) (x : Own N) (j : Bool) : Op (Model N) := Cfield (x.val.2 j)
def flipR (g : Site (More N)→E) (x : Input N) : Input N := (gauge g x.1,fun j=>turnX (g ∘ node) (x.2 j))
lemma slow_g (x : Site N→Vect) (U : Bkg N) (p : Site N→E) {r : ℝ} (h : Slow U x r) : Slow (gauge p U) (turnX p x) r := by
  intro y i
  let T := x (y+step i); let a := p y; let c := p (y+step i)
  change ‖turn (a*U _*c⁻¹) (turn c T)-turn a (x y)‖< _
  rw [turn_seq,turn_inv_g,turn_seq,←turn_sub,turn_norm]; exact h y i
lemma flip_own (g : Site (More N)→E) (x : Input N) (h : TenantK x) : TenantK (flipR g x) := by
  let k := g ∘ node (N:=N); refine ⟨?_,?_,?_,?_⟩
  · change PlaqBound _ (links (gauge g x.1)) _; rw [links_g]; exact plaq_gauge _ _ _ h.paid
  · intro j y; change ‖turn _ _‖=_; rw [turn_norm]; exact h.unit ..
  · intro j; change Slow (links (gauge g _)) (turnX k (x.2 j)) _; rw [links_g]; exact slow_g _ _ k (h.snug j)
  have he (j:Bool) : Cfield ((flipR g x).2 j)=congrC (conjG matter k) (Cfield (x.2 j)) := C_gauge ..
  rw [he false,he true, show ∀ (V:UNI (Model N)) (A B : Op (Model N)), congrC V A - congrC V B=congrC V (A-B) from fun V A B=>by rw [congrC,congrC,congrC,mul_sub,sub_mul],congr_norm]; exact h.gap

abbrev Geometry (N : Side) := Site (More N)→E
abbrev toss (g : Geometry N) (x : Own N) : Own N := ⟨flipR g x.val,flip_own g x.val x.property⟩
-- links and pair endpoints are separate currencies
abbrev Edges (N : Side) := Edge (Site N)
def leaks (s : Seal (Site N)) : Finset (Edges N) := univ.filter fun i=>i.1∈s ∧ i.1+step i.2∈s
def news (s : Seal (Site (More N))) : Finset (Site N) := univ.filter fun i=>node i∈s
def vacancy (S : Seal (Site (More N))) (x y : Input N) :=
    (∑ i∈leaks S, ‖color matter (x.1 i)-color matter (y.1 i)‖)+
    ∑ t:Bool,∑ j∈news S, ‖localPair (x.2 t j)-localPair (y.2 t j)‖
lemma vacancy_pos (S : Seal (Site (More N))) (x y : Input N) : 0≤vacancy S x y := by unfold vacancy; positivity
lemma vacancy_inc {S T : Seal (Site (More N))} (h:S⊆T) (x y : Input N) : vacancy S x y≤vacancy T x y := by
  have hp : leaks S⊆leaks T := fun i l=> mem_filter.mpr ⟨mem_univ _, h (mem_filter.mp l).2.1,h (mem_filter.mp l).2.2⟩
  have hh : news S⊆news T := fun i l=> mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp l).2⟩
  exact add_le_add (sum_le_sum_of_subset_of_nonneg hp (fun _ _ _=>norm_nonneg _)) (sum_le_sum fun _ _=>sum_le_sum_of_subset_of_nonneg hh (fun _ _ _=>norm_nonneg _))
def slotK (N : Side) : Stage (Site (More N)) (Model N) (Own N) (Geometry N) :=
  ⟨terr _,carrier N,toss,fun S x y=>vacancy S x.val y.val,fun _ _ _=> vacancy_pos ..,fun h x y=> vacancy_inc h _ _⟩
def sigK (N : Side) : Tag (slotK N) :=
  ⟨fun g=>conjG matter (g ∘ node),fun g i j h=> by
    have he : i.1≠j.1 := fun e=> h (congrArg node e)
    simp [conjG,jump_apply,he]⟩
lemma ample_slots (N : Side) : Capacity (slotK N) quota := norm_care (Y:=Unit) _ rfl rfl

end YM.CF.Tenant
