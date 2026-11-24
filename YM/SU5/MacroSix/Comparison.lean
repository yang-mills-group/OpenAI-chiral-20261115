import YM.SU5.MacroSix.ReflectedPocket
import YM.SU5.MacroSix.Product

/-! # The prices in the comparator: Structural and physical use of Ward

Ward in the assigned comparators, not only on the gauge-invariant observables. But suffice
EITHER raw factor marginal, on gauges taking the prescribed values through
pockets (and can take identity throughout other bodies). See also author's related
Selected/Cor/Rubric.lean (for a different class of factors and costs); the
center eigen test proof is adapted from there using the same SU & inverse Ward.
Keep exact center `star` for the chosen BIRTH pocket (on creation). Pays for link-size
receipts on all Pane. No normalization transfer between probe or course indices.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 460000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Pockets
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure
  Next.SectorChange Common Fock Satin Tapestry Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP
attribute [local instance] opCStarAlgebra

section center
local notation "γ" => SU.central
variable {K : Calibration}{S T U V : Finset Cover}{b : Bool} (g : GVertex)
variable {f : Family K} {i : SpinIdx} {j : SU.Slot} {x : Cover}
local notation "ξ" => star (centerPay b)
lemma living_circle (h : f∈ living K b S) (p : ∀ i∈ S,g i=γ) : Circular S g f (ξ • f) := by
  refine Submodule.span_induction (p:=fun f _ ↦ Circular S g f (ξ • f)) ?_
    (by rw [smul_zero]; exact fun _ _ _ _ ↦ (map_zero _).symm)
    (fun _ _ _ _ p q ↦ by rw [smul_add]; exact Circular.add g S p q)
    (fun a _ _ h ↦ by rw [smul_comm]; exact Circular.scale g S h a) h
  rintro _ ⟨x,i,k,h,u,e,rfl⟩ N t v W
  let a := basisC (K.c N) x i k
  change create a = twist (quantU _) (ξ • create a)
  rw [twist_scalar,twist_create]; unfold a; rw [turn_basisC, v _ u,p _ u,SU.by_charge,sum_eq_single k]
  · rw [Matrix.diagonal_apply_eq,paysTag k,e,map_smul,smul_smul,scale_unit_self (center_scale _),one_smul]
  · intro j _ h; rw [Matrix.diagonal_apply_ne _ h,zero_smul]
  simp

lemma dying_circle (h : f∈ dying K b S) (p : ∀ i∈ S,g i=1) : Circular S g f f := by
  refine Submodule.span_induction (p:=fun f _ ↦ Circular S g f f) ?_
    (fun _ _ _ _ ↦ (map_zero _).symm) (fun _ _ _ _ p q ↦ Circular.add g S p q)
    (fun a _ _ h ↦ Circular.scale g S h a) h
  rintro _ ⟨x,i,k,h,u,e,rfl⟩ N t v W
  let a := basisC (K.c N) x i k
  change Fock.remove a = twist (quantU _) (Fock.remove a)
  rw [twist_remove]; unfold a; rw [turn_basisC,v _ u,p _ u]
  simp [Matrix.one_apply]

lemma stamp_circle (h : f∈ stamp K b U V) (u : U⊆ S) (v : V ⊆ S) (p : ∀ i∈ U,g i=γ)
    (q : ∀ i∈ V,g i=1) : Circular S g f (ξ • f) := by
  refine Submodule.span_induction (p:=fun f _ ↦ Circular S g f (ξ • f)) ?_
    (by rw [smul_zero]; exact fun _ _ _ _ ↦ (map_zero _).symm)
    (fun _ _ _ _ p q ↦ by rw [smul_add]; exact Circular.add g S p q)
    (fun a _ _ h ↦ by rw [smul_comm]; exact Circular.scale g S h a) h
  rintro _ ⟨x,h,y,t,rfl|rfl⟩
  · rw [←Algebra.smul_mul_assoc]
    exact Circular.mul g S (largerGauge u (living_circle g h p)) (largerGauge v (dying_circle g t q))
  rw [←Algebra.mul_smul_comm]; exact Circular.mul g S
    (largerGauge v (dying_circle g t q)) (largerGauge u (living_circle g h p))

variable {A : Dome K}
lemma trivial_acts (h : A∈ bay K S true) (e : ∀ i∈ S, g i=1) : pennant K g A=A := by
  have ht := pennantTrace K S 1 h
  rw [pennantId] at ht
  exact appointed K S g _ _ (fun N t v ↦ ht N t (fun i u ↦ (v i u).trans (e i u))) h

local notation "Φ" => pennant K g
lemma colored_stamp (h : A.val ∈ stamp K b U V) (p : ∀ i∈ U,g i=γ) (q : ∀ i∈ V,g i=1) :
    pennant K g A= (star (centerPay b)) • A := by
  let S := U∪V; let u : U⊆ S:= Finset.subset_union_left; let v : V⊆ S:= Finset.subset_union_right
  exact appointed K S g A _ (stamp_circle g h u v p q)
    ((bay K S true).smul_mem (stamp_test h u v) _)
lemma pure_stamp (h : A.val ∈ stamp K b U V) : A∈ Mantle K := by
  intro N i y; obtain ⟨a,h,u⟩ := stamp_paid N h
  exact (u i).trans (u y).symm
end center

section comparison
variable {K : Calibration} {M : Prices K} {S T U V : Finset Cover} {b : Bool}
variable {f g : Dome K} {z : ℂ} (p : GVertex)
local notation "Φ" => pennant K p
local notation "ξ" => star (centerPay b)

-- any eligible pure product pieces of the summand, tested at that gauge
-- using C-linear Pennant only. Whole product summand may be assumed singlet;
-- then get the gauge Ward option with no Ward hypothesis on matter marginal.
def census (K : Calibration) (z : ℂ) (p : GVertex) : Submodule ℂ (Dome K) :=
  Submodule.span ℂ { f | ∃ x∈ Gate K, ∃ y∈ Mantle K, pennant K p y=z • y ∧ f=x*y}
lemma census_here {x y : Dome K}(h : x∈ Gate K) (g : y∈ Mantle K) (e : Φ y=z • y) :
    x*y∈ census K z p := Submodule.subset_span (show _ ∈ _ from ⟨x,h,y,g,e,rfl⟩)
lemma enroll (h : f.val ∈ ribbon K S b U V) (u : U⊆ S) (v : V⊆ S)
    (t : ∀ i∈ U,p i=SU.central) (e : ∀ i∈ V,p i=1) : f ∈ census K ξ p := by
  let Q := census K ξ p
  let A := (screenHall K).val.toLinearMap
  have he : ribbon K S b U V ≤ Q.map A := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x,h,z,a,rfl⟩
    let y : Dome K:= ⟨x,broadCompile _ _ (stamp_test h u v)⟩
    refine ⟨markInk K a * y,?_,rfl⟩
    exact census_here p (ink_mem K a) (pure_stamp h) (colored_stamp p h t e)
  obtain ⟨y,g,e₀⟩:= he h
  exact (show y=f from Subtype.ext e₀) ▸ g
lemma enroll_more (h : f∈ census K z p) (u : g∈ bay K S true) (t : ∀ i∈ S,p i=1) :
    f*g ∈ census K z p := by
  let D:= census K z p
  refine Submodule.span_induction (p:=fun f _ ↦ f*g∈ D) ?_
    (by rw [zero_mul]; apply D.zero_mem)
    (fun _ _ _ _ p q ↦ by rw [add_mul]; exact D.add_mem p q)
    (fun a _ _ h ↦ by rw [Algebra.smul_mul_assoc]; exact D.smul_mem _ h) h
  rintro f ⟨x,h,y,u',e,rfl⟩; obtain ⟨v,rfl⟩ := accolade K S g u
  rw [factors, mul_sum]; refine D.sum_mem (fun i _ ↦ ?_)
  rw [mul_mul_mul_comm]; refine census_here p ((Gate K).mul_mem h (ink_mem ..))
    ((Mantle K).mul_mem u' (word_ink S K i)) ?_
  rw [map_mul, e, trivial_acts p (word_locates S K i true) t,Algebra.smul_mul_assoc]

lemma split_void (h : f ∈ census K z p) (u : Split M) (v : z≠1) (e : Φ f=f)
    (t : GatesPrice M p ∨ MantlesPrice M p) : M f=0 := by
  rcases t with t|t
  · have he : M (Φ f)= z • M f := by
      refine Submodule.span_induction (p:=fun f _ ↦ M (Φ f) = z • M f) ?_ (by simp)
        (fun a b _ _ p q ↦ by rw [map_add,map_add,map_add,p,q,smul_add])
        (fun c a _ h ↦ by rw [map_smul,map_smul,map_smul,h,smul_comm]) h
      rintro f ⟨a,h,c,g,e,rfl⟩
      rw [map_mul,u.pixel _ h _ g,u.pixel _ (gateWard p h) _ (mantleWard p g),e,map_smul,t _ h]
      simp only [smul_eq_mul]; ring
    rw [e] at he; by_contra w
    exact v (mul_right_cancel₀ w (he.symm.trans (one_mul _).symm))
  refine Submodule.span_induction (p:=fun f _ ↦ M f=0) ?_ (map_zero _)
    (fun _ _ _ _ p q ↦ by rw [map_add,p,q,add_zero])
    (fun c _ _ p ↦ by rw [map_smul,p,smul_zero]) h
  rintro f ⟨a,h,c,g,e,rfl⟩
  rw [u.pixel _ h _ g]; suffices M c=0 by rw [this,mul_zero]
  have he := t c g; rw [e,map_smul] at he; by_contra w
  exact v (mul_right_cancel₀ w (he.trans (one_mul _).symm))

lemma center_star_activated (b : Bool) : star (centerPay b) ≠ 1 := fun e ↦
  center_activated b (star_injective (e.trans (star_one _).symm))

/-- `p` can interpolate away from the pockets of the active factor (incl on its own
remaining stencil). `p` prices all of the OTHER factor at identity here. These are
arbitrary even factors from Dome. Therefore the comparison applies to products of such
any other factors as well. For this reason we don't require singlet on `g`. -/
theorem pocket_zero (h : f.val∈ ribbon K S b U V) (u : U⊆ S) (v : V⊆ S)
    (c : f∈ enclave K) (t' : g∈ bay K T true) (e : ∀ i∈ U,p i=SU.central)
    (d : ∀ i∈ V,p i=1) (t : ∀ i∈ T,p i=1)
    (s : Split M) (k : GatesPrice M p ∨ MantlesPrice M p) : M (f*g)=0 :=
  split_void p (enroll_more p (enroll p h u v e d) t' t) s (center_star_activated b)
    (by rw [map_mul,(colorFixed K).1 c p,trivial_acts p t' t]) k

def litPocket (U : Finset Cover) : GVertex := fun i : Cover ↦ if i∈U then SU.central else 1
-- simple version
lemma comparison_zero (h : f.val∈ ribbon K S b U V) (u : U⊆ S) (v : V⊆ S)
    (c : f∈ enclave K) (t' : g∈ bay K T true) (d : Disjoint V U) (t : Disjoint T U)
    (k : Comparison M) : M (f*g)=0 := pocket_zero (litPocket U) h u v c t'
  (fun i h ↦ if_pos h) (fun i h ↦ if_neg (Finset.disjoint_left.mp d h))
  (fun i h ↦ if_neg (Finset.disjoint_left.mp t h)) k.1 (k.2.imp (fun v ↦ v _) (fun h ↦ h _))
end comparison

end YM.CF.Buffered.Afterglow.Pockets
namespace YM.CF.Buffered.Afterglow.Pockets
#print axioms pocket_zero
#print axioms comparison_zero
end YM.CF.Buffered.Afterglow.Pockets
