import YM.SU5.FiniteGaugeData.Concord.Palette

/-!
# Harvest any actual local mark at one period as a fixed test in the FiniteGaugeData local system
(may use for cutoff-dependent marks like nextMark)

Extra care: `Hosp S n` alone might allow *extra* edges of the finite torus between images. Need
observer-relative injectivity on `tips`. No assumed equality on a different period.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Pastry
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
open Reed (Fine think)
attribute [local instance] opCStarAlgebra

variable {S : Finset Cover} {n m : Side}

theorem smaller {T : Finset Cover} (p : Hosp T n) (h : S ⊆ T) : Hosp S n :=
  ⟨p.seat_.mono (show (S : Set Cover) ⊆ (T : Set Cover) from coe_subset.mpr h)⟩

lemma roomy (p : Hosp (tips S) n) : Hosp S n := smaller p (fun _ a => tips_here _ a)

lemma graft_point (p : Hosp S n) (U : LinksC) (a : Cover) (ha : a ∈ S) (i : Axis) :
    graft S n U (wrap (More n) a,i)=U (a,i) :=
  (onC_spec n (graft S n U) (a,i)).symm.trans (Satin.tail S n p U (a,i) ha)

lemma graft_agrees (p : Hosp (tips S) n) {U V : LinksC} (h : Agrees S U V) :
    Agrees (region S n) (graft S n U) (graft S n V) := by
  rintro ⟨x,i⟩ a b
  obtain ⟨k,u,rfl⟩ := Finset.mem_image.mp a
  obtain ⟨l,hb,v⟩ := Finset.mem_image.mp b
  have he : k+step i=l := p.seat_ (tips_there S u i) (tips_here S hb) (by rw [map_add, wrap_step]; exact v.symm)
  rw [graft_point (roomy p) U k u i, graft_point (roomy p) V k u i]
  exact h (k,i) u (show k+step i ∈ S from he.symm ▸ hb)

lemma regrown (p : Hosp S n) (U : Pane n) : Agrees (region S n) (graft S n (onC n U)) U := by
  rintro ⟨x,i⟩ a _
  obtain ⟨k,u,rfl⟩ := Finset.mem_image.mp a
  exact (graft_point p _ _ u i).trans (onC_spec n U (k,i))

theorem occupy_fills (p : Hosp S n) (x : Single n) (h : x ∈ modesIn n (region S n)) :
    ∃ a, occupy S n p a=x := by
  obtain ⟨⟨x,i⟩,b⟩:=x; rw [modes_at] at h; change node x ∈ region S n at h
  obtain ⟨y,t,h⟩ := mem_image.mp h
  let x₀:= nodeC (natural x)
  let d:= periods (More n) y - periods (More n) x₀
  let v:= natural x + n.val • d
  have he : nodeC v=y := by
    have hv : wrap (More n) x₀=node x := by unfold x₀; rw [←node_of, nat_true]
    calc nodeC v=x₀+(More n).val • d := by unfold v x₀ nodeC; rw [smul_add]; change _= _ + (n.val*2) • d; rw [Nat.mul_comm,mul_smul]; abel
         _ = y := by
           have a := carrying (More n) x₀; have v := carrying (More n) y; rw [hv] at a; rw [h] at v; unfold d; rw [smul_sub]; nth_rw 1 [← a]; refine Eq.trans ?_ v; abel
  have ha : wrap n v=x := needle (by rw [node_of,he]; exact h)
  let a : Satin.Tag S := ⟨(v,i,b), show nodeC v ∈ S from he.symm ▸ t⟩
  exact ⟨a,congrArg (fun y => ((y,i),b)) ha⟩

section round
variable {K:Calibration}(p : Hosp S (K.c m))
local notation "J" => occupy S (K.c m) p
local notation "φ" => star (flake (Tset (K.c m))ᶜ)

def permPhase (i : Evens S) := (museum S (K.c m) p i.val).choose

theorem perm_norm (i : Evens S) : ‖permPhase p i‖ = 1 := (museum S (K.c m) p i.val).choose_spec.1
lemma perm_ne (i : Evens S) : permPhase p i ≠ 0 := norm_pos_iff.mp ((perm_norm ..).symm ▸ zero_lt_one)

def bandCoord (i : Evens S) : FC (Single (K.c m)) →ₗ[ℂ] ℂ where
  toFun x := crumb (twist φ x) (i.val.map J) /permPhase p i
  map_add' x y := by rw [map_add, crumb_add,add_div]
  map_smul' c x := by rw [twist_scalar, crumb_scale, mul_div_assoc]; rfl

lemma band_bound (i : Evens S) (x : FC (Single (K.c m))) : ‖bandCoord p i x‖ ≤ ‖x‖ := by
  change ‖_/permPhase p i‖ ≤ _; rw [norm_div,perm_norm,div_one]
  exact (norm_entry _ _ _).trans_eq (twist_norm ..)

/-- Decode the native coefficients after their actual AP winds. -/
lemma harvest (f : Palette S) (x : Fields (K.c m)) (i : Evens S) :
    bandCoord p i (native S K m f x) = tint S (f i) (Prod.map (onC _) (onC _) x) := by
  let v:=Prod.map (onC (K.c m)) (onC (K.c m)) x
  have he (t : Evens S) : twist φ (note K (tint S (f t)) (tagWord S t.val) m x)=
      tint S (f t) v • (permPhase p t • poke (t.val.map J)) := by
    rw [note_v,twist_scalar, spool_sing,velvetTag, (museum S (K.c m) p t.val).choose_spec.2]; rfl
  change crumb (twist φ (native S K m f x)) _ / permPhase p i = _
  simp_rw [native_formula,pigment_formula,Finset.sum_apply,map_sum,he,crumb_sum,
    crumb_scale, Pastry.chip]
  rw [sum_eq_single i]
  · rw [if_pos rfl,mul_one,mul_div_cancel_right₀ _ (perm_ne p i)]
  · intro j _ h; rw [if_neg ?_,mul_zero,mul_zero]; exact fun e=> h (Subtype.ext (Finset.map_injective J e.symm))
  simp

lemma band_painted (f : Palette S) (y : PairsC) (i : Evens S) :
    tint S (f i) y=bandCoord p i (native S K m f (replant S (K.c m) y)) := by
  rw [harvest]; symm; exact (toPurse S _).property.locus _ _
     (fun k a _=> Satin.tail S _ p _ k a) (fun k a _=> Satin.tail S _ p _ k a)

include p
-- first onto any constant member of the supported grammar
private lemma personal (a : Satin.Tag S) : ∃ f : Family K, InTest K true S true f ∧
    ∀ x, f m x= (think (Tset (K.c m))).term (J a) := by
  obtain ⟨⟨x,i,b⟩,q⟩ := a; let a : Satin.Tag S := ⟨(x,i,b),q⟩
  let y:= J a; let c:= Lifted.winding (K.c m) x; have hc : c≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (Rush.fee_norm _).ge)
  by_cases h : i∈ plusHalf
  · refine ⟨c⁻¹ • creation K x i b, .smul _ (.creator _ h q), fun z=>?_⟩
    change c⁻¹ • create (c • basisKet y)=_
    rw [map_smul, inv_smul_smul₀ hc, create_put, show (think _).term (J a) = put _ from if_pos ((mem_Tset ..).2 h)]
  refine ⟨- (star c)⁻¹ • removal K x i b, .smul _ (.remover _ h q), fun z=>?_⟩
  change -(star c)⁻¹ • Fock.remove (c • basisKet y)= _
  unfold Fock.remove; rw [map_smul,star_smul, neg_smul, inv_smul_smul₀ (star_ne_zero.mpr hc), create_put,
    show (think _).term (J a) = -takeF _ from if_neg (fun v=> h ((mem_Tset ..).1 v))]

private lemma native_letters {x : FC (Single (K.c m))} {b : Bool} (h : Fine (Tset (K.c m)) (modesIn (K.c m) (region S (K.c m))) b x) :
    ∃ f : Family K, InTest K true S b f ∧ ∀ y, f m y=x := by
  induction h with
  | one => exact ⟨1,.one,fun _=>rfl⟩
  | empty => exact ⟨0,.zero,fun _=>rfl⟩
  | seed i v => obtain ⟨q,rfl⟩:= occupy_fills p i v; exact personal p q
  | scale h c U => obtain ⟨f,t,g⟩ := U; exact ⟨c • f,.smul _ t,fun z=> congrArg (c • ·) (g z)⟩
  | grow a b A B => obtain ⟨f,t,g⟩ := A; obtain ⟨F,V,G⟩:= B; exact ⟨f*F,.mul t V,fun z=>congrArg₂ (·*·) (g z) (G z)⟩
  | add a b A B => obtain ⟨f,t,g⟩ := A; obtain ⟨F,V,G⟩:= B; exact ⟨f+F,.add t V,fun z=>congrArg₂ (·+·) (g z) (G z)⟩

theorem shape_recover {x y : FC (Single (K.c m))}
    (a : Fine (Tset (K.c m)) (modesIn (K.c m) (region S (K.c m))) false x)
    (b : Fine (Tset (K.c m)) (modesIn (K.c m) (region S (K.c m))) false y)
    (v : ∀ i, bandCoord p i x= bandCoord p i y) : x=y := by
  obtain ⟨j,t,z⟩ := native_letters p a; obtain ⟨f,rfl⟩ := encode S K t
  obtain ⟨k,u,Z⟩ := native_letters p b; obtain ⟨g,rfl⟩ := encode S K u
  let W : Fields (K.c m) := 1
  rw [show x=native S K m f W from (z W).symm, show y=native S K m g W from (Z W).symm] at v ⊢
  simp_rw [harvest] at v; simp_rw [native_formula,pigment_formula,Finset.sum_apply,note_v]; simp_rw [v]
end round

variable (S) (K:Calibration)
def active (m : Side) : Submodule ℂ (Buffered.Mark (K.c m)) where
  carrier := {x | AtSupport false (region S (K.c m)) x}
  zero_mem' := AtSupport.zeroM
  add_mem' := AtSupport.addM
  smul_mem' := fun c _ t => AtSupport.smulM t c

variable (p : Hosp (tips S) (K.c m))

private def sliceBand (F:active S K m) (i : Evens S) (x : PairsC) : ℂ :=
  bandCoord (K:=K) (roomy p) i (F.val (replant S (K.c m) x))
private theorem slice_mem (F:active S K m) (i:Evens S) : Coeff true S (sliceBand S K p F i) := by
  have he := show AtSupport false (region S (K.c m)) F.val from F.property
  let Z:= bandCoord (K:=K) (roomy p) i
  refine ⟨fun _=>by contradiction, ⟨Z.continuous_of_finiteDimensional.measurable.comp (he.env.meas.comp (replant_b ..)),he.env.cost.choose,fun _=> (band_bound ..).trans (he.env.cost.choose_spec _)⟩,?_⟩
  exact fun x y v w => congrArg Z (he.dep (replant S _ x) (replant S _ y) (graft_agrees p v) (graft_agrees p w))

private def slicePaint (F:active S K m) (i:Evens S): swatches S := ofPurse S ⟨_, slice_mem S K p F i⟩
private theorem cut_slice (F:active S K m) : native S K m (slicePaint S K p F)=F.val := by
  have hx := (pigment_test S K (slicePaint S K p F)).support m; have he := show AtSupport false (region S (K.c m)) F.val from F.property
  funext y
  apply shape_recover (roomy p) (hx.allV _) (he.allV y)
  intro i
  let Z: PairsC:= Prod.map (onC _) (onC _) y
  change bandCoord (roomy p) i (native S K m (slicePaint S K p F) y)= _
  rw [harvest]; change tint S (ofPurse S _) Z =_
  rw [tint_ofPurse]; exact congrArg (bandCoord (K:=K) (roomy p) i) (he.dep (replant S (K.c m) Z) y (regrown (roomy p) y.1) (regrown (roomy p) y.2))

def paintMark : active S K m ≃ₗ[ℂ] Palette S :=
  (LinearEquiv.ofBijective ((native S K m).codRestrict (active S K m)
    (fun f=> (pigment_test S K f).support m))
    ⟨(fun _ _ a=> native_injective S K (roomy p) (congrArg Subtype.val a)),
      fun x=> ⟨slicePaint S K p x, Subtype.ext (cut_slice S K p x)⟩⟩).symm

lemma exhibit (F : active S K m) : native S K m (paintMark S K p F)=F.val :=
  congrArg Subtype.val ((paintMark S K p).symm_apply_apply F)

lemma test_budget (F : active S K m) (y : ℝ) (h : ∀ x, ‖F.val x‖ ≤ y) :
    ‖paintMark S K p F‖ ≤ y := palette_norm S K (roomy p) (by rw [exhibit]; exact h)
lemma all_budget (F : active S K m) (y : ℝ) (h : ∀ x, ‖F.val x‖ ≤ y)
    (n : Side) (x : Fields (K.c n)) : ‖native S K n (paintMark S K p F) x‖ ≤ count S*y :=
  (native_bound ..).trans (mul_le_mul_of_nonneg_left (test_budget S K p F y h) (count_nonneg S))

lemma brush (F:active S K m) (x:PairsC)(i:Evens S) :
    tint S (paintMark S K p F i) x = bandCoord (roomy p) i (F.val (replant S (K.c m) x)) := by
  rw [band_painted (K:=K) (roomy p),exhibit]
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.exhibit
#print axioms YM.CF.Buffered.Concord.brush
