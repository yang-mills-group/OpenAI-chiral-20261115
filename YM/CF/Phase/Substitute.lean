import YM.CF.Phase.Expect

/-! Planar and whole operands, support invariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Sample
open Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {e : ℝ}
abbrev Hub (m : Side) := Option (Index m)
abbrev Stamp (m B : Side) := Seal (Site (Domain m B))
abbrev Post (m B : Side) := Own (CSide m B)
def window (m B : Side) (S : Stamp m B) : Hub m→Support (Domain m B)
  | none => walls m B S
  | some h => room m B h
def sanctioned (m B : Side) (S : Stamp m B) : Hub m→Prop
  | none=>True
  | some v=>∀ i∈S, slab m B v i
def stationP (m B : Side) (q t : Sq) : Hub m→Skin m B→ArrayF m→Tenant.Input (CSide m B)
  | none=>touch m B q t
  | some v => twinR m B v q t
lemma near_wire {S : Stamp m B} (v : Hub m) (a) (e:a∈chairs m B S) (p : sanctioned m B S v) : room m B a⊆window m B S v := by
  cases v with
  | none=> exact in_wall (chair_pad e)
  | some b =>
    obtain ⟨x,k,j,u,f⟩ := chaff.mp e
    have h := p x k; rw [slab_act h] at u
    exact room_in (fits_trans f (room_active (snapped h) u))
lemma drives {q t r U A} (b : Room B e) (g : Guard U e) (V : Verified m B margin U A r) (x:q∈zone r) (y:t∈zone r) (h : ‖t-q‖≤2/(way B:ℝ)) (v : Hub m) : TenantK (stationP m B q t v U A) := by
  cases v; exact enter_pair b g V x y h; exact replica_pair b g V x y _ h
lemma dress (p q : Sq) (r) (h:p∈zone r) (g:q∈zone r) (a : Hub m) (b : Room B e) : ContinuousOn (fun t:FlagU m B => stationP m B p q a t.1 t.2) (banner m B e r) := by
  cases a with
  | none=>
    rintro ⟨t,w⟩ ⟨u,v⟩; apply ContinuousAt.continuousWithinAt; apply ContinuousAt.prodMk continuousAt_fst _
    apply continuousAt_pi.mpr; intro i; apply continuousAt_pi.mpr; intro z
    let H := fun t:FlagU m B=> (t.1,t.2,duo p q i)
    let F := fun y:Skin m B×ArrayF m×Sq=> paintV m B y.1 y.2.1 y.2.2 (node z)
    change ContinuousAt (F ∘ H) _; have ht := either_duo h g i
    have he : ContinuousAt F (H (t,w)) := continuousAt_pi.mp (paintV_at (U:=t) ht.1 b.1 u v ht.2 b.2.2) _
    exact he.comp (continuousAt_fst.prodMk (continuousAt_snd.prodMk continuousAt_const))
  | some a=>
    rintro ⟨t,w⟩ ⟨u,v⟩; apply ContinuousAt.continuousWithinAt; apply ContinuousAt.prodMk ((replica_cont a|>.comp (continuous_fst (Y:=ArrayF m))).continuousAt) _
    apply continuousAt_pi.mpr; intro i; apply continuousAt_pi.mpr; intro z
    let H := fun t:FlagU m B=> (t.1,t.2,duo p q i)
    let F := fun y:Skin m B×ArrayF m×Sq=> paintV m B y.1 y.2.1 y.2.2 (snap m B a (node z))
    change ContinuousAt (F ∘ H) _; have ht := either_duo h g i
    have he : ContinuousAt F (H (t,w)) := continuousAt_pi.mp (paintV_at (U:=t) ht.1 b.1 u v ht.2 b.2.2) _
    exact he.comp (continuousAt_fst.prodMk (continuousAt_snd.prodMk continuousAt_const))
lemma station_g (m B : Side) (p q : Sq) (k : Hub m) (t : Site (Domain m B)→E) (U A) : stationP m B p q k (Lattice.gauge t U) (onF t A)=flipR (match k with | some a=>t ∘ snap m B a | none=>t) (stationP m B p q k U A) := by cases k; exact touch_g ..; exact twinR_g ..
-- currency occurrence, support-local value only.
lemma waivered {m B : Side} (S : Stamp m B) {U V : Tenant.Input (CSide m B)} (g : ∀ i∈leaks S,U.1 i=V.1 i) (k : ∀ j, ∀ i∈news S,U.2 j i=V.2 j i) : vacancy S U V=0 := by
  unfold vacancy; rw [sum_eq_zero, sum_eq_zero (s:=univ)]; rw [add_zero]
  · intro j _; apply sum_eq_zero; intro i l; rw [k j i l,sub_self,norm_zero]
  intro i l; rw [g i l,sub_self,norm_zero]
lemma station_read {U V : Skin m B} (S : Stamp m B) (v : Hub m) (p q) (e : Agrees (window m B S v) U V) (g : sanctioned m B S v) {A X : ArrayF m} (h : AgreeF (chairs m B S×ˢ Finset.univ) A X) :
    vacancy S (stationP m B p q v U A) (stationP m B p q v V X)=0 := by
  have he (z) (hz:z∈S) (i: Spot m) (hi:i.1∈active m B z) : A i=X i := h i (mem_product.mpr ⟨chaff.mpr ⟨z,hz,i.1,hi,fits_id _ _⟩,mem_univ _⟩)
  cases v with
  | none =>
    apply waivered S
    · intro i hi; have hz := mem_filter.mp hi; exact e i (mem_union_left _ hz.2.1) (mem_union_left _ hz.2.2)
    intro j i hi; have hl : node i∈S := (mem_filter.mp hi).2; obtain ⟨a,hg,_⟩ := full_r m B (node i)
    have ht (k:Spot m) (p:k.1∈active m B (node i)) := he (node i) hl k p
    have hm : a∈pavilion m B S := (pad_iff ..).mpr ⟨node i,hl,a,hg,by simp⟩
    exact paint_local a hg (duo p q j) (fun i x y=>e i (in_wall hm x) (in_wall hm y)) ht
  | some a =>
    apply waivered S
    · rintro ⟨x,j⟩ l; exact rep_local a a (snapped (g _ (mem_filter.mp l).2.1)) j (snapped (g _ (mem_filter.mp l).2.2)) e
    intro j i hi; have hx : node i∈S := (mem_filter.mp hi).2; have ht := g _ hx
    exact paint_local a (snapped ht) _ e (fun i' k=> he (node i) hx i' (by rw [slab_act ht]; exact k))
-- Evaluations are extended by 0 over junk
section fees
variable {Z : Type*} [Zero Z]
def accessK (m B : Side) (q t : Sq) (v : Hub m) (U : Skin m B) (A : ArrayF m) (f : Post m B → Z) :=
    @dite Z (TenantK (stationP m B q t v U A)) (Classical.propDecidable _) (fun p=> f ⟨_,p⟩) (fun _=>0)
lemma entrance {p q v f} {U : Skin m B} {A : ArrayF m} (h : TenantK (stationP m B p q v U A)) : accessK (Z:=Z) m B p q v U A f=f ⟨_,h⟩ := dif_pos h
end fees
lemma access_cont {Z : Type*} [Zero Z] [TopologicalSpace Z] (S : Set (FlagU m B)) (q t : Sq) (v : Hub m) (f : Post m B→Z) (g : Continuous f) (h : ∀ x∈S, TenantK (stationP m B q t v x.1 x.2)) (p : ContinuousOn (fun x:FlagU m B=>stationP m B q t v x.1 x.2) S) : ContinuousOn (fun x:FlagU m B=>accessK m B q t v x.1 x.2 f) S := by
  rw [continuousOn_iff_continuous_restrict]; let F : S→ Post m B := fun x => ⟨_,h x.val x.property⟩
  have he : Continuous F := by apply Continuous.subtype_mk; exact continuousOn_iff_continuous_restrict.mp p
  apply (g.comp he).congr; intro x; exact (entrance (Z:=Z) (m:=m) (B:=B) (h _ x.property)).symm

lemma exact_station (f : Post m B →ℂ) (p q v) (U : Skin m B) (A) (t : Site (Domain m B)→E) (h : TenantK (stationP m B p q v U A)) (e : ∀ x g, f (toss g x)=f x) :
    accessK m B p q v (Lattice.gauge t U) (onF t A) f=accessK m B p q v U A f := by
  let g := match v with | some a=>t ∘ snap m B a | none=>t; let x : Post m B := ⟨_,h⟩
  have hp : (toss g x).val=stationP m B p q v (Lattice.gauge t U) (onF t A) := (station_g ..).symm
  have hz := (toss g x).property; change TenantK (toss g x).val at hz; rw [hp] at hz; rw [entrance h, entrance hz, ← e x g]; congr 1; exact Subtype.ext hp.symm
lemma access_eq {p q} {U V : Skin m B} {A F : ArrayF m} {f : Post m B→ℂ} (S : Stamp m B) {w : ℝ} (h : Element (slotK (CSide m B)) S w f) (v : Hub m) (e : sanctioned m B S v) (Q : TenantK (stationP m B p q v U A)) (P : TenantK (stationP m B p q v V F)) (hu : Agrees (window m B S v) U V) (hv : AgreeF (chairs m B S×ˢ Finset.univ) A F) :
    accessK m B p q v U A f=accessK m B p q v V F f := by
  rw [entrance Q,entrance P]; let x : Post m B := ⟨_,Q⟩; let y : Post m B := ⟨_,P⟩
  apply sub_eq_zero.mp; apply norm_le_zero_iff.mp
  have he : (slotK (CSide m B)).eval S x y=0 := station_read S v p q hu e hv; have hk := h.varies x y; rw [he,mul_zero] at hk; exact hk

-- matching sails
lemma slab_ch {S : Stamp m B} {a:Index m} (h:sanctioned m B S (some a)) : chairs m B S⊆faces m a := by
  intro i hi; obtain ⟨x,g,y,l,v⟩ := chaff.mp hi; rw [slab_act (h x g)] at l; exact mem_filter.mpr ⟨mem_univ _, fits_trans v (room_active (snapped (h x g)) l)⟩
end YM.CF.Phase
