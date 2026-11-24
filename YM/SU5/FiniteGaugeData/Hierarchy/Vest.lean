import YM.SU5.FiniteGaugeData.Hierarchy.Troop
/-! Separated factorization. The limiting step `P` is a linear map on products on the same support too, but multiplicativity there is not the prescription. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
local notation "W"=> GridStep Λ l
local notation "N"=> side Y i s
abbrev spaceBill (Λ:Preparation)(l:ℕ) := 2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)

abbrev Range (r:ℕ) (S T:Finset Cover): Prop:= ∀ x∈ S, ∀ y∈ T, y-x ∉ Lattice.box r
abbrev SeatRange (r:ℕ) (N_:Side)(S T:Finset Cover):Prop:=∀ x∈region S N_,∀ y∈region T N_,r < separation x y
-- local separation on cover fits any rung eventually. 
lemma screen_per (r:ℕ) (p:Range r S T) (h:Hosp (T∪liner S r) (side Y i s)): SeatRange r (side Y i s) S T:=by
  intro x hx y hy; obtain ⟨x,u,rfl⟩:= Finset.mem_image.mp hx; obtain ⟨y,v,rfl⟩:= Finset.mem_image.mp hy; by_contra! k
  have hp:= linen_contains S r (N) (halo_spec.mpr ⟨wrap _ x,mem_image_of_mem (wrap _) u,k⟩); -- this only gives some x∈S; still contradiction
  obtain ⟨z,e,b⟩:=mem_image.mp hp; rw [←h.seat_ (mem_union_right _ e) (mem_union_left _ v) b] at v; obtain ⟨x',q,d⟩:= mem_biUnion.mp e; obtain ⟨s,t,rfl⟩:= mem_image.mp d; exact p _ q _ v (by rw [add_sub_cancel_right]; exact t)
include h in
lemma screen_path (r:ℕ)(p:Range r S T): ∀ᶠ i in atTop, SeatRange r (side Y i s) S T:=by
  filter_upwards [(solvent_often Y h (T∪liner S r) s)] with i t; exact screen_per Y S T s i r p (solvent_lower Y _ _ t)

section producer
private lemma push_unit {N' P:Side}(G:Ratio N' P)(A:StepData (More N') (More P)) (j:ℕ)(Q:Op SU.Slot)(t:Male)(q:Chi)(d β:ℝ)(l:Loom N')(ho:Odd G.count.val)(p:A.patch.Branches A.kernel SU.group):
    pushMark G A j Q t ho q d β l 1= (1:Mark P):=by
  funext x; unfold pushMark linkLaw Advance.assembled gathered before avgF; simp_rw [Pi.one_apply,sub_one,sum_const,card_univ]
  have w:Nonempty (Forest (ratio G)):= Tree.select _ ho
  rw [show ∀ X:FC (Single P), ((Fintype.card (Forest (ratio G)):ℝ)⁻¹) • (Fintype.card (Forest (ratio G)) • X) = X from ?_]
  · simp only [integral_const,probReal_univ,one_smul,integral_smul_const,A.density_total p]
  intro X; rw [← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (by positivity: (Fintype.card (Forest (ratio G)):ℝ) ≠ 0)]

lemma snag_unit (p:Offered Y S s i k) : snag Y h S s i k (unitQ Kₜ S)= unitQ Kₜ W₀:=by
  rw [snag_pay Y h S s i k p,transitionQ_apply]; apply sold_catalog_inj Y h W₀ (s+1) i (roomy_hosp _ p.bill.upper); dsimp only; rw [exchanged, unitQ_id,unitQ_id,sold_one,sold_one]; exact push_unit (apt (Y.ir i) Λ.block L₁ s) _ _ _ _ _ _ _ _ Λ.R.odd_side ((fullness Y i k p.calendar).cap_grant.branch s p.age)

variable (U:Finset Cover)(e:S⊆ U)(a:T⊆U)(x:Catalog S)(y:Catalog T)
lemma snag_join (v:Offered Y S s i k)(u:Offered Y T s i k)(m:Offered Y U s i k)
  (p:SeatRange (spaceBill Λ l) (side Y i s) S T):
    snag Y h U s i k (timesQ Kₜ e a x y)=
      timesQ Kₜ (grid_mono S U (Λ:=Λ) (l:=l) e) (grid_mono T U (Λ:=Λ) (l:=l) a) (snag Y h S s i k x) (snag Y h T s i k y):=by
  apply sold_catalog_inj Y h ((W) U) (s+1) i (roomy_hosp _ m.bill.upper)
  dsimp only; rw [snag_pay Y h S s i k v,snag_pay Y h T s i k u,snag_pay Y h U s i k m]; simp_rw [transitionQ_apply,timesQ_id,sold_mult, exchanged, timesQ_id,sold_mult]
  let t:= crease Y s i k v.calendar v.age
  exact separated_mult (apt (Y.ir i) Λ.block L₁ s) _ _ _ _ Λ.R.odd_side Chi.canonical _ _ _ (show LaurentRadius _ _ _ from Journey.legal Λ) ((Y.voyage i).ownership s).paid.bill ((fullness Y i k v.calendar).cap_grant.branch s v.age) t.1 t.2 _ _ (sold_affair Y h S _ _ (compose_t ..)) (sold_affair Y h T _ _ (compose_t ..)) (Journey.tissue ..) p
include K R in
lemma festive (p: Range (spaceBill Λ l) S T) :
    P U s (timesQ Kₜ e a x y)=
      timesQ Kₜ (grid_mono S U (Λ:=Λ) (l:=l) e) (grid_mono T U (Λ:=Λ) (l:=l) a) (P S s x) (P T s y):=by
  obtain ⟨k,hp⟩:= eligible_exists Y u _ K.pick.grow_k
  have he(L:Finset Cover)(x):= audition _ _ (calls Y h L s R k hp) (tendsto_const_nhds (x:=x))
  let W':= timesQ Kₜ (grid_mono S U (Λ:=Λ) (l:=l) e) (grid_mono T U (Λ:=Λ) (l:=l) a)
  refine tendsto_nhds_unique_of_eventuallyEq (he U (timesQ Kₜ e a x y)) (audition _ _ ((W'.continuous.tendsto _).comp (he S x)) (he T y)) ?_
  filter_upwards [eligible_offer Y h S s K k hp,eligible_offer Y h T s K k hp, eligible_offer Y h U s K k hp,K.pick.grow_i.tendsto_atTop.eventually (screen_path Y h S T s _ p)] with i t u v g; exact snag_join Y h S T s _ _ U e a x y t u v g
include K R in
lemma unit_roll : P S s (unitQ Kₜ S)=unitQ Kₜ W₀:=by
  obtain ⟨k,hp⟩:=eligible_exists Y u _ K.pick.grow_k; exact tendsto_nhds_unique_of_eventuallyEq (audition _ _ (calls Y h S s R k hp) (tendsto_const_nhds (x:=unitQ Kₜ S))) tendsto_const_nhds ((eligible_offer Y h S s K k hp).mono fun i t=> snag_unit Y h S s (u i) _ t)
end producer
#print axioms festive
end YM.CF.Buffered.Afterglow.Hierarchy
