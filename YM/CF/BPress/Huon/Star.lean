import YM.CF.BPress.Huon.Array
/-! flag parity. Masks use actual tags.Area changes.L. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Huon
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
open Along Spine Mosaic.Pulse Mosaic Palmer Contour Lilac.Stripe Ledger Push.AbsoluteSums
variable {R:Hangar (More N)} {H:Crew A}{X:Sugar.Stage N}{e c d:ℝ}{k:ℕ}
variable (p: Rented R H X d e k c) (x: Visit A R H)(S:SlotT A R)
abbrev markZ := H.flag (fU x.val)
abbrev markY := H.areaC R X (fU x.val)
-- Use separate factors stored in generator; merge. Y-power at cardinal W included at mask. price.
open Vesper Wheel Hazel Charter Contour
abbrev κZ := Crew.lock (fU x.val)
abbrev κY := Crew.can (fU x.val)
abbrev segZZ := badcore x (plan A R) S (markZ x)
abbrev segYY := badcore x (plan A R ∘ node) S (markY x (X:=X))
def shapeM (X: Sugar.Stage N)(ε:ℝ) := (ζ (segZZ x S) (κZ x))⁻¹ * bill_phase (ε:ℂ) (κY x) (segYY (X:=X) x S)
include p in
lemma changeZ : (Camp x.val H).biUnion (segZZ x)=markZ x:=by unfold segZZ; rw [partition]; ext1 i; rw [chipAt,mem_filter,and_iff_left_of_imp]; intro h; exact petal_m _ _ (by norm_num : 1≤29) (at_petal.mpr ((p.pay (fU x.val) x.property).flood i i h (by simp)).2) -- note antecedent tune
lemma changeY : (Camp x.val H).biUnion (segYY (X:=X) x)=markY (X:=X) x:=by unfold segYY; rw [partition]; ext1 i; rw [chipAt,mem_filter,and_iff_left_of_imp]; intro h; exact petal_m _ _ (by norm_num :6≤29) (at_petal.mpr (mem_filter.mp h).2.1) -- tune composition plan
include p in
lemma slate_mask(ε:ℝ) : Crew.maskH R H X (House.read A R x.val) ε = ∏ i∈ Camp x.val H, shapeM x i X ε:=by
 let T:= Camp x.val H; let f(i):=segZZ x i; let g:=segYY (X:=X) x; let h:=(ε:ℂ)⁻¹; have he:= separatesV x (plan A R) (markZ x); have ht:= separatesV x (plan A R ∘ node) (markY (X:=X) x); unfold Crew.maskH Mount.Ωmask; change (ζ (markZ x) _)⁻¹ *((ζ (markY (X:=X) x) _)⁻¹* h^(markY (X:=X) x).card)=_; rw [←changeZ p x,←changeY x]; unfold shapeM ζ bill_phase ζ; simp_rw [prod_mul_distrib, ← Finset.prod_inv_distrib]; rw [prod_biUnion he,prod_biUnion ht,card_biUnion ht,Finset.prod_pow_eq_pow_sum]
lemma cost_mask(ε:ℝ) (h:0≤ε): ‖shapeM x S X ε‖= ε⁻¹^(segYY (X:=X) x S).card:=by unfold shapeM bill_phase; simp only [norm_mul,norm_pow,norm_inv,Wheel.ζ_price,inv_one,one_mul,Complex.norm_real,Real.norm_of_nonneg h]
lemma card_mask(h: X.W.M≤ Wealth.cloak B) : (segYY (X:=X) x S).card ≤ (debris H x.val S).card*estate 29 *(R.L.val^3*(B.D+2*X.W.M+1)):= by
 let W:= specialB X.W A R (debts H x.val); let q:= Vista H x.val S; have hp: (badcore x (plan A R ∘ node) S W).image node⊆ clampS q X.W.M:=by
    intro i h; obtain ⟨i,t,rfl⟩:= mem_image.mp h; exact fuel _ _ ((mem_filter.mp t).2) ((mem_filter.mp (mem_filter.mp t).1).2.2) -- tune
 rw [← Finset.card_image_of_injective (segYY (X:=X) x S) Tenant.needle]; exact (Finset.card_le_card hp).trans ((fuel_cost q h).trans (Nat.mul_le_mul_right _ (vista_card ..)))
omit p
variable {S x}
lemma paints_eq {y:Visit A R H}(h:Along x.val y.val (Contour.station fan S)): Vista H x.val S= Vista H y.val S:= congrArg untouch (upper_loc (H:=H) (h.mono (fun _ g=> estate0 g))).1
include p
variable (g:Charter H R X k)
include g
lemma flag_detect {i:Site (More N)}{y:Visit A R H} (h:Along x.val y.val (Contour.station fan S)) (v:i∈ segZZ x S) : i∈ markZ y:=by
 obtain ⟨t,w⟩:= mem_filter.mp v; obtain ⟨j,a,q⟩:= (p.pay (fU x.val) x.property).blaze _ t; let T:= Room j S (Peel.attach X k) 40; let U:= Room j S (Peel.attach X k+4) 41; have hu:Agrees (↑U : Set (Site (More N))) (H.port (fU x.val)) (H.port (fU y.val)):= agreesR g h
 have ht: i∈ T:= mem_filter.mpr ⟨halo_subset _ _ a,?_⟩; swap; · obtain ⟨i,v,w⟩:= mem_biUnion.mp w; exact mem_biUnion.mpr ⟨i,(mem_inter.mp v).2, stem_mid _ (by norm_num : 29≤40) w⟩
 have hf: halo 4 T ⊆ U:=by intro i p; obtain ⟨i,p,z⟩:= halo_spec.mp p; exact extend_ _ _ p g.care ((Nat.le_add_left ..).trans g.pitch) z
 have hU:= spread _ _ T U hf hu (temp H.y); exact (mem_inter.mp (hU ▸ (show i∈T∩ flags (temp H.y) (H.port (fU x.val)) from mem_inter.mpr ⟨ht,t⟩))).2 -- tune Lean
lemma segM {y: Visit A R H}(h:Along x.val y.val (Contour.station fan S)): segZZ x S=segZZ y S∧ segYY (X:=X) x S=segYY (X:=X) y S:=by
 let p1:=paints_eq h; constructor
 · ext1 i; constructor; intro v; exact mem_filter.mpr ⟨flag_detect p g h v, p1 ▸ (mem_filter.mp v).2⟩; intro v; exact mem_filter.mpr ⟨flag_detect p g h.symm v,p1.symm ▸ (mem_filter.mp v).2⟩
 ext1 i; unfold segYY badcore chipAt; simp only [mem_filter,p1]; refine and_congr_left fun v=>?_ ; unfold markY areaC specialB; simp only [mem_filter,mem_univ,true_and]; apply and_congr (h.masks ((stem_mid _ (by norm_num : 6≤40)).trans (vista_demand v))) Iff.rfl -- tune
lemma shape_read {y:Visit A R H}(ε:ℝ)(h:Along x.val y.val (Contour.station fan S)): shapeM x S X ε=shapeM y S X ε:=by
 obtain ⟨t,v⟩:= segM p g h; unfold shapeM bill_phase; rw [←v,←t]; refine congrArg₂ (·*·) (congrArg Inv.inv ?_) (congrArg (·*_) (congrArg Inv.inv ?_)); · exact prod_congr rfl (fun i t=>congrArg (fun x:Circle=>(x:ℂ)) (h.locks i (thinker ((mem_filter.mp t).2)))) -- tune
 exact prod_congr rfl (fun i t=> congrArg (fun x:Circle=>(x:ℂ)) (h.cylinders i (thinker (mem_filter.mp t|>.2))))
end YM.CF.BPress.Huon
