import YM.SU5.WakeInvestment.TractLeaf
import YM.SU5.WakeInvestment.Vessel
import YM.SU5.WindTorque.WakeV
/-! # pricing at publications. A measure on displacements with clearance to shelf landmarks.
All Spin & gauges in common metric. -/
set_option autoImplicit false
set_option synthInstance.maxSize 25000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.EmberWind.Staff
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Fock
attribute [local instance] opCStarAlgebra
open Ballad Hiro
open Py.Rate.LocalLimit.Papal
open Pannier.Chancel Rous Pressure
open Work.E08
open Gleam Regis Regis.Head Gleam.Wake
local notation "A₅" => SU.group
variable (W:Staff){z:ℂ}{n:Side}{r k s d w:ℕ}{α t:ℝ}
private lemma coach(r:ℕ)(o y z:Seat n)(p:y∈ BlockP r o)(h:z∈ visits o (march o y 1)): z∈ BlockP r o:=by
 obtain ⟨v,x,y⟩:= march_visit o y 1 _ h; obtain ⟨g,c⟩:= box_test.mp (lift_mem_box (blocks_test.mp p)); apply blocks_test.mpr; rw [x,add_comm]; apply separation_box_add _ (box_test.mpr ?_)
 constructor <;> intro i
 · have ht:= y.left i; change min (0:ℤ) _ ≤ _ at ht; specialize g i; change _ ≤ _ at g; omega
 have ht:=y.right i; change _ ≤ max (0:ℤ) _ at ht; specialize c i; omega
-- Keep height layout and integer $ℬ$ checks for any covering true Pace. Costs in coupon.
abbrev tenancy (W:Staff)(n:Side) (r d e:ℕ)(o:Seat n) := gateS W (r+d+8) n ⊆ BlockP e o
lemma held_peace(n:Side)(U:Pane n)(S: Support (More n))(L:Walk)(u:Skye.Seat n)(h:Tiny S U t)(p:∀ z∈ visits u L,z∈ S) : SU.group.chord (travel U u L)≤ L.length*t:=by
 induction L generalizing u with
 | nil=> simp [travel]
 | cons i L ih=>
    have he:u∈S:=p _ List.mem_cons_self
    have ht:∀ z∈ visits (u+i.vec) L,z∈ S:=fun _ v=>p _ (List.mem_cons_of_mem _ v); have hv:= ht (u+i.vec) (by cases L <;> simp [visits]); rw [travel]
    apply (Gauge.chord_triangle ..).trans; refine (add_le_add (b:=t) ?_ (ih _ ht)).trans_eq (by rw [List.length_cons]; push_cast; ring)
    obtain ⟨i,e |e⟩:=i; exact h (u,i) he hv
    change SU.group.chord (U (u-step i,i))⁻¹ ≤ t; rw [Gauge.chord_inv]; refine h (u-step i,i) ?_ ?_
    · simpa only [Step.vec,ite_true,sub_eq_add_neg] using hv
    change u-step i+step i∈ S; rwa [sub_add_cancel]
lemma Pays.withinP (p:W.Pays r w) (n:Side): gateS W (r+8) n=(W.skyRent r).image (wrap (More n))∧ W.scope n∈ gateS W r n ∧ touched (W.localFace n) ⊆ gateS W r n ∧ ∀ i∈ visits (W.scope n) W.steps, i∈ gateS W r n:=by
 let a:=wrap (More n); have he (y:Cover)(s:y∈skyDeck W.hub r): wrap (More n) y∈ gateS W r n:= by unfold gateS; rw [←wrap_pav]; exact mem_image_of_mem a s
 refine ⟨(wrap_pav ..).symm, he W.xo (p.node W),?_,?_⟩
 · intro i v; rw [show touched (W.localFace n)= _ from (visa_wrap W.face (More n)).symm] at v; obtain ⟨t,h,rfl⟩:= mem_image.mp v; exact he t (p.faceSites h)
 intro i v; change i∈ visits (wrap (More n) W.xo) _ at v; rw [←tours_paid] at v; obtain ⟨i,u,rfl⟩:=List.mem_map.mp v; exact he _ (p.roomSites _ u)
-- rendezvous. Staging on material. purchase both comparisons U & g' Pose.
abbrev Beacon (o:Seat n)(A:ColorL)(U:Pane n):ColorL:= SU.group.adjoint (travel U o (march o (W.scope n) 1)) A
def cargoS (n:Side)(U:Pane n)(ρ:ℝ):ColorL:=ρ • SU.group.curvature (faceValue U (W.localFace n))
lemma keeper_car (p:W.Pays r w)(U:Pane n)(h:pingS t (W.gateS r n) U)(ρ:ℝ) : ‖cargoS W n U ρ‖ ≤ |ρ| *t ∧ ‖pearl W ρ n r t U‖= ‖cargoS W n U ρ‖ :=by
 let x:= W.localFace n; have hx:= Work.E01.base_touched x; have hh:= h x (not_disjoint_iff.mpr ⟨x.1,(p.withinP W n).2.2.1 hx,hx⟩)
 constructor; · unfold cargoS; rw [norm_smul]; exact mul_le_mul_of_nonneg_left ((SU.group.curvature_norm _).trans hh.le) (abs_nonneg _)
 unfold pearl edgeBudget; rw [if_pos h,Gauge.norm_adjoint]; rfl
lemma pearl_le (p:W.Pays r w) (U:Pane n)(h:0 ≤ t)(ρ:ℝ) : ‖pearl W ρ n r t U‖ ≤ |ρ| * t:=by
 by_cases y:pingS t (W.gateS r n) U; · rw [(keeper_car W p U y ρ).2]; exact (keeper_car W p U y ρ).1
 rw [pearl,if_neg y,norm_zero]; positivity
lemma pearl_cost (U:Pane n){o:Seat n}(p:W.Pays r w)(z:tenancy W n r d s o)(ρ:ℝ)(he:pingS t (W.gateS r n) U)(hx:Tiny (BlockP s o) U α)(f:0 ≤α) :
   ‖pearl W ρ n r t U-cargoS W n U ρ‖ ≤ 2*SU.group.colorScale* w*α*(|ρ| * t) ∧ ‖Beacon W o (pearl W ρ n r t U) U-pearl W ρ n r t U‖ ≤ 2*SU.group.colorScale*4*s*α*(|ρ| *t):=by
 obtain ⟨u,h,v,g⟩:= p.withinP W n; let q:= W.gateS r n; have hh:q⊆ BlockP s o:= (Corona.halo_mono (show r ≤ r+d+8 from by omega) (Subset.refl _)).trans z; let Q:= BlockP s o; let C:= cargoS W n U ρ; let H:= |ρ| * t; let D:=pearl W ρ n r t U; obtain ⟨hq,hD⟩:= keeper_car W p U he ρ
 have hw {S:ColorL} (x:Lattice.Walk)(o₁:Seat n)(h:‖S‖≤ H) (b:ℕ)(u:x.length≤ b)(v:∀ i∈visits o₁ x,i∈Q): ‖SU.group.adjoint (travel U o₁ x) S-S‖ ≤ 2*SU.group.colorScale*(b*α)* H:=by
    have hv:= (held_peace n U Q x o₁ hx v).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr u) f); have hp:0 ≤SU.group.colorScale:=SU.group.colorScale_pos.le
    apply (Next.Fluctuations.adjoint_norm_sub ..).trans; gcongr
 constructor
 · rw [pearl,if_pos he]; exact (hw W.steps _ hq w p.stepCost (fun _ v=> hh (g _ v))).trans_eq (by ring)
 exact (hw _ o (hD.le.trans hq) (4*s) (march_len o (W.scope n) 1 ((separation_comm ..).trans_le (blocks_test.mp (hh h)))) (coach s o _ · (hh h) ·)).trans_eq (by push_cast; ring) -- lambda syntax tuning
lemma passage (U:Pane n)(o:Seat n)(h:tenancy W n r d s o) (p:Py.Rate.LocalLimit.Preparation.Yoke.ordinary (n:=n) (Py.Rate.LocalLimit.Preparation.Yoke.possession (n:=n) (BlockP s o)) α U)(t':α<t): pingS t (W.gateS r n) U:=by
 intro i p'; obtain ⟨x,v,ht⟩:= not_disjoint_iff.mp p'; refine lt_of_le_of_lt (p i (mem_filter.mpr ⟨mem_univ _,fun w v' =>?_⟩)) t'
 obtain ⟨z,y,u⟩:=halo_spec.mp v; refine h (halo_spec.mpr ⟨z,y,(separation_triangle z x w).trans ?_⟩); have hx:=separation_triangle x i.1 w; rw [separation_comm x i.1] at hx; have h':=Work.E01.sep_touched i w v'; have h'':=Work.E01.sep_touched i x ht; omega
-- computed allowances for vessel of two such reads.
private theorem stockFrame (G:Gauge) : ∃ k:ℕ,∀ i:PlaqAxes,∀ t:Signed, (skewSlot G (keelSlot i) t).length≤k:= by
 have hv(i:PlaqAxes)(t:Signed): ∀ᶠ k:ℕ in atTop,(skewSlot G (keelSlot i) t).length≤k:=eventually_ge_atTop _; exact (eventually_all.mpr (fun i:PlaqAxes=> eventually_all.mpr (hv i))).exists
abbrev clearance :ℕ:= Classical.choose (stockFrame SU.group)
lemma withinShip {o:Seat n} {I:Type*}[Fintype I] (X:Gleam.Wake.Vessel SU.group (More n) I) (i:I)(h:X.ua i=W.localFace n)(p:W.Pays r w)(ht:tenancy W n r clearance s o) (u:Signed)(b:Site (More n)):
    touched (X.ua i)⊆BlockP s o ∧ (X.crew i u).length≤clearance ∧ (X.viewFace i u b).1∈ (BlockP s o).image (affine u b):=by -- o binder
 have h':touched (X.ua i)⊆W.gateS r n := h ▸ (p.withinP W n).2.2.1
 have hp:(X.crew i u).length ≤ clearance :=(stockFrame SU.group).choose_spec _ _; refine ⟨h'.trans (fun i v=> ht (Corona.halo_mono (show r ≤ r+clearance+8 from by omega) (Subset.refl _) v)),hp,?_⟩
 let v:=affine u b; let Y:=X.ua i; have he:= Work.E01.base_touched Y; let f:= X.viewFace i u b; let q:= (f.1: Site (More n)); have hc:separation (v Y.1) (f.1) ≤ clearance:=(Work.E04.slot_separation (X.crew i u) (v Y.1)).trans hp
 obtain ⟨z,hz⟩:=(show Surjective v from (Push.Local.turnSites u b).surjective) (f.1)
 obtain ⟨m,a,b⟩:= halo_spec.mp (h' he); refine mem_image.mpr ⟨z,ht (halo_spec.mpr ⟨m,a,(separation_triangle m Y.1 z).trans ?_⟩),hz⟩
 rw [←hz] at hc; have ht:separation Y.1 z≤ clearance:= by simpa only [affine,v,separation_translate,separation_signed] using hc
 omega
end YM.CF.Buffered.EmberWind.Staff
