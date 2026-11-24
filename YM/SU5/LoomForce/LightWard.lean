import YM.SU5.LoomForce.FinePoly
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
open Next.Rank Spindle
open Buffered Pannier Pannier.Chancel Rous Afterglow
open Py Py.Rate Py.Rate.LocalLimit Preparation Preparation.Yoke
open Regis.Head Gleam Gleam.Wake Tempest
variable (B:ℕ)(R:ℤ)(x:Site N) {p:BudgetPoint}{K:Scree.Loom N}
local notation "M"=> More N
local notation "φ"=> fling 3 R N
local notation "J"=> Turn B
local notation "Σ"=> Panels B
local notation "ξ"=> node x
local notation "Ψ"=> affine (Signed.mirror 3) (haul N R)
local notation "V"=> inspectFoot p x
abbrev transit (x:Site N)(R:ℤ)(B:ℕ)(i:Panels B) : Face (Per (More N)):= if i.1 then sendV R (armFace B (node x) i.2.1) else armFace B (node x) i.2.1
noncomputable def readingFob : Vessel group (More N) (Panels B):=⟨fun i=>(transit x R B i,i.2.2)⟩
local notation "Θ"=> readingFob B R x

private lemma meterTall : ∃ C:ℕ, ∀ (F:PlaqAxes)(S:Signed), (skewSlot group (keelSlot F) S).length≤C:= by
 have hv(i:PlaqAxes)(t:Signed): ∀ᶠ k:ℕ in atTop,(skewSlot group (keelSlot i) t).length≤k:=eventually_ge_atTop _; exact (eventually_all.mpr (fun i:PlaqAxes=> eventually_all.mpr (hv i))).exists
noncomputable abbrev creditJ := meterTall.choose

variable (D:ℕ)(d':D≥12+B+creditJ+separation (node x) (sendSite R (node x)))
local notation "Q"=> BlockP D ξ
include d'
theorem zones {pS:BudgetPoint}(q:pS.B=B): inspected (offsetMask pS.B x) ⊆ Q ∧ (inspected (offsetMask pS.B x)).image Ψ ⊆ Q := by
 rw [q]; have he(i:Seat N)(p:i∈inspected (offsetMask B x)) : separation ξ i ≤ B+8:= by obtain ⟨k,q,t⟩ :=halo_spec.mp (Thirst.inspect _ p); exact (separation_triangle ..).trans (Nat.add_le_add (blocks_test.mp q) t)
 have hψ(i j:Seat N): separation (Ψ i) (Ψ j)= separation i j:=by simp [affine]
 refine ⟨fun i p=>blocks_test.mpr ((he i p).trans (by omega)),?_⟩; intro y t; obtain ⟨u,e,rfl⟩:=mem_image.mp t; refine blocks_test.mpr ((separation_triangle ξ (Ψ ξ) (Ψ u)).trans ?_); rw [hψ]; let m:=separation ξ (Ψ ξ); have hv:12+B+creditJ+m≤D:=d'; change m+_≤ D; have ht:=he u e; omega

theorem teacup (h:creditJ≤B) : (readingFob B R x).Ship Q B:=by
 let C:=separation ξ (Ψ ξ)
 have hp(i:Σ)(z:Seat N)(h:z∈ touched ((Θ).ua i)) : separation ξ z+creditJ ≤ D:=by
    have hv:12+B+creditJ+C≤D:=d'
    obtain ⟨i,g,x0⟩:=i; cases i
    · have hh:=blocks_test.mp (show z∈ BlockP B ξ from touches B ξ g h); omega -- notation capture x2
    change z∈touched (Face.send (Signed.mirror 3) (haul N R) (armFace B (node x) g)) at h; rw [Work.H03.touched_send] at h
    obtain ⟨y,hz,rfl⟩:= mem_image.mp h
    have hy:= blocks_test.mp (touches B ξ g hz)
    have hh:= separation_triangle ξ (Ψ ξ) (Ψ y); rw [show separation (Ψ ξ) (Ψ y)=separation ξ y from ?_] at hh; swap
    · simp [affine]
    change separation _ (Ψ _) + _ ≤ _; omega
 have hc(i:Σ)(u:Signed):((Θ).crew i u).length ≤creditJ:= meterTall.choose_spec _ _
 -- viewFace anchor via role length
 refine ⟨fun i y hi=>blocks_test.mpr (by have ht:=hp i y hi; omega),fun i u b=>?_,fun i t=> (hc i t).trans h⟩
 let k:=affine u b; let z:=(Θ).ua i; let f:= (Θ).viewFace i u b; let q:= (f.1: Site (More N)); have he: separation (k z.1) (f.1) ≤ creditJ:=(Work.E04.slot_separation ((Θ).crew i u) (k z.1)).trans (hc i u)
 obtain ⟨v,hv⟩:=(show Surjective k from (Push.Local.turnSites u b).surjective) (f.1); refine mem_image.mpr ⟨v,blocks_test.mpr ((separation_triangle ξ z.1 v).trans ?_),hv⟩; rw [←hv] at he; have ht:separation z.1 v ≤ creditJ:=by simpa [k,affine] using he
 have hz:= hp i z.1 (Work.E01.base_touched _); omega

variable (U:Pane N)
theorem enterMirror {α v:ℝ}(h:α<t)(c:Tiny Q U v)(u:ordinary (possession Q) α U)
    (pB:p.B=B) :
    Tiny (Spindle.patch B ξ) U v ∧ Tiny ((Spindle.patch B ξ).image (sendSite R)) U v ∧
      pingS t (offsetMask B x) U ∧ Tiny (Spindle.patch B ξ) (φ U) v ∧ pingS t (offsetMask B x) (φ U) := by
 obtain ⟨f,g⟩:=zones B R x D d' pB
 have hz:offsetMask B x⊆Q :=by
    rw [←pB]; exact (halo_foot p x).trans f
 rw [tilt_rule]
 have ht:(offsetMask B x).image Ψ⊆ Q:=by
    rw [←pB]; exact (image_subset_image (halo_foot p x)).trans g
 refine ⟨c.raise hz le_rfl, c.raise ht le_rfl, ?_, tugTiny _ _ _ (c.raise ht le_rfl),?_⟩ -- params
 · rintro y k; rw [pB] at f; refine (u y (mem_filter.mpr ⟨mem_univ _,fun i t=> f (mem_union_right _ (mem_biUnion.mpr ⟨y,mem_univ _,?_⟩))⟩)).trans_lt h; rwa [if_neg k]
 intro y k; rw [Face.send_price U y _ _ group.chord group.chord_inv (fun k g=> Gauge.chord_conj ..)]; rw [pB] at g
 refine (u _ (mem_filter.mpr ⟨mem_univ _,?_⟩)).trans_lt h; rw [Work.H03.touched_send]; refine Subset.trans (image_subset_image ?_) g; exact fun i (hi:i∈touched y)=> mem_union_right _ (mem_biUnion.mpr ⟨y,mem_univ _,by rwa [if_neg k] ⟩)
#print axioms enterMirror
end YM.CF.LitCurrent.Surplus
