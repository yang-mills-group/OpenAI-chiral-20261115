import YM.SU5.Relativistic.Rebuke
import YM.CF.BPress.Spin.Touches
import Verses.Checkup
import YM.CF.Cubes.Inside
import YM.Work.E08
/-!
# One frame from positive curvature bound on the actually paid sites.
Use Work.E08 axial coarse estimate (works here directly on the gauge grid),
then shift to fixed continuous stencil rather than picking a frame measurably. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate.Pannier
open Work.E08
variable {n:Side}{k r m:ℕ}

open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {u o:Seat n} {r k:ℕ}
private lemma precinct (r:ℕ)(p:u∈ BlockP r o)(y:Seat n)(h:y∈ visits o (march o u 1)): y∈ BlockP r o:=by
 obtain ⟨v,t,e⟩:= march_visit o u 1 _ h; obtain ⟨g,x⟩:= box_test.mp (lift_mem_box (blocks_test.mp p)); apply blocks_test.mpr; rw [t,add_comm]; apply separation_box_add _ (box_test.mpr ?_);
 constructor <;> intro i
 · have ht:= e.left i; change min (0:ℤ) _ ≤ _ at ht; specialize g i; change _ ≤ _ at g; omega -- align boxX ∀
 have ht:=e.right i; change _ ≤ max (0:ℤ) _ at ht; specialize x i; omega
private lemma stampG_cov(o:Seat n)(U:Pane n)(g:Seat n→SU.E)(i:Seat n):stampG o (gauge g U) i=g o*stampG o U i*(g i)⁻¹:=by unfold stampG; rw [travel_gauge,Cube.arrive]
private lemma costsWalk (D:Finset (Seat n))(U:Pane n)(p:ℝ)(h:∀ i∈ leaks D,SU.group.chord (U i) ≤ p)(L:Lattice.Walk)(i:Seat n)(u:∀ z∈ visits i L,z∈ D): SU.group.chord (travel U i L) ≤ L.length*p:=by
 induction L generalizing i with
 | nil=>rw [travel,SU.group.chord_one]; simp
 | cons a L ih=>
   have he : i∈D:=u i List.mem_cons_self
   have hx:i+a.vec∈D:=by apply u; cases L <;> simp [visits]
   have hl:SU.group.chord (a.read U i) ≤ p:=by
      obtain ⟨b,v |v⟩:=a
      · exact h (i,b) (mem_filter.mpr ⟨mem_univ _,he,hx⟩)
      change SU.group.chord (U (i-step b,b))⁻¹ ≤ _; rw [SU.group.chord_inv]; apply h; exact mem_filter.mpr ⟨mem_univ _,by simpa [sub_eq_add_neg,Step.vec] using hx, (show i-step b+step b∈D from by rwa [sub_add_cancel])⟩
   rw [travel]; apply (SU.group.chord_triangle _ _).trans; exact ((add_le_add hl (ih _ (fun z h=>u z (List.mem_cons_of_mem _ h)))).trans_eq (by rw [List.length_cons]; push_cast; ring))
private lemma travelsQ (o:Seat n)(D:Finset (Seat n))(U:Pane n)(p:ℝ)(h:∀ i∈leaks (BlockP r o),SU.group.chord (U i) ≤ p)(w:0≤p)(i:Seat n)(t:i∈BlockP r o): SU.group.chord (stampG o U i) ≤ 4*r*p:= (costsWalk _ _ p h (march o i 1) o (precinct r t)).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (march_len o i 1 ((separation_comm ..).trans_le (blocks_test.mp t)))) w)
private abbrev CircaV (r:ℕ):= (16:ℝ)*(2*((r:ℝ)+1)+1)^5 * (Fintype.card PlaqAxes:ℝ)
open BPress BPress.Spin
abbrev sticker (r:ℕ)(v:ℝ) := sphereRate*((8*(r:ℝ)+1)*Circa r*v)
lemma stampG_prec {r:ℕ}(ν:ℝ)(h:0≤ν){t:ℕ}(hu:2*(r+1)<(More n).val)(hz:r+1 ≤ t)(o:Seat n)(U:Pane n)(V:Disjoint (BlockP t o) (flags ν U)): Rightful (BlockP r o) (gauge (stampG o U) U) 1 (sticker r ν):=by
 let A:= ((8*(r:ℝ)+1)*Circa r)+1
 have hq:0≤ Circa r:=by unfold Circa; positivity
 have hp:0<A:=by unfold A; positivity
 obtain ⟨g,q⟩:= Work.E08.axial_patch (G:=SU.group) o U r (r+1) le_rfl hu ν h (fun i he k=> by
   by_contra! x; let y:Face _:= (i,k); exact disjoint_left.mp V (blocks_test.mpr (he.trans hz)) ((flags_spec ..).mpr ⟨y,Work.E01.base_touched y,x⟩))
 let W:= Lattice.gauge g U; let ℓ:=stampG o U; let F:=stampG o W; let t':=Circa r*ν; have hx':0≤t':=by unfold t'; positivity
 let D:= BlockP r o
 have hx(b)(v:b∈leaks D):SU.group.chord (W b)≤ t':=by
    apply (q b (blocks_test.mp (mem_filter.mp v).2.1)).trans; unfold t' Circa; push_cast; rfl -- le
 have hw(i)(v:i∈ D):SU.group.chord (F i)≤ 4*r*t':= travelsQ o D W _ hx hx' i v
 apply (riotPort ..).2; rintro i hi; have he (x:E):‖brand x-brand (1:E)‖ ≤ sphereRate * group.chord x:=by rw [Prod.norm_def]; rw [←chord.one]; exact max_le (sphereRate_cost.bot ..) (sphereRate_cost.top ..)
 apply (he _).trans; unfold sticker; apply mul_le_mul_of_nonneg_left _ sphereRate_cost.positive.le; obtain ⟨a,u⟩:= (mem_filter.mp hi).2; let y:=i.1; let z:=i.1+step i.2; have ht:SU.group.chord (Lattice.gauge F W i)= SU.group.chord (Lattice.gauge ℓ U i):=by
   rw [show Lattice.gauge F W i=g o*Lattice.gauge ℓ U i*(g o)⁻¹ from ?_,SU.group.chord_conj]; change stampG o (gauge g U) y*(g y*U i*(g z)⁻¹)*(stampG o (gauge g U) z)⁻¹ = _*(stampG o U y*U i*(stampG o U z)⁻¹)*_; rw [stampG_cov,stampG_cov]; group
 rw [← ht,Lattice.gauge]; apply (SU.group.chord_triangle _ _).trans; rw [SU.group.chord_inv]; refine (add_le_add ((SU.group.chord_triangle _ _).trans (add_le_add (hw y a) (hx i hi))) (hw z u)).trans ?_
 apply le_of_eq; unfold t'; ring
end YM.CF.Pannier.Chancel
