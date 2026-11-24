import YM.SU5.FiniteGaugeData.Pannier.Trefl
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
open scoped Matrix.Norms.Frobenius in
private lemma tollPole {f:SU.E→ℝ}(p:Continuous f){a:ℝ}(h:f 1<a):∃ x>(0:ℝ),∀ y:SU.E,SU.group.chord y ≤ x → f y ≤ a:=by
 let V:= {y:SU.E | a≤ f y}; have hp:IsCompact V:=(isClosed_le continuous_const p).isCompact
 have he(y):f y ≥ a → SU.group.chord y>0:=by
    intro hz; by_contra! hk; have hv:SU.group.chord y=0:=le_antisymm hk (SU.group.chord_nonneg _); suffices y=1 from h.not_ge (this ▸ hz)
    apply group.mat_injective; rw [Gauge.mat_one]; rw [Gauge.chord,div_eq_zero_iff] at hv; exact sub_eq_zero.mp (norm_eq_zero.mp (hv.resolve_right (Real.sqrt_pos.mpr (by exact_mod_cast group.dimPos)).ne'))
 by_cases g:V.Nonempty; swap
 · exact ⟨1,one_pos,fun y _=>(lt_of_not_ge fun k=> g ⟨_,k⟩).le⟩
 obtain ⟨y,hy,hs⟩:=hp.exists_isMinOn g ((show Continuous SU.group.chord from group.continuous_chord).continuousOn)
 refine ⟨SU.group.chord y/2,half_pos (he y hy),fun z t=>?_⟩; by_contra! hv; exact (lt_of_le_of_lt t (half_lt_self (he y hy))).not_ge (hs (show z∈V from hv.le))

open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {u o:Seat n} {r k:ℕ}
abbrev BlockP (r:ℕ)(o:Seat n):= Lattice.halo r ({o}:Finset (Seat n))
abbrev stampG (o:Seat n)(U:Pane n) (x:Seat n) := travel U o (march o x 1)
lemma blocks_test : u∈ BlockP r o↔ separation o u ≤r:=by rw [BlockP,halo_spec]; simp
lemma blocks_rest (o:Seat n)(r:ℕ)(i:Axis) : cows i (BlockP r o) (2*r):=by
 refine ⟨ (natural o i)-(r:ℤ),?_⟩; intro x h; let Z:=Lattice.lift (x-o); let l:=natural o; have p:= (component_le (x-o) i).trans ((separation_comm ..).trans_le (blocks_test.mp h))
 have ht: (Z i).natAbs≤r:=p
 refine ⟨ Z i+l i,by unfold l; omega,by unfold l; omega,?_⟩
 rw [show (((Z i+l i):ℤ): Per (More n)) = wrap (More n) (Z+l) i from rfl, map_add,nat_true,wrap_lift, sub_add_cancel]
private lemma precinct (r:ℕ)(p:u∈ BlockP r o)(y:Seat n)(h:y∈ visits o (march o u 1)): y∈ BlockP r o:=by
 obtain ⟨v,t,e⟩:= march_visit o u 1 _ h; obtain ⟨g,x⟩:= box_test.mp (lift_mem_box (blocks_test.mp p)); apply blocks_test.mpr; rw [t,add_comm]; apply separation_box_add _ (box_test.mpr ?_);
 constructor <;> intro i
 · have ht:= e.left i; change min (0:ℤ) _ ≤ _ at ht; specialize g i; change _ ≤ _ at g; omega -- align boxX ∀
 have ht:=e.right i; change _ ≤ max (0:ℤ) _ at ht; specialize x i; omega
lemma stampG_consistent (o:Seat n){U V:Pane n} (w: Lattice.Agrees (BlockP r o) U V)(p:u∈BlockP r o) : stampG o U u=stampG o V u:= travel_local _ _ _ _ (fun i h g=> w i (precinct r p _ h) (precinct r p _ g))
lemma stampG_cont (o:Seat n) :Continuous (stampG o) := continuous_pi fun i=> travel_cont o _
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
abbrev Circa (r:ℕ):= (16:ℝ)*(2*((r:ℝ)+1)+1)^5 * (Fintype.card PlaqAxes:ℝ)
lemma stampG_price (r:ℕ)(γ:ℝ)(p:0<γ): ∃ τ>(0:ℝ),∀ (ν:ℝ)(h:0≤ν), ν≤τ → ∀ {n:Side}{t:ℕ}, 2*(r+1)<(More n).val → r+1 ≤ t → ∀ (o:Seat n)(U:Pane n),Disjoint (BlockP t o) (flags ν U) →
    Rightful (BlockP r o) (gauge (stampG o U) U) 1 γ:=by
 let Y(x:SU.E):= ‖brand x-(brand 1)‖
 obtain ⟨δ,tD,w⟩:= tollPole (f:=Y) (((matter_cont.prodMk fund_cont).sub (continuous_const (y:=brand 1))).norm) (show Y 1<γ from by unfold Y; simpa using p)
 let A:= ((8*(r:ℝ)+1)*Circa r)+1
 have hq:0≤ Circa r:=by unfold Circa; positivity
 have hp:0<A:=by unfold A; positivity
 refine ⟨δ/A,div_pos tD hp,fun ν h v {n t} hu hz o U V=>?_⟩
 obtain ⟨g,q⟩:= Work.E08.axial_patch (G:=SU.group) o U r (r+1) le_rfl hu ν h (fun i he k=> by
   by_contra! x; let y:Face _:= (i,k); exact disjoint_left.mp V (blocks_test.mpr (he.trans hz)) ((flags_spec ..).mpr ⟨y,Work.E01.base_touched y,x⟩))
 let W:= Lattice.gauge g U; let ℓ:=stampG o U; let F:=stampG o W; let t':=Circa r*ν; have hx':0≤t':=by unfold t'; positivity
 let D:= BlockP r o
 have hx(b)(v:b∈leaks D):SU.group.chord (W b)≤ t':=by
    apply (q b (blocks_test.mp (mem_filter.mp v).2.1)).trans; unfold t' Circa; push_cast; rfl -- le
 have hw(i)(v:i∈ D):SU.group.chord (F i)≤ 4*r*t':= travelsQ o D W _ hx hx' i v
 apply (riotPort ..).2; rintro i hi; apply w _; obtain ⟨a,u⟩:= (mem_filter.mp hi).2; let y:=i.1; let z:=i.1+step i.2; have ht:SU.group.chord (Lattice.gauge F W i)= SU.group.chord (Lattice.gauge ℓ U i):=by
   rw [show Lattice.gauge F W i=g o*Lattice.gauge ℓ U i*(g o)⁻¹ from ?_,SU.group.chord_conj]; change stampG o (gauge g U) y*(g y*U i*(g z)⁻¹)*(stampG o (gauge g U) z)⁻¹ = _*(stampG o U y*U i*(stampG o U z)⁻¹)*_; rw [stampG_cov,stampG_cov]; group
 rw [← ht,Lattice.gauge]; apply (SU.group.chord_triangle _ _).trans; rw [SU.group.chord_inv]; refine (add_le_add ((SU.group.chord_triangle _ _).trans (add_le_add (hw y a) (hx i hi))) (hw z u)).trans ?_
 calc _ = (A-1)*ν:= by unfold A t'; ring
      _ ≤ ν*A:= by nlinarith only [h]
      _ ≤ _ := (le_div_iff₀ hp).1 v
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.stampG_price
