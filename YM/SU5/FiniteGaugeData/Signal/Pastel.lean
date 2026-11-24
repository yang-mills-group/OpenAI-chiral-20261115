import YM.SU5.FiniteGaugeData.Signal.Migrations
import YM.Work.E08
/-! # Buying patch around fixed-tile observations. BOREL selected rotations
 No global gauge assumption; twists follow the local small-plaquette criterion. Use of
 `Wide` stencils to see first-pane. Prices from this same Pane. -/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Advance Reef Hom Tenant Branch
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical
namespace Pastel
variable {N:Side}{i j k d:ℕ}{a b u v:ℝ}
open scoped Matrix.Norms.Frobenius in
private lemma native (x:ℝ)(f:E→ℝ)(c:Continuous f)(p:f 1<x): ∃ y:ℝ,0<y∧∀ v:E, group.chord v≤y→f v<x:=by
 let V:={z | x ≤ f z}; have hp:IsCompact V:=(isClosed_le continuous_const c).isCompact; have he(y:E)(v:y∈V): group.chord y>0:=by
    by_contra! k; have hv:group.chord y=0:=le_antisymm k (group.chord_nonneg _); apply p.not_ge; suffices y=1 from this ▸ v
    apply group.mat_injective; rw [Gauge.mat_one]; rw [Gauge.chord,div_eq_zero_iff] at hv; exact sub_eq_zero.mp (norm_eq_zero.mp (hv.resolve_right (Real.sqrt_pos.mpr (by exact_mod_cast group.dimPos)).ne'))
 by_cases g:V.Nonempty; swap; · exact ⟨1,one_pos,fun y _=> lt_of_not_ge fun k=> g ⟨y,k⟩⟩
 obtain ⟨y,hy,hs⟩:= hp.exists_isMinOn g group.continuous_chord.continuousOn
 refine ⟨group.chord y/2,half_pos (he y hy),fun z t=>?_⟩; by_contra! h; exact ((hs (show z∈V from h)).trans_lt (t.trans_lt (half_lt_self (he y hy)))).false
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (x:Seat N)
local notation "G"=> Seat N→SU.E
local notation "U" i=> Branch.bay (terr (More N)) x i

def color (g:Seat N→SU.E)(A:Support (More N))(V: Pane N):ℝ:= Tulip.fare A (profile (gauge g V)) 1
lemma color_nn (g: G)(A:Support (More N))(V:Pane N):0≤color g A V:=fare_t ..
lemma color_cont (g:G)(A:Support (More N)):Continuous (color g A):=by unfold color Tulip.fare; refine continuous_finsetSum _ fun i _=> (((continuous_apply i).comp (Dial.profile_c.comp ?_)).sub continuous_const).norm; unfold Lattice.gauge; fun_prop
lemma color_local (g:G)(A:Support (More N))(V W:Pane N)(p:Agrees A V W): color g A V=color g A W:=by
 unfold color Tulip.fare; apply sum_congr rfl; intro i v; rw [show profile (gauge g V) i= profile (gauge g W) i from ?_]; funext j; unfold profile Lattice.gauge; rw [p i (mem_filter.mp v).2.1 (mem_filter.mp v).2.2]
lemma light (p:0 ≤ a)(V:Pane N)(g:G) (h:∀ b∈ leaks (U i), ‖brand (gauge g V b) -1‖≤ a) : color g (U i) V ≤ (64*((i:ℝ)+1)^4)*a :=by
 unfold color Tulip.fare; refine (sum_le_sum (g:=fun _ => a) ?_).trans ?_; swap
 · let S:=U i; rw [sum_const,nsmul_eq_mul]; have he: (leaks S).card ≤ S.card*4:=le_trans (card_le_card (t:=S×ˢ(univ:Finset Axis)) (fun i hi=> mem_product.mpr ⟨(mem_filter.mp hi).2.1, mem_univ _⟩)) ((card_product ..).trans_le (by simp [Axis])); have hp : (((leaks S).card:ℕ):ℝ) ≤ S.card*4:=by exact_mod_cast he
   apply mul_le_mul_of_nonneg_right _ p; have hx: (S.card:ℝ)≤16*((i:ℝ)+1)^4 := Tenant.reach ..; change ((leaks S).card:ℝ)≤_; linarith
 intro i v; apply (pi_norm_le_iff_of_nonneg p).2; rintro (_|_); swap; · exact h _ v
 change ‖star (brand (gauge g V i))-1‖≤_; nth_rw 1 [←star_one (R:=Twig)]; rw [←star_sub,norm_star]; exact h i v

omit x
lemma lit (a:ℝ)(p:0<a)(i:ℕ):∃ h:ℝ,0<h∧∀ N:Side,2*(i+1)<(More N).val→∀ (x:Seat N)(u:ℝ),0 ≤ u→u≤h→∀ (V:Pane N),Healthy u (bay (terr (More N)) x (i+1)) V→∃ g:Seat N→SU.E, color g (bay (terr (More N)) x i) V<a:=by -- notation U x binds global variable id qual? when omit shadow hygiene U will refer implicit global section..tune
 let f(x:E):= ‖brand x-1‖; let Q:=(64:ℝ)*((i:ℝ)+1)^4; let d:=a/2/Q; have hp:0<Q:=by unfold Q; positivity
 have hd: f 1 < d:= by unfold f; rw [brand_one,sub_self,norm_zero]; unfold d; positivity
 obtain ⟨b,ht,h⟩:= native d f (spinD.sub continuous_const|>.norm) hd
 let A:ℝ:= 16*(2*((i:ℝ)+1)+1)^5* Fintype.card PlaqAxes; have he:0<A:=by unfold A; haveI: Nonempty PlaqAxes:= ⟨⟨(0,1),by decide⟩⟩; positivity
 refine ⟨b/A,div_pos ht he,fun N v x k w u' V t=>?_⟩
 obtain ⟨g,hg⟩:= Work.E08.axial_patch x V i (i+1) le_rfl v _ w (fun y hy p=> le_of_not_gt fun l=> Finset.disjoint_left.mp t ((bay_mem _).2 hy) ((flags_spec ..).mpr ⟨(y,p), Work.E01.base_touched _,l⟩))
 refine ⟨g,(light x (i:=i) (a:=d) (by unfold d; positivity) V g ?_).trans_lt (lt_of_eq_of_lt (by unfold d; change Q*_=_; field_simp : Q*d=a/2) (half_lt_self p))⟩
 intro j v; have hs:= hg j ((bay_mem _).1 ((mem_filter.mp v).2.1)); apply (h _ _).le; push_cast at hs; exact hs.trans ((mul_comm A k).trans_le ((le_div_iff₀ he).1 u'))

section b
variable (S:Support (More N))(T:Support (More N))(u d:ℝ)
-- compactness of Healthy, not support of color. can then fix on first-pane
private def pick_gauge (L:List (Seat N→E))(V:Pane N): G:= match L with
 | [] => 1
 | i::L=> if color i S V <d then i else pick_gauge L V
lemma brochure (h:∀ (V:Pane N),Healthy u T V→∃ g, color g S V < d):∃ f:Pane N→ (Seat N→E), Measurable f ∧ LocalOn S f ∧ ∀ V:Pane N,Healthy u T V → color (f V) S V < d:=by
 let C:= {V:Pane N| Healthy u T V}; have t : IsCompact C:=(healthy_closed u T).isCompact
 let B(g:Seat N→E):= {V:Pane N| color g S V<d}; have hp(g):IsOpen (B g):= isOpen_lt (color_cont g S) continuous_const
 obtain ⟨P,p⟩:= t.elim_finite_subcover B hp (fun x v=>by obtain ⟨g,w⟩:=h x v; exact Set.mem_iUnion.mpr ⟨g,w⟩)
 have ht (L:List (Seat N→E)): Measurable (pick_gauge S d L)∧ LocalOn S (pick_gauge S d L) ∧∀ V:Pane N,(∃ i∈L,V∈B i)→color (pick_gauge S d L V) S V<d:=by
    induction L with
    | nil=> exact ⟨measurable_const,fun _ _ _=>rfl, fun _ v=>(by simp at v)⟩
    | cons i L ih=>
                   have he(V):pick_gauge S d (i::L) V=if V∈B i then i else pick_gauge S d L V:=by rw [pick_gauge]; split <;> rename_i j; exact (if_pos j).symm; exact (if_neg j).symm
                   refine ⟨?_,fun x y u=>?_,fun x w=>?_⟩
                   · rw [funext he]; exact Measurable.ite (hp i).measurableSet measurable_const ih.1
                   · unfold pick_gauge; rw [color_local i S x y u,ih.2.1 x y u]
                   rw [he]; split; assumption
                   apply ih.2.2; obtain ⟨j,hj,h⟩:=w; obtain hj|hj:= List.mem_cons.mp hj; · subst j; contradiction
                   exact ⟨j,hj,h⟩
 let L:=P.toList; refine ⟨pick_gauge S d L,(ht _).1,(ht _).2.1,fun x k=>?_⟩; have he:=p k; obtain ⟨i,hp,t⟩:=Set.mem_iUnion₂.mp he; exact (ht L).2.2 x ⟨i,by simpa [L] using hp,t⟩
end b
end Pastel
end YM.CF.Signal
