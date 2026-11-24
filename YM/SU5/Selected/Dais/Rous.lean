import YM.SU5.Selected.Hill.Crete
import YM.SU5.Selected.Dais.Vega
import YM.SU5.Selected.Dais.Folio
import YM.SU5.FiniteGaugeData.Pannier.PaleFace
/-! One frame for comparison on the whole torus. Copy tollPole helper. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel.Rous
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate.Pannier
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
open Hill.Box Hill.Post Graph Next.Rank Tree
open scoped Classical
open Font
variable {j w k:ℕ}{M:Jill.Male} {n:Side} {γ t s u v δ δ' η τ ε a:ℝ}{r:Side} {A: Orbit n→Pane n}
def iceland (r:Side)(w:ℕ)(U:Pane n)(s:ℝ):Finset (Seat n) := univ.filter fun i=> Light r (menu U s) (w+1) i
lemma craneReady(r:Side)(w:ℕ)(p:0 <γ) : ∃ x> (0:ℝ),∀ (t:ℝ),0≤t→ t≤x→ ∀ {N:Side}(V:Pane N),
 Rightful (Lattice.halo w (iceland r w V t)) (let W:= columbia r (More N); gauge (W.foldAt V) V) 1 γ :=by
 let Y(x:SU.E):= ‖brand x-(brand 1)‖
 obtain ⟨e,V,h⟩:= tollPole (f:=Y) (((matter_cont.prodMk fund_cont).sub (continuous_const (y:=brand 1))).norm) (show Y 1<γ from by unfold Y; simpa using p)
 have hg: (0:ℝ)<r.val:= Nat.cast_pos.mpr r.property
 refine ⟨e/(4*r.val),by positivity,fun t a v N U=>?_⟩; let W:= columbia r (More N); let G:= W.foldAt U; let L:= gauge G U; let T:=menu U t; apply (riotPort ..).mpr; intro i p; obtain ⟨x,hx,q⟩:= halo_spec.mp (mem_filter.mp p).2.1; have he:Light r T 1 i.1:= ((mem_filter.mp hx).2).sees q
 have hP:Light r (menu L t) 1 i.1:=by rw [show menu L t=T from ?_]; exact he; unfold L T Hill.Box.menu; simp only [face_gauge,Gauge.chord_conj] -- tune
 have hl: ∃ V:W.Slice SU.group, L=W.drape V := by
    let f:W.Slice SU.group:=fun i=> L i.val; refine ⟨f,funext fun i=>?_⟩; by_cases w:i∈W.trunks; · have hp':L i=1:=W.compress U i w; exact hp'.trans (W.on_tree f ⟨i,w⟩).symm
    exact (W.off_tree f ⟨i,w⟩).symm
 obtain ⟨j,u⟩:=hl; exact h _ ((hP.link j u i.2 a).trans ((mul_comm ..)|>.le.trans ((le_div_iff₀ (by positivity :(0:ℝ)<4*r.val)).mp v))) -- tune
-- count omitted: seat rough area in transformed frame due A0, on ALL v ≤x, pay original flags
open Fixed.Extensive
lemma fallenB (C:Finset (Seat n)): ((modesIn n C)ᶜ : Finset (Single n)).card ≤ (Cᶜ : Finset (Seat n)).card*180:=by
 have hx:((modesIn n C)ᶜ : Finset (Single n))= univ.filter (fun i=> place_x i ∈ Cᶜ):= by ext i; simp [place_x] -- tune place_x node
 rw [hx]; exact Damask.hawk_budget Cᶜ -- maybe private type mismatch
lemma rough_count(U: Orbit n)(p:Roof n u δ k A)(v:s≤u): (menu (A U) s).card≤ ((roughness s U.1).card*4*((k+4)*2+1)^4)* Fintype.card PlaqAxes:=by
 let T:=A U; let S:= flags s T; have he: menu T s⊆ S×ˢ univ:=fun i x=> mem_product.mpr ⟨(flags_spec ..).mpr ⟨i,Work.E01.base_touched i, (mem_filter.mp x).2⟩,mem_univ _⟩; apply (card_le_card he).trans; rw [card_product,card_univ]; apply Nat.mul_le_mul_right; apply (card_le_card (halo_subset 0 S)).trans; have hx:= grease_f p U v 0 1; rw [Lattice.pull_id,zero_add,zero_add,one_pow,mul_one] at hx; exact hx
lemma countI (V:Pane n) : ((iceland r w V s)ᶜ:Finset (Seat n)).card ≤ (univ.filter fun i:Seat n=>¬ recess r (w+1) i).card + (menu V s).card*r.val^4:=by
 let P(i : Plane (More n)):= orbit r i.1
 let S:= menu V s; let X:= S.biUnion P; let T:= univ.filter fun i:Seat n=>¬recess r (w+1) i; have hx:X.card ≤ S.card*r.val^4:= card_biUnion_le.trans ((sum_le_sum fun x _=> orbit_bill x.1 r).trans_eq (by simp)); apply le_trans (b:=(T∪X).card); swap; · exact (card_union_le ..).trans (Nat.add_le_add_left hx _)
 apply card_le_card; intro i w; by_contra h; refine notMem_compl.mpr ?_ w; refine mem_filter.mpr ⟨mem_univ _,⟨?_, fun b t p=>?_⟩⟩
 · exact Classical.byContradiction fun u=> h (mem_union_left X (mem_filter.mpr ⟨mem_univ _,u⟩)) -- p
 exact h (mem_union_right T (mem_biUnion.mpr ⟨b,t,mem_filter.mpr ⟨mem_univ _,p⟩⟩))
-- translates. p, spark precondition.
open Dais.Parity
lemma aria (Q R: Op (Single n))(X:Finset (Seat n))(q:IsStarProjection Q)(p:IsStarProjection R)(g:0<t)(h:t≤1)(u:0≤ ε)(w:‖(Q-R)*Vo X‖≤ ε): Real.log (grip (tickA n) Q t).det.re-Real.log (grip (tickA n) R t).det.re ≤ (t^2)⁻¹ * ((Fintype.card (Single n):ℝ)*ε+((modesIn n X)ᶜ:Finset (Single n)).card * 2):=by
 let P:=tickA n; have hP:=Kea.cut_t n; let d:=grip P Q t-grip P R t; have he: ‖Q-R‖≤2:=(norm_sub_le ..).trans ((add_le_add (q.norm_le _) (p.norm_le _)).trans_eq (by ring)); have ht:‖d‖≤2:= (by rw [←mul_one d]; unfold d; exact grip_mono hP g.le h (by norm_num) 1 (Commute.one_right _) (by rwa [mul_one]))
 refine diff_charge (pow_pos g _) (grip_base hP p g.le h) (grip_base hP q g.le h) u ht (grip_mono hP g.le h u (Vo X) ?_ w)
 rw [touchP]; unfold Vo cutM Commute SemiconjBy; rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; congr 1; funext x; exact mul_comm ..
open Dais.Span
abbrev logo(t:ℝ)(j:ℕ)(M:Jill.Male)(U:Pane n):ℝ:=Real.log (grip (tickA n) (spar j M U) t).det.re/2
lemma aria_world (r:Side)(g:0<t)(e:t≤1)(a0:0≤ε)(p:0<δ)(Q:Winter j δ n η w ε)(U:Pane n)(v:Guard U δ')(v':δ'≤δ)(d: Brace.Sparkle n δ' M j)(V:Sods.Cart (More n))(q:Rightful (Lattice.halo w (iceland r w U s)) (Lattice.gauge V U) 1 η)(p':0≤δ') :
 logo t j M U ≤ Real.log (grip (tickA n) (spar j M (1:Pane n)) t).det.re/2 +(t^2)⁻¹ /2 * ((Fintype.card (Single n):ℝ)*ε+((modesIn n (iceland r w U s))ᶜ:Finset (Single n)).card * 2):=by
 let T:=gauge V U; let R:=spar j M T; let H:=iceland r w U s; have hp:=d.projection T (v.cov V); have h1:=d.projection 1 (guard0 p'); have ht : ‖(R-spar j M (1:Pane n))*Vo H‖ ≤ ε:= hearthB_wind Q p.le ((v.cov V).shrink v') q (b:=false)
 have he: logo t j M U= logo t j M T:= by
    unfold logo; rw [show T=gauge V U from rfl,d.covary ..]; rw [show grip (tickA n) (twist (tradew n V) (spar j M U)) t= twist (tradew n V) (grip (tickA n) (spar j M U) t) from ?_] -- dangerous target underscores; try
    · rw [Kea.det_d]
    · rw [grip_twist,Cascade.tick_g]
    exact v
 rw [he]; unfold logo; linarith only [aria R (spar j M (1:Pane n)) _ hp h1 g e a0 ht]
end YM.CF.Pannier.Chancel.Rous
#print axioms YM.CF.Pannier.Chancel.Rous.aria_world
