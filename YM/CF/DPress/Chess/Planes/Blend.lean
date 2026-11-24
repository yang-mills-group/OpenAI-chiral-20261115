import YM.CF.DPress.Chess.Planes.Rock
import YM.CF.DPress.Motto.Frame
-- now use these very Blend weights; mode() even satisfied on every sweep used by comparator. At an aligned wall on any level groups Π factors according to their target site, **all links permitted at true field only** with rail margin, independent of the actual size, J,b,x, h, Legacy. Consumers use win.
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Lattice Finset Fock Laurent Spire Skye Scroll Lat Rush Wilson Py.Kay.WagesC RG
open Cube (More assembly)
open scoped Topology BigOperators Classical
namespace Wall
variable (W:Wall){n:Side}{L:Side}{μ:ℕ}
def score (L:Side)(μ:ℕ)(x: Seat n): Support (More n):= univ.filter fun i=> separation x i ≤ μ ∧ fort L μ i
lemma score_v(x y:Seat n): y∈ score L μ x ↔ separation x y ≤ μ ∧ fort L μ y:=by unfold score; rw [mem_filter]; simp
lemma carts (p:deed n L)(v:μ≤L.val)(x:Seat n): (score L μ x).Nonempty:=by obtain ⟨y,f,s⟩:= flagsJ L x p v; exact ⟨y,(score_v ..).2 ⟨s,f⟩⟩
def atlas(p: deed n L)(h:μ≤ L.val):Blend n μ where
 μ x y:= if y∈score L μ x then ((score L μ x).card :ℝ)⁻¹ else 0
 p x y:=by split <;> positivity
 card x:=by
   rw [← Finset.sum_filter]; let S:=score L μ x; have hp:= (carts p h x); rw [show univ.filter _= score L μ x from ?_,sum_const,nsmul_eq_mul,mul_inv_cancel₀ (by positivity)]; ext; simp -- tune
 near x y t:=by split at t <;> first | exact ((score_v ..).1 (by assumption)).1 | exact (t rfl).elim
lemma tintP (p:deed n L) (s:Sweep n)(t:gridOK L s)(x:Seat n):score L μ (boxA s x)=(score L μ x).map (boxA s).toEmbedding:= by ext y; obtain ⟨y,rfl⟩:=(boxA s).surjective y; rw [score_v,mem_map_equiv,Equiv.symm_apply_apply,score_v, sitT, through L p s t]
lemma evenS (p:deed n L)(s:Sweep n)(t:gridOK L s)(v:μ≤ L.val):(atlas p v).even s:=by
 suffices h:∀ i j,(atlas p v).μ (boxA s i) (boxA s j)=(atlas p v).μ i j from (fun i j=> by simpa only [Equiv.apply_symm_apply] using (h ((boxA s).symm i) ((boxA s).symm j)).symm)
 intro i j; dsimp only [atlas]; rw [tintP p s t i, card_map]; simp
structure Design (L:Side)(B:Blend n μ):Prop where
 deed : Wall.deed n L
 evenS : ∀ s:Sweep n,gridOK L s→B.even s
 blank : ∀ x y,B.μ x y ≠0→ fort L μ y
lemma designed (p:deed n L)(v:μ≤L.val) : Design L (atlas p v):=⟨p,fun s t=> evenS p s t v,fun i j t=>(score_v ..|>.1 (by by_contra z; exact t (if_neg z))).2⟩
variable (B: Blend n μ)(t a:ℝ)
open Blend
abbrev system (S:Support (More n))(x:Pane n) := ∑ i∈ (κN n μ).filter (fun i=> i.2∈ S), B.φΩ i*a*μM (v:=t) i.2 x
include W
lemma stars (i:Seat n)(u:rail+4≤μ)(p:i∈W.crop n μ): halo 2 (Plaque.haloW i)⊆ W.crop n rail:=by
 intro j v; obtain ⟨k,t,u'⟩:=halo_spec.mp v; obtain ⟨x,l,v⟩:=halo_spec.mp t; rw [mem_singleton] at l; subst x
 apply W.surrounding (r:=4) u n; exact halo_spec.mpr ⟨_,p,(separation_triangle _ k _).trans (by omega)⟩
lemma reads (u:rail+4≤μ) : LocalOn (W.crop n rail) (system B t a (W.crop n μ)) :=by
 intro x y v; unfold system; apply sum_congr rfl; intro i p; rw [stool i.2 _ _ (agrees_mono v (Finset.coe_subset.mpr (W.stars i.2 u ((mem_filter.mp p).2))))]
lemma stamp (h:Design L B)(p:W.aligned L)(x: Pane n) : system B t a (W.crop n μ) (W.shine n x) = system B t a (W.negZ (W.crop n μ)) x:=by
 let M:=W.joy n; let R:=τσ M; have hp(i:Seat n × Seat n):i.2∈ W.negZ (W.crop n μ) ↔ (R i).2∈ W.crop n μ:=by rw [W.swipe,show (R i).2=(W.site n).symm i.2 from rfl,W.itself n]
 -- nesting? Goal outer
 symm; apply sum_equiv R; intro i; rw [mem_filter (s:=κN n μ),mem_filter (s:=κN n μ)]; exact and_congr (similar ..) (hp i)
 intro i _; rw [show B.φΩ (R i)=_ from h.evenS M (W.grid n p) i.1 i.2,show μM (v:=t) (R i).2 (W.shine n x)=_ from transitμ M i.2 x]
lemma page (h:Design L B)(p:W.aligned L)(u:0<μ) (x: Pane n): (B.Φ (h:=t) a x)= system B t a (W.crop n μ) x +system B t a (W.crop n μ) (W.shine n x):=by
 rw [W.stamp B t a h p]; unfold Φ system; rw [sum_filter (s:=κN n μ),sum_filter (s:=κN n μ),←sum_add_distrib]; refine sum_congr rfl (fun i _=>?_); by_cases t': B.φΩ i=0; simp [t']
 rcases W.νlive p h.deed i.2 (h.blank i.1 i.2 t') with v|v; rw [if_pos v,if_neg (Finset.disjoint_left.mp (W.night (a:=μ) (b:=μ) (by omega) n) v), add_zero]; rw [if_pos v,if_neg (Finset.disjoint_left.mp (Disjoint.symm (W.night (a:=μ) (b:=μ) (by omega) n)) v),zero_add] -- tune
omit W
lemma system_C (S:Support (More n)):Envelope (system B t a S) := Envelope.sum _ _ fun i=> (Envelope.const (B.φΩ i * a)).mul (by
 let G:= Plaque.feeW (n:=More n) i.2
 obtain ⟨z,u⟩:= isCompact_range (Plaque.contFee i.2 (n:=More n)|>.norm)|>.bddAbove
 refine show Envelope (μM (v:=t) i.2) from ⟨measurable_μM _, |z|,fun x=>?_⟩
 unfold μM Set.indicator; split; exact (u (Set.mem_range_self _)).trans (le_abs_self _); rw [norm_zero]; exact abs_nonneg _)
end Wall
end YM.CF.DPress.Chess
