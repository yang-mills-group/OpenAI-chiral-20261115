import YM.SU5.Reconstruction.Anvil.OpCoin
import YM.SU5.Reconstruction.Anvil.Plate
/-! # Iterated passage on horizontal lengths. Normalize after limits with WOT in
 corresponding phases. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace OS Semigroup Price Terrain ConePrice Analysis Sail
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
variable {ι:Type*} {H : Hilbert} {a: Axis} (S:OS.Semigroup H a) (T:ℝ)
variable {A B:H.Op} (L R:H) {X Y:ι→ H.Op} {u v:ℝ} (y:Bool)(z:Wage)
local notation "PP" u:max v:max=> vertical T u v
local notation "Fm" u:max v:max=> (vertical T u v).sale y S
-- index i prices
section one
variable (l:Filter ι)[l.IsCountablyGenerated] {r s:ι→ℝ}
variable (p:(vertical T u v).permeates a y z)(qn:∀ᶠ i in l,(vertical T (r i) (s i)).permeates a y z)
   (U:Tendsto r l (𝓝 u))(V:Tendsto s l (𝓝 v))
local notation "Q"=> vertical T u v
local notation "Pq" i:max=> vertical T (r i) (s i)
lemma contWidth (x:ℂ):Continuous (fun t:ℝ=> onlyTime a ((t:ℂ)+x)):= continuous_pi fun i=>by by_cases p:i=a <;> simp [onlyTime,p] <;> fun_prop -- redundant
include U V
set_option maxHeartbeats 200000 in
private lemma duties (a:Axis): Tendsto (fun i => (Pq i).entry a y z) l (𝓝 ((Q).entry a y z)) ∧ Tendsto (fun i => (Pq i).compare a y z) l (𝓝 ((Q).compare a y z)) ∧ Tendsto (fun i => (Pq i).leaves a y z) l (𝓝 ((Q).leaves a y z)):= by
 let H:= U.prodMk_nhds V
 let Q'(x:ℝ × ℝ):= vertical T x.1 x.2; let Y:(ℝ × ℝ) := (u,v); have e(k:Axis):Continuous (fun x:ℝ=>onlyTime k (x:ℂ)):= by simpa only [add_zero] using contWidth (a:=k) 0
 have h1:Continuous (fun x:ℝ × ℝ=> (Q' x).entry a y z):=by cases y<;> simp only [Q',entry,if_false,reduceCtorEq,if_true]<;> fun_prop
 have h2:Continuous (fun x:ℝ × ℝ=> (Q' x).compare a y z):=by cases y<;> simp only [Q',Price.compare,if_false,reduceCtorEq,if_true]<;> (apply continuous_pi; intro k; by_cases p:k=a <;> simp [onlyTime,p] <;> fun_prop)
 have h3:Continuous (fun x:ℝ × ℝ=> (Q' x).leaves a y z):=by cases y<;> simp only [Q',leaves,if_false,reduceCtorEq,if_true]<;> (apply continuous_pi; intro k; by_cases p:k=a <;> simp [onlyTime,p] <;> fun_prop)
 let w i:=(r i,s i)
 have hu:Tendsto w l (𝓝 (u,v)):= H
 change Tendsto ((fun i=> (Q' i).entry a y z) ∘ w) _ (𝓝 ((Q' Y).entry a y z)) ∧ Tendsto ((fun i=> (Q' i).compare a y z) ∘ w) _ (𝓝 ((Q' Y).compare a y z)) ∧ Tendsto ((fun i=> (Q' i).leaves a y z) ∘ w) _ (𝓝 ((Q' Y).leaves a y z))
 -- goal exact pattern explicit
 exact And.intro ((h1.tendsto Y).comp hu) ⟨(h2.tendsto Y).comp hu,(h3.tendsto Y).comp hu⟩
include p qn
lemma iteration (v1:Limited l X A)(v2:Pearl l Y B) : Tendsto (fun i=> (vertical T (r i) (s i)).sale y S (X i) (Y i) L R z) l (𝓝 ((Q).sale y S A B L R z)):= by
 let h:= duties T y z l U V a; let L0:= earns_per l S p.1.le h.1 (qn.mono (fun i v=>v.1.le)) -- usage check
 let L1:= earns_per l S p.2.1.le h.2.1 (qn.mono (fun i v=>v.2.1.le)); let L2:= earns_per l S p.2.2.le h.2.2 (qn.mono (fun i v=>v.2.2.le)); cases y
 · exact (((((v1.toLeft L1).toLeft v2).toLeft L0).toRight L2)).confirms L R
 exact ((((v1.toRight L1).toRight v2).toRight L2).toLeft L0|>.confirms L R)
lemma iteration' (v1:Pearl l X A)(v2:Limited l Y B) : Tendsto (fun i=> (vertical T (r i) (s i)).sale y S (X i) (Y i) L R z) l (𝓝 ((Q).sale y S A B L R z)):= by
 let h:= duties T y z l U V a; let L0:= earns_per l S p.1.le h.1 (qn.mono (fun i v=>v.1.le)); let L1:= earns_per l S p.2.1.le h.2.1 (qn.mono (fun i v=>v.2.1.le)); let L2:= earns_per l S p.2.2.le h.2.2 (qn.mono (fun i v=>v.2.2.le)); cases y
 · exact (((v2.toRight L1).toRight v1).toRight L2|>.toLeft L0|>.confirms L R)
 exact (((v2.toLeft L1).toLeft v1).toLeft L0|>.toRight L2|>.confirms L R)
end one
-- keep braces real-life
namespace Umbrella
variable {a : Axis} {x:Meter} {b T d r e:ℝ}{K:Finset Axis}{P:Terrain a K}(C:Umbrella a x b T d r e P)(hx:x a=0)
local notation "𝔯"=> aim a x b
variable (S:OS.Semigroup H a) (L R:H)
def Station (s:ℝ) := if y then s∈ Ioo d (d+1) else -s∈Ioo d (d+1) -- set order note implicit d
local notation "qs" s:max=> LedgerRide a (aim a x b) (s:ℂ)
-- SOT or WOT(V with Therm). provide at THIS phase
variable {X Y:ℕ→ H.Op}{u v:ℕ→ℝ}
variable (X₀:Limited atTop X A)(h1:Tendsto u atTop (𝓝 0))(Y₀:Limited atTop Y B)(h2:Tendsto v atTop (𝓝 0))
variable (hr:0≤r)(p: ∀ n,u n ≤ r)(q : ∀ n,v n≤ r)
include C
lemma on_aside (s:ℝ) (lᵢ : Station (d:=d) y s) (u v:ℝ)(p:u≤r)(t:v≤r): (vertical T u v).permeates a y (qs s):= by
 let g:= C.horizon 0 (by simp [Pane]) (s:ℂ) u v p t; rw [C.atSpot] at g; cases y; · exact g.2 (Ioo_subset_Icc_self lᵢ) -- defeq even Fin.?
 exact g.1 (Ioo_subset_Icc_self lᵢ)
local notation "F*" i:max k:max y:max => (vertical T (u i) (v k)).sale y S (X i) (Y k) L R
variable (D:ℕ→ℕ→ℂ→ℂ)(M:ℝ)(vt:∀ n m,AnalyticOnNhd ℂ (D n m) (slit e) ∧ ∀ z∈ slit e,‖D n m z‖≤ M)
variable (w:∀ (y:Bool) (n m:ℕ),∀ z:ℝ,Station (d:=d) y z → D n m (z:ℂ) = (vertical T (u n) (v m)).sale y S (X n) (Y m) L R (LedgerRide a (aim a x b) (z:ℂ)))
include X₀ h1 p q hr vt w
local notation "q₁"=> ((Ultrafilter.of (atTop:Filter ℕ)):Filter ℕ)
include M
private lemma inherits (m:ℕ):∃ F:ℂ→ℂ, (AnalyticOnNhd ℂ F (slit e) ∧ ∀ z∈slit e, ‖F z‖≤ M) ∧ ∀ (y:Bool)(z:ℝ), Station (d:=d) y z → F (z:ℂ)= (vertical T 0 (v m)).sale y S A (Y m) L R (qs z):= by
 obtain ⟨f,h,u⟩:= limit_chance (fun i:ℕ=> D i m) (slit_open e) (fun i=>(vt i m).1.differentiableOn) (fun i=> (vt i m).2)
 refine ⟨f,⟨h,fun z v=> le_of_tendsto (u z v|>.norm) (Eventually.of_forall (fun i=> (vt i m).2 z v))⟩,?_⟩ -- orientations
 intro y z t; apply tendsto_nhds_unique (u _ (slit_ground e C.costly z)); have W:= iteration S T L R y (qs z) atTop (C.on_aside y z t 0 _ hr (q m)) (Eventually.of_forall (fun n=> C.on_aside y z t _ _ (p n) (q m))) h1 tendsto_const_nhds X₀ (Pearl.still _ (Y m));
 exact (W.mono_left (Ultrafilter.of_le atTop)).congr' (Eventually.of_forall fun i=> (w y i m z t).symm)
include h2 Y₀
lemma inherits' : ∃ F:ℂ→ℂ,(AnalyticOnNhd ℂ F (slit e) ∧ ∀ z∈slit e, ‖F z‖≤ M) ∧ ∀ (y:Bool)(z:ℝ), Station (d:=d) y z → F (z:ℂ)= (vertical T 0 0).sale y S A B L R (qs z):= by
 choose f h U using C.inherits S L R X₀ h1 hr p q D M vt w -- order args tune
 obtain ⟨f1,hf,V⟩:= limit_chance f (slit_open e) (fun i=>(h i).1.differentiableOn) (fun i=> (h i).2)
 refine ⟨f1,⟨hf,fun z v=> le_of_tendsto (V z v|>.norm) (Eventually.of_forall (fun i=>(h i).2 z v))⟩,?_⟩
 intro y z t; apply tendsto_nhds_unique (V _ (slit_ground e C.costly z)); have W:= iteration' S T L R y (qs z) atTop (C.on_aside y z t 0 0 hr hr) (Eventually.of_forall (fun n=> C.on_aside y z t 0 _ hr (q n))) tendsto_const_nhds h2 (Pearl.still _ A) Y₀
 exact (W.mono_left (Ultrafilter.of_le atTop)).congr' (Eventually.of_forall fun i=> (U i y z t).symm)
include hx
lemma pure_time (T₁:ConePrice.Forward S) :
    inner ℂ (S.E T.toNNReal L) (A (sunny S x b B (S.E T.toNNReal R))) = inner ℂ (S.E T.toNNReal L) (sunny S x b B (A (S.E T.toNNReal R))) := by
 obtain ⟨f0,⟨h_e,g'⟩,lease⟩:= C.inherits' S L R X₀ h1 Y₀ h2 hr p q D M vt w
 have hx' := C.enough; have hT:= C.pos; let k:= (vertical T 0 0); let h₀(y:Bool):= k.sale y S A B L R
 have h1 : EqOn f0 (fun z=>h₀ true (qs z)) (veil 0 T e):= by
    refine pioneer (w:=d+1/2) (veil_connected 0 T e) (veil_real C.costly _ (show d+1/2∈ Ioo 0 T from ⟨by linarith,by linarith⟩)) d (d+1) ⟨by linarith,by linarith⟩ (h_e.mono veil_slit) (honorable S T x b hx A B L R e).1 fun v q=> lease true v q -- pioneer open?
 have h2 : EqOn f0 (fun z=>h₀ false (qs z)) (veil (-T) 0 e):=by
    refine pioneer (w:= -d-1/2) (veil_connected (-T) 0 e) (veil_real C.costly _ (show -d-1/2∈ Ioo (-T) 0 from ⟨by linarith,by linarith⟩)) (-(d+1)) (-d) ⟨by linarith,by linarith⟩ (h_e.mono veil_slit) (honorable S T x b hx A B L R e).2 fun v q=> lease false v (show _∈ Ioo d (d+1) from ⟨by linarith [q.2],by linarith [q.1]⟩)
 have ht:0<T:=by linarith; -- goto
 have hg:Tendsto (fun t:ℝ=> f0 (t:ℂ)) (𝓝 0) (𝓝 (f0 0)):= by
   have h: (0:ℂ)∈slit e:= by simpa [slit] using C.costly
   refine ( (h_e 0 h).continuousAt.tendsto).comp (by simpa using Complex.continuous_ofReal.tendsto (0:ℝ))
 rw [← (finishes S T x b T₁ hx A B L R ht).1,←(finishes S T x b T₁ hx A B L R ht).2]
 trans f0 0
 · apply tendsto_nhds_unique (l:=𝓝[>] (0:ℝ)) (center_cont S T x b hx A B L R true ht); apply (hg.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0))).congr'; filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with t w l; exact h1 (veil_real C.costly t ⟨w,l⟩)
 symm; apply tendsto_nhds_unique (l:=𝓝[<] (0:ℝ)) (center_cont S T x b hx A B L R false ht); apply (hg.mono_left (nhdsWithin_le_nhds (s:=Set.Iio 0))).congr'; filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (neg_lt_zero.mpr ht))] with t w l; exact h2 (veil_real C.costly t ⟨l,w⟩)
end Umbrella
end YM.Anvil
