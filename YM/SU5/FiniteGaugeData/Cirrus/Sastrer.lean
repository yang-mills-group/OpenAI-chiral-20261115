import YM.SU5.FiniteGaugeData.Cirrus.Couture
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute Mink Mink.General Vp.Folio Celeritas Land
open scoped Topology NNReal InnerProductSpace Classical
local notation "a"=>timeAxis
variable {H:Axis→Hilbert}(S:∀ i:Axis, OS.Semigroup (H i) i)
variable (Ω:(i:Axis)→(H i).space)(Ω':Bench (S a))(ht:Ω'.val=Ω a) (hΩ:∀ p:E4,M (S a) p Ω'.val=Ω'.val)(o:‖Ω'.val‖=1)
variable {ι:Type}(G:Canopy (H a) ι)(J K:Set ι)
open Gem
variable (V:Gem.Tribe G){r:Axis→ℝ≥0}
variable (L U: Bag G r)
-- common sequence sizes not just an existential eval equality.
abbrev TokenF := ℂ × Cartouche G r
private def foldB(X Y:TokenF G (r:=r)):Bag G r:= if d:Sewable G X.2 Y.2 then [(X.1 * Y.1, stitch G X.2 Y.2 d)] else []
-- public.Eval label
abbrev leeway(L U:Bag G r):Prop:= ∀ i∈L,∀ j∈U,Sewable G i.2 j.2
def pairBag(L U: Bag G r)(p:leeway G L U): Bag G r:= L.flatMap fun i=> U.flatMap fun j=> foldB G i j
lemma bias(T Y: TokenF (r:=r) G)(p:leeway G [T] [Y]): pairBag G [T] [Y] p= [(T.1*Y.1, stitch G T.2 Y.2 (p T List.mem_cons_self Y List.mem_cons_self) )]:=by
 simp [pairBag, foldB, p T List.mem_cons_self Y List.mem_cons_self]
abbrev Painted (J:Set ι)(L:Bag G r) := ∀ i∈L,Stripe G J i.2
abbrev hue(B:Bag G r):= oars S G V r a B
local notation "µ"=> traceB S G V r a
local notation "Q"=>value_κ S Ω'
-- lemma Konto_eval additive
lemma two_k (X Y:(H a).Op): value_κ S Ω' (X+Y)=value_κ S Ω' X+ value_κ S Ω' Y:= inner_add_right ..
lemma scale_k (X:(H a).Op)(c:ℂ): value_κ S Ω' (c • X)= c*value_κ S Ω' X:= inner_smul_right (𝕜:=ℂ) ..
lemma zero_k: value_κ S Ω' (0:(H a).Op)=0:= inner_zero_right ..
lemma more_k(U V':Bag G r): Q (hue S G V (U++V'))=Q (hue S G V U)+Q (hue S G V V'):=by rw [show hue S G V _= _ from (by simp [hue,oars] : hue S G V (U++V')=hue S G V U+hue S G V V'),two_k]
variable (z:leeway G L U)
variable (E:G.Earned (S a) Ω')(P:Pale (S a) Ω' G J K) (e:Ray)(W:Shelf (S a) (magnet e))
include Ω ht hΩ E P W o
lemma saw(p:Painted G J L)(q:Painted G K U)(z:leeway G L U): Q (hue S G V (pairBag G L U z))= Q (hue S G V L)*Q (hue S G V U):=by
 unfold pairBag
 let v(A:TokenF (r:=r) G):= A.1 • (µ A.2); have he(B:TokenF (r:=r) G)(U:Bag G r)(b:Stripe G J B.2)(q:Painted G K U)(p:∀ z∈U,Sewable G B.2 z.2): Q (hue S G V (U.flatMap (foldB G B)))= Q (v B)* Q (hue S G V U):=by
    induction U with
    | nil=> change Q 0= Q _*Q 0; rw [zero_k,mul_zero]
    | cons i U ih=>
       let u:= p i List.mem_cons_self; rw [List.flatMap_cons,more_k, ih (fun i v=>q i (List.mem_cons_of_mem _ v)) (fun i h=>p i (List.mem_cons_of_mem _ h)),foldB,dif_pos u]; let Z:=stitch G B.2 i.2 u
       change Q ((B.1*i.1) • (µ Z)+0) + _ = _*Q (v i + hue S G V U); rw [add_zero,two_k, mul_add]; let A:= (q i List.mem_cons_self)
       unfold v; simp_rw [scale_k]; rw [ show Q (µ Z)= _ from contour S Ω Ω' ht hΩ o G J K V B.2 i.2 u E P e W b A]; ring
 induction L with
 | nil=> change Q 0=Q 0* _; rw [zero_k,zero_mul]
 | cons i L ih=>
    rw [List.flatMap_cons, more_k, he i U (p _ List.mem_cons_self) q (z i List.mem_cons_self), ih (fun i d=> p i (List.mem_cons_of_mem _ d)) (fun i d=> z i (List.mem_cons_of_mem _ d))]; change _=Q (v i + hue S G V L)*_; rw [two_k,add_mul]
omit Ω ht hΩ E P W o
structure Weft (t : Axis→ℝ≥0) (A B C: (i:Axis)→ (H i).Op) :Prop where
 pays : ∃ (u v:ℕ→Bag G t), (∀ i,Painted G J (u i))∧(∀ i,Painted G K (v i))∧∃ p:∀ i,leeway G (u i) (v i),∀ w:Axis,
       Wot (fun i=>oars S G V t w (u i)) (A w)∧ Wot (fun i=> oars S G V t w (v i)) (B w)∧ Wot (fun i=> oars S G V t w (pairBag G (u i) (v i) (p i))) (C w)
include E P W o Ω hΩ ht
lemma woof (A B C: (i:Axis)→ (H i).Op)(X:Weft S G J K V r A B C): Q (C a)= Q (A a)* Q (B a):=by
 obtain ⟨f,g,z,k,p,T⟩:= X.pays; apply tendsto_nhds_unique_of_eventuallyEq ((T a).2.2.funds Ω'.val Ω'.val) (((T a).1.funds Ω'.val Ω'.val).mul ((T a).2.1.funds Ω'.val Ω'.val)); exact Eventually.of_forall fun i=> saw S Ω Ω' ht hΩ o G J K V (f i) (g i) E P e W (z i) (k i) (p i)
#print axioms woof
#print axioms bias
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
