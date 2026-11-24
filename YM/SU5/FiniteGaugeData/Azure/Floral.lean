import YM.SU5.FiniteGaugeData.Cirrus.PieceW
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute Mink Mink.General Vp.Folio Celeritas Land
open scoped Topology NNReal InnerProductSpace Classical
namespace AzureP
local notation "a"=>timeAxis
variable {H:Axis→Hilbert}(S:∀ i:Axis, OS.Semigroup (H i) i)(Ω:Bench (S timeAxis))(p:∀ x:E4,M (S timeAxis) x Ω.val=Ω.val)
variable {ι:Type} (G:Canopy (H timeAxis) ι)(J:Set ι)
local notation "Q"=> (H a)
local notation "K"=> tower G J
local notation "KP"=> Canopy.Hatch (K) (S a) Ω
local notation "S₁"=> S a
open Gem
variable (V:Tribe G){r:Axis→ℝ≥0}(C:Cartouche G r)
include p
lemma purePat (j: Fin C.count)(p':Stripe G J C): Commute (Gem.cam S G V a C.chips C.points (Sum.inr j)) KP:= by
 change Commute (coreSp S₁ _ (useB G V _ a)) _; rw [usea]; exact stainH S₁ Ω p G J _ _ (p' j)
lemma traceW (v:Stripe G J C):Commute (traceB S G V r a C) KP:=by
 let c:= Gem.spire r a C.points; let A:=Gem.cam S G V a C.chips C.points; let k:=GapK (S a) c (costR G C.chips); have he(i): Commute (A i) (KP):=by cases i with | inl u=> exact Commute.one_left _| inr y=> exact purePat S Ω p G J V C y v
 suffices h:∀ L,Sau c L→ Commute (Film A k L) KP from h _ (C.behind a)
 intro L; induction L with
 | nil=> exact fun _=> Commute.one_left _
 | cons i L ih=> intro r; rw [Film_step]; apply (he i).mul_left; refine Commute.mul_left ?_ (ih (List.pairwise_cons.mp r).2); cases L with| nil=>exact Commute.one_left _| cons j L=> exact gapH S₁ Ω p G J _ _ (sub_pos.mpr ((List.pairwise_cons.mp r).1 j List.mem_cons_self)) -- tune
lemma arraY(L:Bag G r)(h:Painted G J L): Commute (oars S G V r a L) KP:=by induction L with | nil=> exact Commute.zero_left _| cons i L ih=> exact ((traceW S Ω p G J V i.2 (h i List.mem_cons_self)).smul_left i.1).add_left (ih fun j q=> h j (List.mem_cons_of_mem _ q))
set_option maxHeartbeats 180000
-- WOT.E.Commutant.Include Ω_.Heavy.N.CQName
lemma candleW (T:(H a).Op)(F:ℕ→Bag G r)(v:Wot (fun i=>oars S G V r a (F i)) T)(p':∀ i,Painted G J (F i)): Commute T KP:= by
 let P:= KP; ext1 x; apply ext_inner_left ℂ; intro y; apply tendsto_nhds_unique_of_eventuallyEq (((v.body (g:=fun _=> P) (x:=T) tendsto_const_nhds)).funds y x) (((v.shrew (g:=fun _=>P) tendsto_const_nhds)).funds y x) (Eventually.of_forall fun i=> congrArg (fun f: (H a).Op=>inner ℂ y (f x)) (arraY S Ω p G J V (F i) (p' i)).eq) -- tune order.B.
#print axioms candleW
local notation "Ἤ"=> Height S₁ Ω G J
lemma comm_flow(x:E4): Commute (leg (S a) x) KP:=by rw [Leal.acts_leg]; exact Canopy.stock (tower G J) (S a) Ω p (SEP timeAxis x).val
lemma woven(x:E4)(Z:(H a).Op)(e:Commute Z KP): Commute (opt (S a) x Z) KP:= ((comm_flow S Ω p G J x).mul_left e).mul_left (comm_flow S Ω p G J _)
lemma marches(x:E4)(y:(H a).space): y∈ Height (S a) Ω G J ↔ leg (S a) x y∈ Height (S a) Ω G J:=by
 refine ⟨fun h=>stayH (S a) Ω G J _ (comm_flow S Ω p G J _) y h, fun h=>?_⟩; let z:= stayH (S a) Ω G J _ (comm_flow S Ω p G J (-x)) _ h; have he: leg (S a) (-x) (leg (S a) x y)= y :=DFunLike.congr_fun (leg_pair (S a) x) y; exact he ▸ z
lemma warmR(x:ℝ≥0)(y:(H a).space):y∈ Height (S a) Ω G J ↔ (S a).E x y∈ Height (S a) Ω G J:=by
 let W:=Canopy.heat_P (K) (S a) Ω p x; let P:=KP; constructor; · exact stayH S₁ Ω G J _ W _
 intro h; let X:=(S a).E x; have he:X (P y)=X y:= ( DFunLike.congr_fun W.eq y).trans (Submodule.starProjection_eq_self_iff.mpr h); apply Submodule.starProjection_eq_self_iff.mp; apply sub_eq_zero.mp; exact (S a).heat_faithful x (P y-y) (by rw [map_sub]; exact sub_eq_zero.mpr he) -- instance complete.P.
#print axioms warmR
end AzureP
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
