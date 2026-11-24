import YM.SU5.FiniteGaugeData.Poin.Gem
import YM.SU5.FiniteGaugeData.Seld.HonorC
/-! # MULTIVIEW tilt estimates to generate separated Eu readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set Mink Mink.General Mink.Lorentz Real Flute MeasureTheory OS OS.Semigroup
open scoped Topology BigOperators NNReal
local notation "a"=>timeAxis
variable {H:Hilbert}{n:ℕ}{ι:Type}(T:Canopy H ι)(S:OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ x:E4,M S x Ω.val=Ω.val)
variable (s:SO)(x:Points n)
namespace Gem
open scoped ENNReal InnerProductSpace ComplexOrder
variable {ι: Type}{K:Axis→Hilbert} (W:∀ a':Axis,OS.Semigroup (K a') a') (G:Canopy (K timeAxis) ι)
open Celeritas Land Leal Leal.Breve Mist
variable (ω: (i:Axis)→ (K i).space)(W₀:Bench (W timeAxis))(A:Tribe G)(U:Set (Shrine K))
variable (L L':Shrine K)(w:G.Chip) (e₀:(ω timeAxis)=W₀.val)
def imprint : Shrine K:= ⟨0,fun a'=> useB G A w a'⟩
structure Stamp:Prop where
 pay(t:G.Chip): imprint G A t ∈ Magic W U (G.grade t)
-- recovery estimate (geometrically, inside THAT very Eu housing, restore price of any finite Cask operation, all vectors simult finite bound)
structure Restaure :Prop where
 pays(L:Shrine K)(p:L∈U):∃ f:ℕ→Bag G L.t,∀ b:Axis,Wot (fun i=> oars W G A L.t b (f i)) (L.f b)
-- charge compatibility
variable (u: Fin n→ G.Chip)(M:List (Fin n))(b:Axis)
local notation "J"=> imprint G A ∘ u
local notation "Q"=> G.credit u
abbrev evaluate := chalk W ω b (Q) (J) x.ofLp M
lemma mapsIn : ProofOrder x b M ↔ M.Pairwise (Seers J x.ofLp b) := by rw [show Seers J x.ofLp b=(fun i j=>x i b<x j b) from funext fun i=>funext fun j=>propext (by simp [Seers,endX,startX,imprint])]; rfl
lemma comparator {X R:Type}[Monoid R] (f:X→R)(F:X→X→R)(Z:List X): Film f F Z=TapeT f F Z:= by
 cases Z with | nil=>rfl | cons i Z=> induction Z generalizing i with | nil => simp only [solitary]; rfl | cons j Z ih=> rw [Film_step,ih]; rfl
lemma utop : evaluate x W G ω A u M b= meanE (W b) (ω b) (fun i=>useB G A (u i) b) Q x M:=by
 let J':= J; let T:= Q; let Kt:=actO W J' x.ofLp b; let Bc:=coast W b T J' x.ofLp; let Qc:=rho (W b) T (clockV b x)
 have he(i j:Fin n): Bc i j= Qc i j:=by unfold Bc coast Hi Qc rho; simp [J',Function.comp_def, endX, startX,imprint,clockV, Par]
 have ht(i:Fin n): Kt i=coreSp (W b) (x i) (useB G A (u i) b):= barry W b (imprint G A (u i)) (x i)
 change inner ℂ _ (TapeT Kt Bc M (ω b))=_; rw [← comparator,show Kt=(fun i=>_) from funext ht, funext (show ∀ i,Bc i=Qc i from fun i=> funext (he i))]; rfl
structure RotReal :Prop where
 ink(n:ℕ)(x:Points n)(u:Fin n→G.Chip)(s:SO)(F F':List (Fin n)) (p:F.Perm (Each n))(t:F'.Perm (Each n))(h:ProofOrder x timeAxis F)(z:ProofOrder (turnO s.val x) timeAxis F')(ε:ℝ) (_:0<ε):
    dist (evaluate x W G ω A u F timeAxis) (evaluate (turnO s.val x) W G ω A (G.stampE s u) F' timeAxis) ≤ ε
include e₀
lemma advert: evaluate x W G ω A u M timeAxis= G.Sr (W timeAxis) W₀ x u M:=by
 rw [utop,e₀]; unfold Canopy.Sr; congr 2; funext i; exact usea G A (u i)
lemma tileR (V: RotReal W G ω A): Canopy.Tile G (W a) W₀:=by
 refine ⟨fun n b x y i j v u p q=> ?_⟩; -- dist
 rw [← advert ..,← advert ..,←dist_le_zero]; refine le_of_forall_pos_le_add ?_; intro e z; simpa using V.ink _ x y b i j v u p q _ z
 all_goals exact e₀
#print axioms tileR
variable (V:Restaure W G A U)
include V
lemma remunerate (p:Seance W ω U timeAxis false) : G.Pierces (W timeAxis) W₀:=by
 constructor; intro Qx hQ z v k t hc he; let v0:= ω a; rw [← e₀] at hc
 have hr(L:Shrine K)(e:L∈ U): Commute (L.f a) Qx:=by
    obtain ⟨f,h⟩:=V.pays L e; let B(i):= oars W G A L.t a (f i); let w':=L.f a; have hp:= (h a).body (tendsto_const_nhds (x:=Qx)); have hh(i:ℕ):=hook W G A L.t Qx v k t he (f i); let hz: Wot (fun i=>Qx*B i) (Qx*w'):= (h a).shrew tendsto_const_nhds
    ext1 x; apply ext_inner_left ℂ; intro y; apply tendsto_nhds_unique (hp.funds y x); simp_rw [(hh _).eq]; exact hz.funds y x
 have he(L:Shrine K)(h:L∈U)(y:E4): let A:=soup W ω a L false y; Qx A=A:= by
    let f:= leg (W a) y; let k:= orbit_on W a y L; have he:Commute k Qx:= ((t (SEP a y)).mul_left (hr L h)).mul_left (t (SEP a (-y))); exact (DFunLike.congr_fun he.symm.eq v0).trans (congrArg k hc)
 ext1 x; apply sub_eq_zero.mp; apply p; intro L h y; let z':= soup W ω a L false y; change inner ℂ (_-x) _=_; rw [inner_sub_left,←ContinuousLinearMap.adjoint_inner_right Qx, show Qx.adjoint=Qx from z, he L h y,sub_self]
omit V
#print axioms remunerate
variable (β: RotReal W G ω A)(X' : Stamp W G A U)
structure Prism (n:ℕ) : Prop where
 sail : Philos (σ:= Fin n) W ω timeAxis b U
variable (ph: ∀ i,saucer (W i) (ω i)=ω i)
include β X' ph
-- fit with ANY active Pc.
lemma stirring (hM:M.Perm (Each n))(v:ProofOrder x b M)(p:b=a ∨ Prism (n:=n) W ω U b) : Canopy.ornate G (W a) W₀ x u = evaluate x W G ω A u M b:=by
 rcases p with p|p
 · subst b; rw [advert x W G ω W₀ A e₀, Canopy.sing G (W a) W₀ _ _ M (tileR W G ω W₀ A e₀ β) hM v]
 rw [utop]; apply Canopy.soliloque G (W a) W₀ x u M (tileR W G ω W₀ A e₀ β) b (W b) (ω b) (fun w=>useB G A w b) _ hM v; intro x L t g k; rw [←advert x W G ω W₀ A e₀]; let F:=evaluate x W G ω A u M b; exact (show evaluate x W G ω A u L a=F from Cords W ω a b L Q J x.ofLp U p.sail (ph a) (ph b) (fun i=> X'.pay (u i)) M (t.trans hM.symm) (t.nodup_iff.mpr (List.nodup_finRange _)) ((mapsIn x G A u L a).1 g) ((mapsIn x G A u M b).1 k)).trans (utop ..)
#print axioms stirring
end Gem
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
