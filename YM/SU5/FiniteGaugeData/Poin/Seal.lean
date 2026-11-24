import YM.SU5.FiniteGaugeData.Poin.Rosette
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
open _root_.YM Boundary Probe
variable (b:Axis)(w:G.Chip)
local notation "V"=> imprint G A
local notation "Y₀"=>W timeAxis
structure Authority:Prop where
 pace (b:Axis) (_:b ≠ timeAxis) : Pace W ω timeAxis b U
 κ(n:ℕ)(b:Axis) (p:b ≠ timeAxis): Prism W ω U b n
noncomputable abbrev Lobby {H:Hilbert}(S:OS.Semigroup H timeAxis) (e:Cinema S)(b:Mink.Ray): Shelf S (magnet b) where
 cup s:= Celeritas.cup S s e (magnet b) (bearing b).le
 hol s _:= Celeritas.cup_A S (magnet b) s e (bearing b).le
 norm s z p:=Celeritas.cupH S (magnet b) s z e (bearing b).le p
 realC s p t:=Celeritas.credit_h S (magnet b) s t e (bearing b).le p
variable (h: Authority W ω U) (v: Stamp W G A U)
-- turn enough.V.C `∀$$ below`. collapse.Pin
include h v
lemma pane: G.Loom (W timeAxis) W₀:=by
 constructor; intro B L p q i r δ m e p0 k z; rcases Set.eq_empty_or_nonempty (tsupport p) with H|⟨x,hx⟩
 · have he:p=0:=by ext1 x; apply image_eq_zero_of_notMem_tsupport; rw [H]; apply notMem_empty
   rw [he]; change Commute (G.fieldMap (Y₀) W₀ _ 0) _; rw [map_zero]; exact Commute.zero_left _
 have ht: ∀ y∈tsupport q,y i ≤ m:= fun y p=>(z (Set.mk_mem_prod hx p)).2.2.1.le
 have hz: Shaving a i (V B) (V L) q p r δ:= by
    intro x p y q; have he:= z (Set.mk_mem_prod p q); have hs: |x timeAxis-y timeAxis|<(r:ℝ):= he.1; have hv: (r:ℝ)+(δ:ℝ)< y i-x i:= he.2.1; refine ⟨ ?_,?_⟩; · rwa [abs_sub_comm]
    unfold imprint; simpa only [Pi.zero_apply,NNReal.coe_zero,sub_zero,add_zero] using hv.le
 have hm:= esteem W ω a i (imprint G A B) (imprint G A L) (G.grade B) (G.grade L) U (h.pace i e) (show Stake W a (V B) (V L) (G.grade B) (G.grade L) U from ⟨v.pay B,v.pay L,rfl,rfl⟩) q p r δ p0 k m ht hz; change (ℑ (W a) (useB G A B a) p _).comp (ℑ (W a) (useB G A L a) q _)= _ at hm; simp only [imprint,usea] at hm; ext1 y; exact Subtype.ext (DFunLike.congr_fun hm y.val)
variable (s₀:saucer (W b) (ω b)=ω b)(E: ω timeAxis=W₀.val)
include E
omit v in
lemma fullPay (v:Restaure W G A U): G.Climb (W timeAxis) W₀=⊤:=by
 let b:Axis:=0; let p:=h.pace b (by decide); apply G.fullCanopy _ _ _ (remunerate W G ω W₀ A U E v (p.spanning false)); intro z; rw [← E]; exact p.Ωa z
-- defer endpoint to orientation.Main theorem
#print axioms pane
#print axioms fullPay
end Gem
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
