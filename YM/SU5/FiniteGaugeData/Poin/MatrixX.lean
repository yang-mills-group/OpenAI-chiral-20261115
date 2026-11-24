import YM.SU5.FiniteGaugeData.Poin.Seal
import YM.SU5.FiniteGaugeData.Poin.Sonic
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
local notation "ℰ"=> W timeAxis
-- optional constructive words `restore P` contract.Prop`
structure Rider:Prop where
 geometry : Authority W ω U
 fare : Stamp W G A U
 owes : Restaure W G A U
 stipend : RotReal W G ω A
variable (p: Rider W G ω A U)(ww: ‖ω timeAxis‖=1)(e:ω timeAxis=W₀.val)
structure Life (X:Action (K timeAxis)):Prop where
 learns : G.Arrival ℰ W₀ X
 growth : G.Earned ℰ W₀
 -- precise tying all views.price. realM
 votes (n:ℕ)(x:Points n)(L:List (Fin n))(f:Fin n→ G.Chip)(b:Axis) (q:L.Perm (Each n))(z:ProofOrder x b L): Canopy.ornate G (W timeAxis) W₀ x f= Gem.evaluate x W G ω A f L b
include p ww e
lemma important : ∃ X:Action (K timeAxis), Life W G ω W₀ A X:=by
 have eb:(0:Axis)≠timeAxis:=by decide
 let P:= p.geometry.pace (0:Axis) eb; let T:=W timeAxis; let V':= tileR W G ω W₀ A e p.stipend; have hΩ(x:E4): M T x W₀.val=W₀.val:= by rw [← e]; exact P.Ωa x
 let a':= Lobby T P.coneP; obtain ⟨X,h⟩:=Canopy.arrivals G T W₀ hΩ a' V' (fullPay W G ω W₀ A U p.geometry e p.owes) (by rwa [← e]) (show T.ℚmeasure.region Mink.coneᶜ=0 from timeCone ▸ P.coneP) (pane W G ω W₀ A U p.geometry p.fare)
 refine ⟨X,h, G.eldership T W₀ hΩ a' V',?_⟩; intro n x L f b q z; apply stirring x W G ω W₀ A U e f L b p.stipend p.fare _ q z; · by_cases d:b=timeAxis; exact Or.inl d; exact Or.inr (p.geometry.κ n b d)
 intro i; by_cases h:i=timeAxis; · subst i; exact P.first.cover
 exact (p.geometry.pace i h).first.leave
#print axioms important
end Gem
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
