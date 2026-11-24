import YM.CF.BPress.Hazel.Years
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {B:BandWidth}
open RG Filter Pressure Weave Port Letters Letter Grid Wealth Locale Tunnel Bands Branch Clipγ Chrono Skye Meadow.Stamps
variable {T: BPress.Sheet.Atlas}{Lf C C' y:ℝ}{a:ℕ}{A L D κ ζ:ℝ}{W: Rental}{r' r:Side}{q q' δ e d:ℝ}
-- grammar price. .d binding can pay arbitrarily small; .r' small fixed derives from $Period_N$. .age budget.
structure Shields (T:BPress.Sheet.Atlas)(G: BandWidth)(P:Weave.Budget)(D κ ζ A Lf y C C':ℝ)(r r': Side)(q δ:ℝ)(W:Rental) :Prop where
 plenty : Plenty T P G D κ ζ A y
 weight : StageC r q δ W G (price_p A ζ y)
 summer : W.M ≤ Warm G
 lost(s: Side)(a:ℕ)(F:Net s T Lf y C C' a)(X:Bands s G)(K:X.Sky)(Z:X.Slates)(U:Micro s): Z∈X.permit T y (X.atmospheric K) → ToneNoise y U → Lost y X (F.roll X Z K U)
 ticket(s:Side)(m:Record r' s)(a:ℕ)(F:Net s T Lf y C C' a)(X:Bands s G)(i:X.Index)(U:Micro s)(p:Duo s): F.takeN X U i p ≠0 → (i ∉ X.dc→ p∈ T.pairs y ((X.mark i).reads U)) → Grains (X.band i) U (plant F U p m.key X i) (brush F U p m.key X i) (soil r) (η q)
variable {P:Weave.Budget}
lemma issuance (T:BPress.Sheet.Atlas)(P:Weave.Budget)(G:GapSize)(w: Poses r' (soil r) (η q))(a:Buoyant r q W)(p:lease r q (G.select 1).D)(v:∀ᶠ y in atTop, Plenty T P (G.select y) D κ ζ A y)(h:0<q)(c:0<C)(k:0<C')(t:0<δ) : ∀ᶠ L in atTop,∀ᶠ y:ℝ in atTop, Shields T (G.select y) P D κ ζ A L y C C' r r' q δ W:= by
 filter_upwards [Stamps.crit T G r' w C C' c k (by unfold soil; positivity) (by unfold η; positivity), list_flags G T C C' c k] with L p' h'; filter_upwards [p',h',v,stage_γ r G a A ζ δ p t, duskY G W] with y t k l u v; exact ⟨l,u,v,k,t⟩ -- syntax
variable {N:Side}{X:Bands (More N) B}{F:Net (More N) T Lf y C C' a}{R:Hangar (More N)}{K:Fare X}
variable {U:Micro (More N)}{S:Seal X.Hcols}{v:Quarters X}{w:X.Slates}
local notation "s₂"=> bawl X R y S (Prod.fst v)
structure Booked (d:ℝ) (k:ℕ) (W:Rental)(r:Side)(q q':ℝ):Prop where
 tone : Poses r q' (η q)
 credit : Buoyant r q W
 pays: d ≤ Chrono.earth r
 past: k+6 ≤ W.U
 good_q:0<q
variable {Y: Orbit N→Pane N}{k:ℕ} (p:Reserve X K S v w U y κ T)(v₀:Booked d k W r q q')(Z:Shields T B P D κ ζ A Lf y C C' r r' q δ W)
  (V:Roof N e d k Y) (t:Summer X K P.upper (P.low y) (P.reach y) (P.chunks y)) (Cstar:W.M≤ R.L.val)(rL: P.reach y≤ R.L.val)(u:temp y≤e)
include p v₀ Z V t Cstar rL u
structure Licence (A:Letter X)(m:Tiling (More N))(c:ℝ)(S:Seal (SiteX X R))(X₁:Micro (More N))(W:Rental)(q q' δ:ℝ) : Prop where
 grip: Grip X W R S A X₁ (soil m.b) (η q) c
 progress : Stopped A m grip q' q
 looks : let H:= Kactual W R S A m X₁; Looks X₁ (Picks X R S) H (primeC H) W.P Ringmark 3 q δ
lemma realized (f:Record r (More N))(g:Record r' (More N))(i:Ids N): let U':= field X F K S v w U; Licence (R:=R) (PortLetter X F K S v w U g.key) f.key (price_p A ζ y) s₂ (Y (U',i)) W q q' δ := by
 intro U'; let S':= bawl X R y S v.1; let H:=PortLetter X F K S v w U g.key; let T':=Y (U',i); have hp: Grip X W R S' H T' (soil r) (η q) (price_p A ζ y):= p.shelter Z.plenty t rL ⟨Z.summer,Cstar⟩ V u v₀.past (Z.lost _ _ F X _ w U p.gate p.u) g.key i (fun i=> Z.ticket _ g _ F X i _ _)
 let A:=f.key; have he:=legit Z.weight v₀.credit v₀.tone v₀.good_q.le hp f (fun i k=>(rings_cost d _ (V.paid (U',_)) i k).trans (pWeight _ v₀.pays)); exact ⟨hp,he,shake he Z.weight.wage Z.weight.bear Z.weight.radiusC le_rfl⟩ -- tune syntax p HP
end YM.CF.BPress.Hazel
#print axioms YM.CF.BPress.Hazel.realized
