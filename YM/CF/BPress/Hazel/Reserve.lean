import YM.CF.BPress.Hazel.Atrium
import YM.CF.BPress.Wealth.Signs
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}
open Grid Wealth Tunnel Locale Bands Branch Clipγ Letter Letters Meadow.Frame Meadow.Stamps Weave Port
open Pressure RG
variable {T: BPress.Sheet.Atlas}{Lf C C' y:ℝ}{a:ℕ}{A L D κ η:ℝ}(X:Bands s B)(F:Net s T Lf y C C' a)(R:Hangar s)(K:Fare X)
abbrev BadCols (X:Bands s B)(S:Seal X.Hcols)(v:Fills X)(y:ℝ):= univ.filter (rawBad X y S v)
def bawl (y:ℝ)(S:Seal X.Hcols)(v:Fills X):= (BadCols X S v y).image (own X R)
-- packaged comparison forecaster, bought pre data. 
structure Plenty (T:BPress.Sheet.Atlas) (P:Weave.Budget) (b:BandWidth) (D κ Q A y:ℝ):Prop where
 grant: Dividend D κ Q y
 desires : 0 ≤ A
 heals (s:Side)(U:Horiz s)(x:Tri s): BPress.Sheet.Atlas.Heals 1 y U x→ BPress.Sheet.Atlas.Healthy A y T U x
 bonds(s:Side)(U:Horiz s)(x:FlatLink s) : BPress.Sheet.Atlas.Heals 1 y U x.1 → BPress.Sheet.Atlas.Heals 1 y U (Grid.hop x.1 x.2 1) → ∀ i j, group.chord (T.give y U x.1 i * U x * (T.give y U (Grid.hop x.1 x.2 1) j)⁻¹)≤ sigmaN y ↔ i=j
 wind: ∃ k, CheckWind b.D P κ y k
 Xi : xi y ≤ 1
 coast:T.Coasts y -- for applying room from allowed? include

lemma plenty_cost (T:BPress.Sheet.Atlas)(P:Weave.Budget)(G:GapSize)(h:0<κ)(u:∀ᶠ y in atTop,Dividend D κ η y):∃ A,∀ᶠ y in atTop,Plenty T P (G.select y) D κ η A y:=by
 obtain ⟨a,p,H⟩:= T.heals_pass _ zero_le_one; obtain ⟨b,W⟩:= check_buy (D:=(G.select 0).D) P κ h -- tune syntax
 refine ⟨a,?_⟩; filter_upwards [u,H,T.heals_bond _ zero_le_one,W,T.coasts_y, npl_xi.drop.eventually (ge_mem_nhds zero_lt_one)] with y α h v q x ζ; exact ⟨α,p.le,h,v,⟨b,q⟩,ζ,x⟩

-- ensure eq since pick rewrites. acceptance components relevant also off no frames. `awarded` can work when all default using just individual conditions in Bcontour.
variable (S:Seal X.Hcols)(v:Quarters X) (w:X.Slates)(U:Micro s)
def centerSky (y:ℝ):= Aback X (bodyBase X y K S v)
def field := F.roll X w (centerSky X K S v y) U
abbrev PortLetter(k:Tiling s) := ballot X F k w (field X F K S v w U)
structure Reserve (y κ:ℝ)(T:BPress.Sheet.Atlas):Prop where
 eye : aware X κ y K S v
 bill : Barrel X y v.1
 gate : w∈ X.permit T y (X.atmospheric (centerSky X K S v y))
 u : ToneNoise y U
abbrev price_p (A ζ y:ℝ):= temp y+ζ*aA y+ A*(heigh y)⁻¹^2 -- matches $hFrame. NPL
lemma price_npl (A ζ:ℝ): NPL (price_p A ζ):= (npl_temp.add (npl_aA.const_mul ζ)).add ((npl_power heigh_npl 2 (by omega)).const_mul A) -- tune
variable {X F R K S v w U}
namespace Reserve
variable {P:Weave.Budget}(Z:Reserve X K S v w U y κ T) (t:Plenty T P B D κ η A y) (sK: Summer X K P.upper (P.low y) (P.reach y) (P.chunks y)) (u:P.reach y≤ R.L.val) -- u existing real includes? include dups
variable {i:X.Hcols}{q:X.Index}
lemma hurt_m (l: rawBad X y S v.1 i) :own X R i∈ bawl X R y S v.1:= mem_image_of_mem (own X R) (mem_filter.mpr ⟨mem_univ i,l⟩)
lemma cool (p:Good X R (bawl X R y S v.1) 0 i) : ¬rawBad X y S v.1 i:=fun l=> p (local_0 X R (bawl ..) _ (hurt_m l) 0)
include u t sK
lemma ready (p:Good X R (bawl X R y S v.1) 1 i): ∀ j,chord (bodyBase X y K S v i j) (bMag B.D y j) ≤ wc y:=by
 refine (t.wind.choose_spec.open_gate sK S v i ?_).2.1; intro j h; apply cool (X:=X) (R:=R); exact good_cc p (column_eq.mp h|>.1.symm) (((column_eq.mp h).2).trans u)
lemma skyline (x:X.Index)(l:FlatLink s) {t':X.Sky}{V:Micro s} (q: X.skyH V=t') : window X V x l=t' ((x,l.1),⟨B.D-1,Nat.sub_one_lt B.D_pos.ne'⟩,l.2):=by
 rw [←q]; let k:= B.D-1; unfold window horizontal skyH; simp only [skylink]; rw [Nat.sub_add_cancel B.D_pos] -- omit?
lemma healed (F:Net s T Lf y C C' a) (w:X.Slates) (U:Micro s) (p:Good X R (bawl X R y S v.1) 2 i) : BPress.Sheet.Atlas.Heals 1 y (window X (field X F K S v w U) i.1) i.2:= by
 intro j f; rw [one_mul]; have ht:= good_cc (r:=1) (y:=(i.1,j.1)) p rfl (show delta _ _≤ _ from (le_trans f R.L.property)); unfold Hazel.field; rw [skyline t sK u _ _ (F.roll_sky ..)]; exact ready t sK u ht _ -- tune
include Z
lemma park (W: Tiling s)(f:Good X R (bawl X R y S v.1) 2 i) : chord ((PortLetter X F K S v w U W).h i) (Mag.center (code X w i)) ≤ A*(heigh y)⁻¹^2 := (t.heals _ _ _ (healed t sK u F _ _ f)).near_center _ -- tune Z unused
omit t sK u in
lemma permitted (k:X.Index)(p:k∉X.dc): let T':=field X F K S v w U; knot (T:=T) (y:=y) X w T' k∈ T.pairs y ((X.mark k).reads T') := by intro Y; rw [← X.choices_B T y Y p]; exact mem_image_of_mem _ (roll_coast F w _ Z.gate k) -- tune
lemma frame_allowance (x:X.Index) : let Y:=field X F K S v w U; T.allowed y (window X Y x) (T.frame y (window X Y x) (orientation X w x)):=by
 intro Y; by_cases h:x∈X.dc
 · have ht:x+1∈X.nc:=by rw [ X.nc_index,X.prev_next]; change ¬¬X.Dmark x; push Not; simpa using h
                               -- indent fix
   have he:= (mem_sdiff.mp ht).2; let p:= (T.pairs_ok y (knot X w Y (x+1)) ((X.mark (x+1)).reads Y) t.coast |>.1 (permitted (F:=F) Z _ he)).1; rw [orientation, if_pos h]; unfold window; have hx:= left_shadow ht; rw [add_sub_cancel_right] at hx; rw [hx]; convert! p using 1; unfold Letters.knot putF; rw [if_neg he]; rfl -- tune
 let q:= (mem_sdiff.mpr ⟨mem_univ x,h⟩:x∈X.nc); let p:= (T.pairs_ok y _ _ t.coast|>.1 (permitted (F:=F) Z x h)).2; rw [orientation,if_neg h]; unfold window; rw [right_shadow q]; convert! p using 1; unfold Letters.knot putF; rw [if_neg h]; rfl

lemma steady (F:Net s T Lf y C C' a) : stable (code X w) R (bawl X R y S v.1) := by
 intro j x b p' q; rw [←hop_glide] at *; let H:= window X (field X F K S v w U) j; let i:=Grid.hop x b 1; change Good X R (bawl ..) 2 (j,i) at q; refine (t.bonds s H (x,b) (healed t sK u F _ _ p') (healed t sK u F _ _ q) _ _).mp ?_; exact (frame_allowance (F:=F) Z t sK u j).2 (x,b) -- tune arguments
lemma mission : Mission X y (centerSky X K S v y) U (field X F K S v w U):= marches X F w _ U
lemma gold {l:Link s}(p:l∈inside (halo (Wealth.cloak B) (X.gap q)))(h:Good X R (bawl X R y S v.1) 2 (panel X l.1)) : chord (field X F K S v w U l) 1 ≤ price_p A η y:=by
 have hx:= (zone_of_halo X q (Wealth.cloak B) l.1|>.1 ((inside_iff ..).mp p).1); have ht:panel X l.1=(q,Fin.tail l.1):=Prod.ext (collar_ride X hx le_rfl) rfl
 have he(e:X.Air)(f:edgeKey X l=some e): e.1 ∉ chosen X κ y (centerSky X K S v y):=by
    rw [key_housed X hx f, ← ht,show chosen X κ y (centerSky X K S v y)=S from Z.eye]; exact fun l'=> cool (good_m h (by norm_num)) (Or.inl l')
 apply (chord.triangle _ (background y l) 1).trans; rw [chord.one]; let d:= t.grant; have hl:= d.bgView l.2; apply (add_le_add ((near_back κ y d.branch (mission Z t sK u) Z.u l he p).trans d.olive) hl).trans; exact le_add_of_nonneg_right (mul_nonneg t.desires (sq_nonneg _))
end Reserve
end YM.CF.BPress.Hazel
