import YM.CF.Buffered.Spectrum
/-! Order of purchase of the rates of Bill-E, from the given admissible pivot and witnesses.

Provide also explicit order book theorem: the thresholds needed don't require already knowing horizon or x. In particular C₁ MUST be issued before mark R.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 23000
set_option maxHeartbeats 550000
noncomputable section
namespace YM.CF.Buffered.Concert.Lobby
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube Lat Tenant Tulip Pastry Scroll Spire Fock Vault Pail Stake Vale Vale.Grace Gauge Paige Brace Next.SectorChange Skye Cascade Analysis Pressure Py Haro Jet Vol Rel Graph Nova Alloy Mint Ballad Region Burn
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker ComplexOrder ENNReal NNReal
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
section choose
variable {B: Side}
-- first inputs independent of x
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {N':Side}{V:Grace K R L}
variable {d:ℝ}{U:Grasp V.U B d}{W:GivenX V U}
variable {KX b' vL c l b D E' C0 h1 r α t e:ℝ}{kT d':ℕ}
variable (P_ : Pic.Span W.pearl KX b' vL c l b kT)
-- no h, R₀ budget or x
abbrev C₁ (P_ : Pic.Span W.pearl KX b' vL c l b kT) (g:0<e) := (Ballad.floored P_ (e/16) (by positivity)).choose
variable (g:0<e)
local notation "s"=>C₁ P_ g
noncomputable def howR : ℕ := (Filter.eventually_atTop.mp (Melody.atVertex (B:=B) P_.p P_.rP (Ballad.floored P_ (e/16) (by positivity)).choose_spec.1 ((e/16)/8) (by positivity))).choose
structure Tab (v:ℕ) (D H t:ℝ)(w i:ℕ) where
 tower : Ballad.Tower P_ v D H s (e/16) t w i
structure Insure (v:ℕ) where
 D:ℝ
 H:ℝ
 t:ℝ
 w:ℕ
 i:ℕ
 tower : Ballad.Tower P_ v D H (C₁ P_ g) (e/16) t w i
 v':ℝ
 t':ℝ
 k:ℕ
 crop : Alloy.Crop K.j H v' t' k
include K g
lemma insurance (v:ℕ) : Nonempty (Insure P_ g v):=by
 obtain ⟨D,H,u,w,i,T⟩:=(Ballad.floored P_ (e/16) (by positivity)).choose_spec.2 v; obtain ⟨A,t,b,C⟩:= crop_f P_.p T.loom.le; exact ⟨⟨D,H,u,w,i,T,A,t,b,C⟩⟩
noncomputable def Purchase (r:ℕ) := (insurance P_ g r).some
-- check h1 used V separately
variable (J: Robes N' V W)(q:Chi)(r₀:ℕ)(a:ℝ)(p i N0:ℕ) (D':Side) (S:Insure P_ g r₀) (h:ℝ)(R0 δ:ℝ→ℝ) (E:ℝ)(d₀:ℕ)
-- delays for the estimates. depend on h, D', not q after
variable (Y:Roe.Port P_ D E' C0 h1 r d') (p':1≤h)(l':C0≤h) (f:S.v'≤h)
noncomputable def h_g : ℝ:= (Filter.eventually_atTop.mp (Edition.playback V a p i N0 J q h R0 δ P_ Y p' l' S.tower S.crop (by positivity:e/16>0) f E d₀)).choose
noncomputable def h_a : ℝ:= (Filter.eventually_atTop.mp (Edition.mounts V a p i N0 J q h R0 δ P_ p' E d₀ (priceθ_p B D'))).choose
-- these are rates of the two extra estimates, there are earlier x-based activation etc costs. Window.enrollment likewise x-independent.
noncomputable def h_e : ℝ:= (Filter.eventually_atTop.mp (Volume.Window V a p i N0 J q h R0 δ E d₀ p' P_ Y l')).choose
end choose
-- Translation threshold independent of other parameters after vertex bought. copy birth formula to expose type independence
section mark
open Bilinear Lifted
variable (B : Side)(R:ℕ)
def originL : Lead R:= ⟨creatorSite,creatorSite+R • step 3,0,false,List.replicate (2*R) (posDir 3), by simp [direction,Ballad.sail], by rw [Sods.swifts]; unfold nodeC; rw [smul_add,mul_smul (2:ℕ)]; abel,List.length_replicate ⟩
def origin (B:Side)(R:ℕ): Melody B R:= ⟨originL R, (originL R).mirror 3 (Heat.gaugeShift B (-((R/(2*B.val):ℕ):ℤ))),rfl,by simp [Lead.mirror,axis_val],true,by
 let x:= Heat.gaugeShift B (-((R/(2*B.val):ℕ):ℤ)); change (plane 3 x).flee (creatorSite+_) = _; funext i; by_cases h:i=3 <;> simp only [Ballad.sail,ite_true] <;> simp [originL,creatorSite,direction, Lifted.flee_pos,h, Ne.symm]; unfold Ballad.gap x Heat.gaugeShift; ring⟩
lemma identity (K:Calibration):origin K.B K.vertex =Original.primary K:=rfl
variable (m:ℕ)
lemma mover : ∃ z:ℤ,∃ N:Side,∀ i:Side,N≤ i→ Melody.Budget (Ballad.Venue.towards B (origin B R) z) (Domain i B) m 0:=by
 obtain ⟨i,h⟩:=(Ballad.Venue.stamp (origin B R) m).exists; exact ⟨i, (Filter.eventually_atTop.mp h)⟩
-- Want divisibility and opposite plane even at q even. after R choose z, sufficiently large tile; q chosen taking odd multiples. Supports qualify opposite for general via growing m; word bill requires room. Ensure exists R satisfying line and positive; no ambient constraints.
lemma dueR : ∀ᶠ v:ℕ in atTop, 2*m ≤ 4*B.val*(v/(2*B.val)):=by
 filter_upwards [eventually_ge_atTop (m*(2* B.val))] with v hv
 have hp:0<B.val:= B.property; have hx : m ≤ v/(2*B.val):=(Nat.le_div_iff_mul_le (by positivity)).2 hv; nlinarith
end mark
variable (Q:Calibration)(S:Burn.SpanCal Q){e:ℝ}(g:0<e)
variable (T:Insure S.spanX g Q.vertex)
-- canonical venue. expresses numerical tests only (no appearance of ν/story comparison)
variable (p:T.v'≤ Q.h) (J:Tiling Q)
def opens : Venue S e:= ⟨T.H,T.D,C₁ S.spanX g,T.t,priceθ Q.B J.d',T.w,T.i,T.v', T.t', T.k,g,priceθ_p .., T.tower,T.crop,p⟩
local notation "Xv"=> opens Q S g T p J
noncomputable def longitude (Lr: howR S.spanX g≤Q.vertex) := (Filter.eventually_atTop.mp ((Filter.eventually_atTop.mp (Melody.atVertex (B:=Q.B) S.spanX.p S.spanX.rP (Ballad.floored S.spanX (e/16) (by positivity)).choose_spec.1 ((e/16)/8) (by positivity))).choose_spec Q.vertex Lr)).choose
-- predecessor-specific heights
local notation "Hq" => h_g S.spanX g Q.J Q.η Q.vertex Q.a Q.p Q.i Q.N0 T Q.h Q.R0 Q.δ S.c S.k S.portX Q.positive_h S.enough_h p
local notation "HQ" => h_a S.spanX Q.J Q.η Q.a Q.p Q.i Q.N0 J.d' Q.h Q.R0 Q.δ S.c S.k Q.positive_h
local notation "He"=> h_e S.spanX Q.J Q.η Q.a Q.p Q.i Q.N0 Q.h Q.R0 Q.δ S.c S.k S.portX Q.positive_h S.enough_h
-- list gas. q count threshold pure too
noncomputable def onAge (A b:ℝ)(B D':Side) : Side:= (Filter.eventually_atTop.mp (authorize B D' A b)).choose
-- plusV: finite constants
lemma fields (Lr: howR S.spanX g ≤ Q.vertex) (Lq: longitude Q S g Lr ≤ Q.c Q.q) (x:Hq ≤ Q.x)(u:HQ ≤ Q.x)(h:(Real.log Q.x)^4 ≤ (Q.q.val:ℝ))(v:onAge (plusV Xv) (creditA Xv+1) Q.B J.d'≤ J.qcount Q.q): Rates (opens Q S g T p J) J:=
 ⟨x,u,((Filter.eventually_atTop.mp (Melody.atVertex (B:=Q.B) S.spanX.p S.spanX.rP (Ballad.floored S.spanX (e/16) (by positivity)).choose_spec.1 ((e/16)/8) (by positivity))).choose_spec Q.vertex Lr), Lq,h, (authorization Xv J rfl v).1,(authorization Xv J rfl v).2⟩
lemma lastTicks {C:Conveyor Q} (v:∀ᶠ n in atTop, Nonempty (Mail.Unison.Sponsor Q C J n))(Le:He ≤ Q.x)(t:under S Q.q)(j:under S (Q.q*3)): Backed Q C J S:=⟨v,Le,t,j⟩
include S g T J Q
#print axioms fields
lemma buy_here (z:ℤ)(p':Melody.Budget (Ballad.Venue.towards Q.B (origin Q.B Q.vertex) z) (Domain J.d' Q.B) (Q.ℓ+T.w+1) 0): Rented (opens Q S g T p J) J z:=by unfold Rented; rw [← identity Q]; change Melody.Budget _ (Domain (mesh J.d' Q.R.L 0) Q.B) (Q.ℓ+T.w+1) 0; rw [Vale.mesh,pow_zero,mul_one]; exact p'
-- support q before horizon for assembling. sufficient q prices above are just power log or fixed. Record possibility of still fitting progression; leave activation predicate to predecessor horizon data. This estimate accommodates EXTRA lower bounds polylog and constant factors for all that. Use m0 already eligible, D optional extra multiplier.
omit S g T J
variable (t:ℕ) (D N: Side)
lemma crestq : ∀ᶠ x:ℝ in atTop,
   ∃ m:Side, oddMultiple m (D*N) ∧
   grainZ Q.V Q.W Q.N0 x ≤ m.val ∧
   (Real.log x)^4 ≤ (m.val:ℝ) ∧ t ≤ m.val ∧
   ((radiusB x)^t:ℕ) ≤ m.val ∧
   (m* (3:Side)).val ≤ ((oYY Q.V Q.N0 Q.J x).val)^(3+t):=by
 let v:= D*N; let f(x:ℝ):=((oYY Q.V Q.N0 Q.J x).val)
 have hp(x:ℝ):f x>grainZ Q.V Q.W Q.N0 x:=by unfold f oYY; refine lt_of_lt_of_le ?_ (Nat.le_mul_of_pos_right _ Q.M'.property); change _< Q.J.h + _+_; omega
 have ht(x:ℝ): radiusB x +1 ≤ f x:= by apply le_trans _ (hp x).le; unfold grainZ; nlinarith
 filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (max t (9*v.val))] with x e; replace e:= max_le_iff.mp e
 let z:= f x; let k:= z^(2+t); let s':Side:= ⟨k+k+1,by omega⟩; let m:=v*(s':Side)
 have hu:z≥1:=by have hv:=hp x; unfold z; omega
 have hb:z^2 ≤ k := pow_le_pow_right₀ hu (show 2 ≤ 2+t by omega)
 have ha:z≤k:=hb.trans' (by nlinarith)
 have he: m.val=v.val*(k+k+1):=rfl; have hv:k ≤ m.val:=by apply le_trans _ (show k+k+1 ≤ m.val from Nat.le_mul_of_pos_left _ v.property); omega
 refine ⟨m,⟨s',?_,rfl⟩,(hp _).le.trans (ha.trans hv), ?_,(e.1.trans (le_trans (by omega:radiusB x≤radiusB x+1) (ht x))).trans (ha.trans hv),?_,?_⟩
 · exact ⟨k,(by change k+k+1=2*k+1; omega)⟩
 · have hz:(Real.log x)^2 ≤ (z:ℝ):= (Nat.le_ceil ((Real.log x)^2)).trans (by exact_mod_cast (Nat.le_trans (by omega : radiusB x ≤ radiusB x+1) (ht x) : radiusB x≤ z)); have hx: ((z:ℝ)^2) ≤ (m.val:ℝ):=by exact_mod_cast (hb.trans hv)
   nlinarith only [hz,hx,sq_nonneg (Real.log x)]
 · exact (Nat.pow_le_pow_left (show radiusB x ≤ z from le_trans (by omega : radiusB x≤ radiusB x+1) (ht x)) t).trans ((pow_le_pow_right₀ hu (by omega:t≤2+t)).trans hv)
 change m.val*3 ≤ z^(3+t); rw [he,show 3+t=2+t+1 by omega,pow_succ]; have hl:9*v.val≤z:=e.2.trans ((Nat.le_succ _).trans (ht x)); change _≤k*z; nlinarith
end YM.CF.Buffered.Concert.Lobby
