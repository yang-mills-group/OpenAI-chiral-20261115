import YM.SU5.FiniteGaugeData.Chrono.Awning
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Chrono
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Py (Vestal Cape)
open Reed (Fine think)
open Advance Heat
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ}
variable (P : Grasp Y B e) (X : Vestal m B L) (R : Cape m B L) (q : Chi) (d : ℝ)
variable (n : ℕ) (Q : ℕ → Haro.SpaceM)
variable (A : Steps m B L) {D J w U : ℕ} (v : Stencil.LaurentRadius j L D) (L' : 3 ≤ L.val) (T : Granted P X R q d n Q A J)
variable (t : ∀ k<n,LoomLaw (R k) w) (p : Margin L D w J U)
local notation "Ω" i:max=> cell m B L i
local notation "ρ" i=> denZ (X i) P (R i)
local notation :max "out_" i:max=>nextMark (ho:=ho) (j:=j) X R q d Q A i
-- actual partner moved without buffer clipping.
include P T v t
variable (Z:Buffered.Donor P X R n)
include Z
lemma lago (a:Axis)(i:ℕ)(h:i≤n)(z:ℤ)(f:Mark (Ω i))(u:AtSupport false univ f) : markedRead (reflMark a (gaugeShift B z) (reflMark a 0 f)) (R i) (ρ i) = markedRead f (R i) (ρ i):=by
  let E(i:ℕ):= ∀ z:ℤ,∀ f:Mark (Ω i), AtSupport false univ f→ markedRead (reflMark a (gaugeShift B z) (reflMark a 0 f)) (R i) (ρ i)=markedRead f (R i) (ρ i)
  have rwarm (n: Side)(i:ℤ){f:Mark n}(g:AtSupport false univ f): AtSupport false univ (reflMark a i f):=(g.refl a i).mono (subset_univ _)
  have he:E n:=by
    intro z f u; obtain ⟨X',Y,w,h,V⟩:= Z.grants; obtain ⟨x,y,t,s',A_⟩:=Z.roof
    let p:=rwarm _ (gaugeShift B z) (rwarm _ 0 u)
    rw [summit_num P (X n) (R n) Z.pin Z.scroll _ _ Z.top h V s' A_ (T.noTies n le_rfl) p.env,summit_num P (X n) (R n) Z.pin Z.scroll _ _ Z.top h V s' A_ (T.noTies n le_rfl) u.env]
    have ht: 0-gaugeShift B z=pitchT B (-(2*z)):=by unfold gaugeShift pitchT; ring
    exact (oven_move a 0 (gaugeShift B z) ht (both f) (fun x=> (u.allV (x,x)).sector)).symm
  have ht(i:ℕ)(h:i<n)(e:E (i+1)):E i:=by
    intro z f u; obtain ⟨g⟩:= T.grant i h; obtain ⟨V,b,c,Y',l⟩:= g.cap
    let K:= apt m B L i; have we:= T.branch i h; let M:=(out_ i) f
    have vt:AtSupport false univ M:= (surround K (A i) j (Q i).val (X (i+1)).J.M ho q d (X (i+1)).beta (R i) (g.power.symm ▸ v) Y'.bill we g.legal.1 g.legal.2 _ u (t _ h) (T.aligned i h)).mono (subset_univ _)
    have hp (z:ℤ)(F:Mark (Ω i))(w:AtSupport false univ F): (out_ i) (reflMark a z F)= reflMark a (L.val*z) ((out_ i) F):=rising K (A i) j (Q i).val (X (i+1)).J.M ho q d (X (i+1)).beta (R i) a z (T.aligned i h) w we Y' (g.power.symm ▸ v) g.legal.1 g.legal.2
    rw [single_num P X R q d n Q A v T (rwarm _ (gaugeShift B z) (rwarm _ 0 u)) h, single_num P X R q d n Q A v T u h,hp _ _ (rwarm _ 0 u),hp _ _ u, mul_zero, show (L.val:ℤ)*gaugeShift B z=gaugeShift B (L.val*z:ℤ) from by unfold gaugeShift; ring]; exact e _ _ vt
  have H(k:ℕ)(h:k≤n):E (n-k):=by induction k with | zero=>simpa using he | succ k ih=> exact ht (n-(k+1)) (by omega) ((show n-k=n-(k+1)+1 by omega) ▸ ih (by omega))
  exact (show E i from (show n-(n-i)=i by omega) ▸ H (n-i) (Nat.sub_le ..)) z f u
omit P Z T v t
end YM.CF.Buffered.Afterglow.Hierarchy.Chrono
set_option autoImplicit false
set_option synthInstance.maxSize 24000
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Heat Charm
namespace Chrono
variable (a:Axis)(z:ℤ)
lemma solder_tick (p:Ferry Y s i k) (f:Mark (side Y i s))(u:AtSupport false univ f) :
    Journey.solder Y i k p.depth s (reflMark a (gaugeShift Λ.block z) (reflMark a 0 f)) = Journey.solder Y i k p.depth s f:= by
  let W:= fullness Y i k p.depth; unfold Journey.solder; apply congrArg (fun z:ℂ=> z/_) (lago _ _ _ _ _ _ _ _ (legal Λ) W.warm_grant (fun k _=> tissue Y i k) W.heat.choose a s p.enters z f u)
lemma collector_tick (p:Ferry Y s i k) (f:W Kₜ) : collector Y h i k p.depth s ((clockW Kₜ a z f).val (momentm Y i s))=collector Y h i k p.depth s (f.val (momentm Y i s)):=by
 change Journey.solder Y i k p.depth s _= Journey.solder Y i k p.depth s _; have hf(y:Family Kₜ): send Y h i s (y (momentm Y i s))=sold Y h s i y:= (sold_v Y h s i y).symm
 rw [hf,hf,clockW,ice_print,ice_print,sold_reflect,sold_reflect]; exact solder_tick Y s i k a z p _ ((sold_affair Y h _ s i (well_for Kₜ f).1.paid.choose_spec).mono (subset_univ _)) -- check send/sold args

variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E)
include K
lemma metro_glide (x:W Kₜ) : I s (clockW Kₜ a z x).val i= I s x.val i:=by
 rw [← internal_eq Y h s i K _ (well_for Kₜ _).1, ← internal_eq Y h s i K _ (well_for Kₜ _).1]; apply tendsto_nhds_unique_of_eventuallyEq ((K.pick.booked Y h s (well_for Kₜ _).1).1.inner i) ((K.pick.booked Y h s (well_for Kₜ _).1).1.inner i)
 filter_upwards [K.pick.pass Y h s i] with n p; unfold hot; rw [dif_pos p.depth,dif_pos p.depth]; exact collector_tick Y h s _ _ a z p x
lemma invariantW (x:W Kₜ) : E s (clockW Kₜ a z x).val= E s x.val:= by
 rw [← mood_eq Y h s K _ (well_for Kₜ _).1, ← mood_eq Y h s K _ (well_for Kₜ _).1]; apply tendsto_nhds_unique_of_eventuallyEq (K.pick.booked Y h s (well_for Kₜ _).1).1.periods (K.pick.booked Y h s (well_for Kₜ _).1).1.periods; exact Eventually.of_forall fun i=> ((internal_eq Y h s _ K _ (well_for Kₜ _).1).trans (metro_glide Y h s _ a z K x)).trans (internal_eq Y h s _ K _ (well_for Kₜ _).1).symm
#print axioms invariantW
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
