import YM.SU5.FiniteGaugeData.SalonG.Cyl
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
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
namespace SalonG
open Nacre Heat Charm Chrono Journey
variable {S T}{x y u f:W (tent Y h)} (a:Axis)
local notation "η"=> reserve Λ l
local notation "φ"=> Λ.R.L.val
local notation "ξ"=> GridStep Λ l
local notation "N"=> side Y i s
local notation "D"=> Locator Kₜ
abbrev Reprise : Prop:= ingress Y s i k (sold Y h s i x.val)=sold Y h (s+1) i u.val -- inferred {x u}; want binder
#check Reprise
abbrev joinV (x y:W (tent Y h)):= Reprise Y h s i k (x:=x) (u:=y)
-- connect Heat Sharp
variable (j:Offered Y S s i k)
include j
lemma Transit.oneP : joinV Y h s i k 1 1:=by
 have h1:=snag_unit Y h S s i k j; rw [snag_pay Y h S s i k j,transitionQ_apply] at h1
 have ht:=exchanged Y h S s j (unitQ Kₜ S); rw [h1,unitQ_id,unitQ_id] at ht; exact ht.symm
local notation "R"=> joinV Y h s i k
lemma Transit.reflectP (z:ℤ)(v:joinV Y h s i k x u): joinV Y h s i k (fire Kₜ a z x) (fire Kₜ a ((Λ.R.L.val:ℤ)*z) u):= by
 obtain ⟨S',e⟩:=testimony Kₜ x; unfold joinV Reprise; rw [ice_print,ice_print,sold_reflect,sold_reflect,ingress_turn Y s i k a z (sold_affair Y h S' s i e) j.calendar j.age,v]
lemma grow_cut (z:ℤ) : (Λ.R.L.val:ℤ)*gaugeShift (Kₜ).B z= gaugeShift (Kₜ).B ((Λ.R.L.val:ℤ)*z):=by unfold gaugeShift; ring -- omit
lemma Transit.tickP (z:ℤ)(v:R x u): joinV Y h s i k (clockW Kₜ a z x) (clockW Kₜ a ((Λ.R.L.val:ℤ)*z) u):=by
 have h':=Transit.reflectP Y h s i k a j (gaugeShift (Kₜ).B z) (Transit.reflectP Y h s i k a j 0 v); rw [mul_zero,grow_cut Y h s i k j] at h'; exact h'
lemma Transit.mateP (d:ℕ)(v:R x y): joinV Y h s i k (mateW Kₜ a d x) (mateW Kₜ a (Λ.R.L.val*d) y):=by unfold mateW; rw [Nat.cast_mul,← grow_cut Y h s i k j]; exact Transit.reflectP Y h s i k a j _ v
lemma Transit.reamP (d n:ℕ)(v:R x y): joinV Y h s i k (reamW Kₜ a d x n) (reamW Kₜ a (Λ.R.L.val*d) y n):=by unfold reamW; split; exact v; exact Transit.mateP Y h s i k a j d v
lemma Transit.stepF : ∀ {S' T':Finset Cover} {f g t y:W Kₜ},R f g→R t y→Locator Kₜ f S'→Locator Kₜ t T'→SeatRange (spaceBill Λ l) (side Y i s) S' T'→joinV Y h s i k (f*t) (g*y):=by
 intro S' T' f g x y r t hx hv z
 let a':= j.calendar; let u:= j.age; let v:= crease Y s i k a' u
 unfold joinV Reprise; rw [joinW,joinW,sold_mult,sold_mult,← r,← t]; exact separated_mult (apt (Y.ir i) Λ.block L₁ s) _ _ _ _ Λ.R.odd_side Chi.canonical _ _ _ (show LaurentRadius _ _ _ from Journey.legal Λ) ((Y.voyage i).ownership s).paid.bill ((fullness Y i k a').cap_grant.branch s u) v.1 v.2 _ _ (sold_affair Y h S' s i hx) (sold_affair Y h T' s i hv) (Journey.tissue ..) z
variable {d n:ℕ}(p: Locator (tent Y h) f S)(t:Studio a 0 (yard (tent Y h) d) (reserve Λ l) S)
include p t
local notation "y'"=> (yard Kₜ d)
local notation "w"=> Λ.R.L.val*d
lemma Transit.trainF (q:joinV Y h s i k f x)(g:proceed Kₜ n d ≤ (N).val) : joinV Y h s i k (Train Kₜ a d f n) (Train Kₜ a (Λ.R.L.val*d) x n):= by
 induction n with
 | zero=> exact Transit.oneP Y h s i k j
 | succ n ih=>
   rw [proceed_succ] at g
   have hp := Transit.tickP Y h s i k a j d (ih (by omega)); have ht:= shift_port Kₜ a (n:=n) t; let z:ℤ:= ↑y'
   refine Transit.stepF Y h s i k j (Transit.reamP Y h s i k a j d n q) ?_ (ream_loc Kₜ a d n f p) (loc_tic Kₜ _ a _ (train_loc Kₜ a d n f p)) (seat_separate a (y:= (y':ℤ)) (N) ((t.union (arbour t)).earlier (by omega)) (ht.later (by rw [proceed_succ]; omega))) -- ? factors orientation
   rw [Nat.cast_mul (φ) d]; exact hp
lemma Transit.jacketF (q:joinV Y h s i k f x)(g:proceed Kₜ n d ≤ (N).val) : joinV Y h s i k (Jacket a d n f) (Jacket a (Λ.R.L.val*d) n x):=by
 have ht:= Transit.trainF Y h s i k a j p t q g -- 
 let S':= proceed_set Kₜ a d S n
 have he:= proceed_geo Kₜ a d n t
 have h':later 0 (N) S' a η:= he.later (by omega)
 have hz:= Transit.reflectP Y h s i k a j 0 ht; rw [mul_zero] at hz; exact Transit.stepF Y h s i k j hz ht (locate_cold Kₜ S' a 0 (train_loc Kₜ a d n f p)) (train_loc Kₜ a d n f p) (seat_separate a (N) (y:=0) (S:=refract a 0 S') (by rw [cold_twice]; exact h') h')
omit j p t in
lemma proceed_step (K: Calibration)(h d n:ℕ): proceed K n (h*d)= h*proceed K n d:= by unfold proceed; rw [yard_mul,mul_assoc]
lemma Transit.carrierF (q:joinV Y h s i k f x)(g:2*proceed Kₜ n d ≤ (N).val) : joinV Y h s i k (CarrierF a d n f) (CarrierF a (Λ.R.L.val*d) n x):=by
 have ht := Transit.jacketF Y h s i k a j p t q (by omega:(proceed Kₜ n d) ≤ (N).val); let z:= (proceed Kₜ n d:ℤ); let T:= blanket a d n (K:=Kₜ) S; have hp:Locator Kₜ (Jacket a d n f) T:= blanket_flight a d n S f p; have he: later z (N) (refract a z T) a η:= blanket_on a d n S t g; let A:= Transit.reflectP Y h s i k a j z ht; unfold CarrierF; rw [proceed_step, Nat.cast_mul]; exact Transit.stepF Y h s i k j ht A hp (locate_cold Kₜ T a z hp) (seat_separate a (N) he he)
-- exact boost radius through Blocks
omit p t
lemma Transit.gateLet (q:joinV Y h s i k x f): sharp Y h s i k x.val=sharp Y h (s+1) i k f.val:= by
 obtain ⟨Z,e⟩:= testimony Kₜ x; rw [refresh Y h Z s i k j.calendar j.age x.val e,sold_sharp Y h (s+1),q]
include p t in
lemma Transit.let_carrier (q:joinV Y h s i k f x)(g:2*proceed Kₜ n d ≤ (N).val):sharp Y h s i k (CarrierF a d n f).val= sharp Y h (s+1) i k (CarrierF a (Λ.R.L.val*d) n x).val:= Transit.gateLet Y h s i k j (Transit.carrierF Y h s i k a j p t q g)
#print axioms Transit.let_carrier
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
