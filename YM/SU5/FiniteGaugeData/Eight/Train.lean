import YM.SU5.FiniteGaugeData.Eight.Hull
import YM.SU5.FiniteGaugeData.SalonG.JourneyL
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Eight
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
-- using Harvest assembly at finite heat ONLY for transfer & geometry. preserve licences.
variable (a i:Axis)
variable {Ck Z:Side} {K:Calibration} {S T:Finset Cover} {j k M d r n:ℕ}
lemma shiftHour (x:ℤ) : hour K S a x= refract a (gaugeShift K.B x) (refract a 0 S):=by
 symm
 rw [refract,refract,image_image]; apply congrArg (fun f:Cover → Cover=> S.image f); funext t r; change _= beat K a x t r; simp_rw [Function.comp_apply,fling_move]; split_ifs with h
 · rw [←h,beat_same]; rw [← tick_tock]; simp
 rw [beat_slant K r a x t h]
variable (s i0:ℕ)
local notation "N"=> side Y i0 s
local notation "Kₜ"=> tent Y h
local notation "B"=> (tent Y h).B
local notation "L"=> (Y.voyage i0).CapeT s
local notation "C"=> proceed (tent Y h)
variable {f g: W (tent Y h)} {V:Literature (side Y i0 s)}{c v:ℝ}
local notation "σ₀"=> sold Y h s i0
abbrev Tax (n m:ℕ)(c:ℝ) (S:Finset Cover)(x: W (tent Y h)) := Hull ((Y.voyage i0).CapeT s) V n m c (region S (side Y i0 s)) (sold Y h s i0 x.val) -- include V? auto
local notation "Π'"=> Tax Y h s i0 (V:=V)
lemma Tax.fireW (z:ℤ)(p:Tax Y h s i0 (V:=V) j k c S f): Tax Y h s i0 (V:=V) k j c (refract a z S) (fire Kₜ a z f):=by
 unfold Tax; rw [ice_print,sold_reflect,refl_region]; exact Hull.turn (posters_p ..) _ _ p
lemma Tax.tickW (z:ℤ)(p:Tax Y h s i0 (V:=V) j k c S f): Tax Y h s i0 (V:=V) j k c (hour Kₜ S a z) (clockW Kₜ a z f):=by rw [shiftHour]; exact Tax.fireW Y h a s i0 _ (Tax.fireW Y h a s i0 0 p)
lemma Tax.join (t:Tax Y h s i0 (V:=V) j k c S f) (u:Tax Y h s i0 (V:=V) n M v T g)(p:0≤c)(q:0 ≤ v)(e:SeatRange r (side Y i0 s) S T): Tax Y h s i0 (V:=V) (j+n) (k+M) (c*v) (S∪T) (f*g):=by
 unfold Tax; rw [joinW,sold_mult, SalonG.region_union]; apply Hull.join t u p q; refine Finset.disjoint_left.mpr (fun i y q=>?_); specialize e i y i q; simp at e
variable (x: Studio a 0 (yard (tent Y h) d) (reserve Λ l) S)(hc:0≤c)
local notation "η"=> reserve Λ l
local notation "T₁"=> proceed_set Kₜ a d S n
include x hc
lemma Tax.train (p:Tax Y h s i0 (V:=V) k 0 c S f)(q:proceed (tent Y h) n d ≤ (side Y i0 s).val): ∃ u v:ℕ, u+v=n*k ∧ Tax Y h s i0 (V:=V) u v (c^n) (proceed_set Kₜ a d S n) (SalonG.Train Kₜ a d f n):= by
 induction n with
 | zero=> refine ⟨0,0,?_,?_⟩;· omega -- n*k zero
          rw [proceed_set,SalonG.Train, Tax,identityW, sold_one, pow_zero]; exact Hull.base _
 | succ n ih=>
   rw [proceed_succ] at q; obtain ⟨u,v,hz,xn⟩:= ih (by omega); let z:= (yard Kₜ d:ℤ); let r_:=refract a (gaugeShift B d) S; let v0:= S∪ r_; let U':= clockW Kₜ a d (SalonG.Train Kₜ a d f n); let T':= hour Kₜ (proceed_set Kₜ a d S n) a d
   have hu:SeatRange (spaceBill Λ l) (side Y i0 s) (S∪r_) T':= seat_separate a (N) (S:=S∪r_) (y:=z) ((x.union (arbour x)).earlier (by omega)) ((shift_port Kₜ a (n:=n) x).later (by rw [proceed_succ]; omega))
   rw [pow_succ',SalonG.Train,proceed_set,reamW]; split_ifs with e
   · exact ⟨k+u,0+v,(by rw [Nat.succ_mul]; omega), Tax.join Y h s i0 (f:=f) (g:=U') (Hull.expand p _ (image_subset_image subset_union_left)) (Tax.tickW Y h a s i0 d xn) hc (pow_nonneg hc _) hu⟩
   exact ⟨0+u,k+v,(by rw [Nat.succ_mul]; omega),Tax.join Y h s i0 (f:=mateW Kₜ a d f) (g:=U') (Hull.expand (Tax.fireW Y h a s i0 (gaugeShift B d) p) _ (image_subset_image subset_union_right)) (Tax.tickW Y h a s i0 d xn) hc (pow_nonneg hc _) hu⟩
lemma Tax.jacket (p:Tax Y h s i0 (V:=V) k 0 c S f)(q:proceed (tent Y h) n d ≤ (side Y i0 s).val): Tax Y h s i0 (V:=V) (n*k) (n*k) (c^(2*n)) (blanket a d n (K:=Kₜ) S) (Jacket a d n f):= by
 obtain ⟨u,v,e,xn⟩:= Tax.train Y h a s i0 x hc p q; have hs:= Tax.fireW Y h a s i0 0 xn; have hv:later 0 (N) (T₁) a η:= (proceed_geo Kₜ a d n x).later (by omega); rw [two_mul,pow_add,← e]; exact lemm Y h _ _ hs xn hc (seat_separate a (N) (y:=0) (S:=refract a 0 (T₁)) (by rw [cold_twice]; exact hv) hv)
where
 lemm (Y':Course Λ (VolumeCape.Dream.Nimbus l))(h':Real.exp 1≤ Λ.x) (s0 i':ℕ){q u v:ℕ}{U: Literature (side Y' i' s0)} {A Bt:Finset Cover} {f g:W (tent Y' h')}(t:Tax Y' h' s0 i' (V:=U) u v (c^n) A f)(x:Tax Y' h' s0 i' (V:=U) v u (c^n) Bt g)(c':0≤c)(g1:SeatRange q (side Y' i' s0) A Bt): Tax Y' h' s0 i' (V:=U) (v+u) (v+u) (c^n*c^n) (A∪Bt) (f*g):= by
   have he:= Tax.join Y' h' s0 i' t x (pow_nonneg c' _) (pow_nonneg c' _) g1; rwa [Nat.add_comm u v] at he -- try
lemma Tax.carrier (p:Tax Y h s i0 (V:=V) k 0 c S f)(q:2*proceed (tent Y h) n d≤(side Y i0 s).val):Tax Y h s i0 (V:=V) (2*n*k) (2*n*k) (c^(4*n)) (terrace (K:=Kₜ) a d n S) (CarrierF a d n f):=by
 have he:=Tax.jacket Y h a s i0 x hc p (by omega:proceed Kₜ n d≤ (N).val); let z:= (proceed Kₜ n d:ℤ); let T:=blanket a d n (K:=Kₜ) S; have ht:=Tax.fireW Y h a s i0 z he; have hx:= blanket_on a d n S x q
 have hp:= Tax.join Y h s i0 he ht (pow_nonneg hc _) (pow_nonneg hc _) (seat_separate a (N) (y:=z) hx hx); rwa [show 4*n=2*n+2*n from by omega, pow_add, show 2*n*k=n*k+n*k from by ring] -- target, exact hp?? `rwa` uses assumption
#print axioms Tax.carrier
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
