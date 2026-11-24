import YM.SU5.FiniteGaugeData.CodaT.Print
import YM.SU5.FiniteGaugeData.Eight.Likeness
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
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
open YM.SU5.FiniteGaugeData.CodaT Eight
/- coupon assembly in analogy with WP8 Invoice---no scales except the original publisher supplies from the start, at THIS price. -/
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
variable (a i:Axis)
variable {Ck Z:Side} {K:Calibration} {S T:Finset Cover} {j k M d r n w:ℕ}
variable (s i0:ℕ)
local notation "N"=> side Y i0 s
local notation "Kₜ"=> tent Y h
local notation "B"=> (tent Y h).B
local notation "L"=> (Y.voyage i0).CapeT s
local notation "V₀"=> proceed (tent Y h)
variable {f g: W (tent Y h)} {J T':Tilt (side Y i0 s)}{C c v ξ G α b:ℝ}
local notation "σ₀"=> sold Y h s i0
abbrev Rent (J T':Tilt N)(w:ℕ)(v b c ξ G α:ℝ)(n:ℕ) (S:Finset Cover)(x: W (tent Y h)) := Post J T' w v b c ξ G α n (region S (side Y i0 s)) (sold Y h s i0 x.val)
local notation "Π'"=> Rent Y h s i0 J T' w v b c ξ G α
variable (Fb:Fable J T')
include Fb
lemma Rent.fireW (z:ℤ)(p:Π' k S f): Π' k (refract a z S) (fire Kₜ a z f):=by unfold Rent; rw [ice_print,sold_reflect,refl_region]; exact Post.turn Fb _ _ p
lemma Rent.tickW (z:ℤ)(p:Π' k S f): Π' k (hour Kₜ S a z) (clockW Kₜ a z f):=by rw [shiftHour]; exact Rent.fireW Y h a s i0 Fb _ (Rent.fireW Y h a s i0 Fb 0 p)
omit Fb in
lemma Rent.join (t:Π' k S f) (u:Π' M T g)(e:SeatRange r (side Y i0 s) S T): Π' (k+M) (S∪T) (f*g):=by
 unfold Rent; rw [joinW,sold_mult, SalonG.region_union]; apply Post.both t u; refine Finset.disjoint_left.mpr (fun i y q=>?_); specialize e i y i q; simp at e
variable (x: Studio a 0 (yard (tent Y h) d) (reserve Λ l) S)
local notation "η"=> reserve Λ l
local notation "T₁"=> proceed_set Kₜ a d S n
include x
lemma Rent.Colony (p:Π' 1 S f)(q:proceed (tent Y h) n d ≤ (side Y i0 s).val): Π' n (proceed_set Kₜ a d S n) (SalonG.Train Kₜ a d f n):= by
 induction n with
 | zero=> rw [proceed_set,SalonG.Train, Rent,identityW, sold_one]; exact Post.unit _
 | succ n ih=>
   rw [proceed_succ] at q; have xn:= ih (by omega); let z:= (yard Kₜ d:ℤ); let r_:=refract a (gaugeShift B d) S; let v0:= S∪ r_; let U':= clockW Kₜ a d (SalonG.Train Kₜ a d f n); let S':= hour Kₜ (proceed_set Kₜ a d S n) a d
   have hu:SeatRange (spaceBill Λ l) (side Y i0 s) (S∪r_) S':= seat_separate a (N) (S:=S∪r_) (y:=z) ((x.union (arbour x)).earlier (by omega)) ((shift_port Kₜ a (n:=n) x).later (by rw [proceed_succ]; omega))
   rw [SalonG.Train,proceed_set,reamW,show n+1=1+n from by omega]; split_ifs with e
   · exact Rent.join Y h s i0 (f:=f) (g:=U') (Post.expand p (image_subset_image subset_union_left)) (Rent.tickW Y h a s i0 Fb d xn) hu
   exact Rent.join Y h s i0 (f:=mateW Kₜ a d f) (g:=U') (Post.expand (Rent.fireW Y h a s i0 Fb (gaugeShift B d) p) (image_subset_image subset_union_right)) (Rent.tickW Y h a s i0 Fb d xn) hu
lemma Rent.jacket (p:Π' 1 S f)(q:proceed (tent Y h) n d ≤ (side Y i0 s).val): Π' (2*n) (blanket a d n (K:=Kₜ) S) (Jacket a d n f):= by
 have xn:= Rent.Colony Y h a s i0 Fb x p q; have hs:= Rent.fireW Y h a s i0 Fb 0 xn; have hv:later 0 (N) (T₁) a η:= (proceed_geo Kₜ a d n x).later (by omega); rw [two_mul]; exact Rent.join Y h s i0 hs xn (seat_separate a (N) (y:=0) (S:=refract a 0 (T₁)) (by rw [cold_twice]; exact hv) hv)
lemma Rent.recycled (p:Π' 1 S f)(q:2*proceed (tent Y h) n d≤(side Y i0 s).val):Π' (4*n) (terrace (K:=Kₜ) a d n S) (CarrierF a d n f):=by
 have he:=Rent.jacket Y h a s i0 Fb x p (by omega:proceed Kₜ n d≤ (N).val); let z:= (proceed Kₜ n d:ℤ); let T:=blanket a d n (K:=Kₜ) S; have ht:=Rent.fireW Y h a s i0 Fb z he; have hx:= blanket_on a d n S x q; rw [show 4*n=2*n+2*n from by omega]; exact Rent.join Y h s i0 he ht (seat_separate a (N) (y:=z) hx hx)
omit Fb x
section
variable {n0 M₀ S₁:Side}{p M₁:Tilt n0} (O:Fable p M₁) {U V:Support (More n0)}{A B₀:Mark n0}{u t:ℕ}
local notation "Ω"=>Post p M₁ t v b c ξ G α
include O
lemma mirror_earns (y':Margin S₁ r k w u)(h:Mirror M₀ u n0 U A V B₀ n)(g:Post p M₁ t v b c ξ G α j U A) : Post p M₁ t v b c ξ G α (j*n) V B₀ := by
 induction h generalizing j with
 | self => simpa using g
 | @grow S F a z b0=>
   let T:= Heat.gaugeShift M₀ z; have he:Disjoint (S.image ((Buffered.plane a T).anon n0)) S:= by
      refine Finset.disjoint_left.mpr ?_; intro y e f; have he:= margin_separate a T y' y y (Finset.image_subset_image (f:=(Buffered.plane a T).anon n0) b0 e) (b0 f); simp at he
   rw [mul_two]; exact Post.both (Post.turn O a T g) g he
 | @trans _ _ _ _ _ _ m s e h a b => rw [←mul_assoc]; exact b (a g)
end
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
