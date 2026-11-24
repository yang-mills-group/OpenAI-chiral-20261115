import YM.SU5.FiniteGaugeData.Lapis.Packed
import YM.SU5.FiniteGaugeData.Eight.Likeness
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LapisS
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
open YM.SU5.FiniteGaugeData.Lapis Lumi Eight
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
variable {f g: W (tent Y h)} {ι:Type}[Fintype ι][DecidableEq ι]{A₀:Duct SU.group ι}{F₀:Clip} {C c v ξ G α b:ℝ}
local notation "σ₀"=> sold Y h s i0
abbrev Rent (A₀:Duct SU.group ι)(F₀:Clip)(v b α:ℝ)(n:ℕ) (S:Finset Cover)(x: W (tent Y h)) := Packed A₀ F₀ v b α n (region S (side Y i0 s)) (sold Y h s i0 x.val)
local notation "Π'"=> Rent Y h s i0 A₀ F₀ v b α

lemma Rent.fireW (z:ℤ)(p:Π' k S f): Π' k (refract a z S) (fire Kₜ a z f):=by unfold Rent; rw [ice_print,sold_reflect,refl_region]; exact Packed.turn p z a
lemma Rent.tickW (z:ℤ)(p:Π' k S f): Π' k (hour Kₜ S a z) (clockW Kₜ a z f):=by rw [shiftHour]; exact Rent.fireW Y h a s i0 _ (Rent.fireW Y h a s i0 0 p)

lemma Rent.join (t:Π' k S f) (u:Π' M T g)(e:SeatRange r (side Y i0 s) S T): Π' (k+M) (S∪T) (f*g):=by
 unfold Rent; rw [joinW,sold_mult, SalonG.region_union]; apply Packed.both t u; refine Finset.disjoint_left.mpr (fun i y q=>?_); specialize e i y i q; simp at e
variable (x: Studio a 0 (yard (tent Y h) d) (reserve Λ l) S)
local notation "η"=> reserve Λ l
local notation "T₁"=> proceed_set Kₜ a d S n
include x
lemma Rent.Colony (p:Π' 1 S f)(q:proceed (tent Y h) n d ≤ (side Y i0 s).val): Π' n (proceed_set Kₜ a d S n) (SalonG.Train Kₜ a d f n):= by
 induction n with
 | zero=> rw [proceed_set,SalonG.Train, Rent,identityW, sold_one]; exact Packed.unit _
 | succ n ih=>
   rw [proceed_succ] at q; have xn:= ih (by omega); let z:= (yard Kₜ d:ℤ); let r_:=refract a (gaugeShift B d) S; let v0:= S∪ r_; let U':= clockW Kₜ a d (SalonG.Train Kₜ a d f n); let S':= hour Kₜ (proceed_set Kₜ a d S n) a d
   have hu:SeatRange (spaceBill Λ l) (side Y i0 s) (S∪r_) S':= seat_separate a (N) (S:=S∪r_) (y:=z) ((x.union (arbour x)).earlier (by omega)) ((shift_port Kₜ a (n:=n) x).later (by rw [proceed_succ]; omega))
   rw [SalonG.Train,proceed_set,reamW,show n+1=1+n from by omega]; split_ifs with e
   · exact Rent.join Y h s i0 (f:=f) (g:=U') (Packed.expand p (image_subset_image subset_union_left)) (Rent.tickW Y h a s i0 d xn) hu
   exact Rent.join Y h s i0 (f:=mateW Kₜ a d f) (g:=U') (Packed.expand (Rent.fireW Y h a s i0 (gaugeShift B d) p) (image_subset_image subset_union_right)) (Rent.tickW Y h a s i0 d xn) hu
lemma Rent.jacket (p:Π' 1 S f)(q:proceed (tent Y h) n d ≤ (side Y i0 s).val): Π' (2*n) (blanket a d n (K:=Kₜ) S) (Jacket a d n f):= by
 have xn:= Rent.Colony Y h a s i0 x p q; have hs:= Rent.fireW Y h a s i0 0 xn; have hv:later 0 (N) (T₁) a η:= (proceed_geo Kₜ a d n x).later (by omega); rw [two_mul]; exact Rent.join Y h s i0 hs xn (seat_separate a (N) (y:=0) (S:=refract a 0 (T₁)) (by rw [cold_twice]; exact hv) hv)
lemma Rent.recycled (p:Π' 1 S f)(q:2*proceed (tent Y h) n d≤(side Y i0 s).val):Π' (4*n) (terrace (K:=Kₜ) a d n S) (CarrierF a d n f):=by
 have he:=Rent.jacket Y h a s i0 x p (by omega:proceed Kₜ n d≤ (N).val); let z:= (proceed Kₜ n d:ℤ); let T:=blanket a d n (K:=Kₜ) S; have ht:=Rent.fireW Y h a s i0 z he; have hx:= blanket_on a d n S x q; rw [show 4*n=2*n+2*n from by omega]; exact Rent.join Y h s i0 he ht (seat_separate a (N) (y:=z) hx hx)
omit x
section
variable {n0 M₀ S₁:Side} {U V:Support (More n0)}{A B₀:Mark n0}{u t:ℕ}
local notation "Ω"=>Packed A₀ F₀ v b α

lemma mirror_earns (y':Margin S₁ r k w u)(h:Mirror M₀ u n0 U A V B₀ n)(g:Packed A₀ F₀ v b α j U A) : Packed A₀ F₀ v b α (j*n) V B₀ := by
 induction h generalizing j with
 | self => simpa using g
 | @grow S F a z b0=>
   let T:= Heat.gaugeShift M₀ z; have he:Disjoint (S.image ((Buffered.plane a T).anon n0)) S:= by
      refine Finset.disjoint_left.mpr ?_; intro y e f; have he:= margin_separate a T y' y y (Finset.image_subset_image (f:=(Buffered.plane a T).anon n0) b0 e) (b0 f); simp at he
   rw [mul_two]; exact Packed.both (Packed.turn g T a) g he
 | @trans _ _ _ _ _ _ m s e h a b => rw [←mul_assoc]; exact b (a g)
end
end YM.CF.Buffered.Afterglow.Hierarchy.LapisS
