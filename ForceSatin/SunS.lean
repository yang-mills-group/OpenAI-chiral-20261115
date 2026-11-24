import ForceSatin.Confine
import ForceSatin.Hose
import Risa.Testify
import YM.Work.H03
import YM.Push.LOCAL_SPLITTING.Orientation
-- Actual face, payer for stint footprints
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 280000
set_option synthInstance.maxSize 18000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Gleam.Luster.Risa.Gentle
open Next.SectorChange Next.SectorChange.Gaussian Function Filter MeasureTheory Metric Finset RG Lattice Wilson Tree Precision Pressure Exterior Next.Rank.Spindle Work.F03 Fineness Regis ProbabilityTheory Module
open scoped Topology ContDiff BigOperators Classical ENNReal
variable {c n:Side}{r:Ratio c n}{G:Gauge}{p:BudgetPoint}{U:Config G n}{S V:Support n}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}{A:Support c}{a C K v v' τ β y σw κ ℓ:ℝ}{R:Rules G} {Z:PathData G}{B:Bed} {q:Clip}{m w:ℕ}
variable (H:Z.Bounds q a C K)(P:Attached B Z)(L:Floor B q n τ v') (O:Bid.Sworn B n G)
open Regis.Head CF.Scree Push.Local
local notation "וּ"=> starFee H P r A D m Y β X
namespace Solace
abbrev ShapeLight (G:Gauge)(n:Side):= Cell n × G.ColorIndex
abbrev faceLoan (F:PlaqAxes):RG.Slot:=⟨[],F⟩
abbrev colorCash (G:Gauge) :ℕ:= sup (univ : Finset (PlaqAxes×Signed)) fun i=> (skewSlot G (faceLoan i.1) i.2).length
lemma vouched (F: PlaqAxes) (σ:Signed): (skewSlot G (faceLoan F) σ).length≤ colorCash G := Finset.le_sup (f:=fun i:PlaqAxes×Signed=> (skewSlot G (faceLoan i.1) i.2).length) (b:=(F,σ)) (mem_univ _)
variable (i:ShapeLight G n)(σ:Signed)(t:Site n)
abbrev caper : Site n:= affine σ t i.1.1
abbrev rake : RG.Slot:=skewSlot G (faceLoan i.1.2) σ
abbrev ticket : Cell n:= slotFace (rake i σ) (caper i σ t)
abbrev lustFace : ℝ:=skewSig G (faceLoan i.1.2) σ
abbrev colorLeg (y:ℝ)(U:Config G n):ℝ:= y* G.curvature (faceValue U i.1) i.2
abbrev lightC (i:ShapeLight G n) (θ:ℝ): Altar G n→ₗ[ℝ] ℝ:= ((θ:ℝ) • ((EuclideanSpace.proj i.2).toLinearMap.comp (Etch.river q i.1))) -- math lemma
noncomputable def LpSign (σ:Signed)(t:Site n)(q:Clip)(i:ShapeLight G n)(y:ℝ): Altar G n→ₗ[ℝ] ℝ:= lustFace i σ • lightC (q:=q) (ticket i σ t,i.2) y
lemma pay_ag (x:Altar G n) : LpSign σ t q i y x=y*lustFace i σ*((Real.sqrt q.direct)⁻¹*x (ticket i σ t,false,i.2)):=by change lustFace i σ*(y*((Real.sqrt q.direct)⁻¹*x (ticket i σ t,false,i.2))) = _; ring -- maybe cup reducible needs change
lemma tuning (x:Dir G n): LpSign σ t q i y (tiler H P x)= lightC i y (q:=q) (tiler H P (bank σ t x)):=by
 have e(f:Cell n) (x:Dir G n):lightC (G:=G) (f,i.2) y (q:=q) (tiler H P x)= y*faceCurl f x i.2:=by change y * (Etch.river q f (tiler H P x)) i.2=_; rw [Etch.river_now q H P]
 change lustFace i σ*lightC _ y (tiler H P x)= lightC (i.1,i.2) y (q:=q) _
 rw [e,e]; have he: slotFace (faceLoan i.1.2) i.1.1=i.1:=by simp [Slot.offset,slotFace,stop]
 rw [show faceCurl i.1 (bank σ t x) = lustFace i σ • faceCurl (ticket i σ t) x from (by calc _= faceCurl (slotFace (faceLoan i.1.2) i.1.1) (bank σ t x) := by rw [he]
                                                                                          _= _ := reflex ..)]; change _ = y*(lustFace i σ*(faceCurl (ticket i σ t) x i.2)); ring
lemma ticketCover (p:Lattice.halo (colorCash G) {i.1.1}⊆ S): (ticket i σ t).1 ∈ S.image (affine σ t):=by
 obtain ⟨b,g⟩:= (turnSites σ t).surjective (ticket i σ t).1
 have he: separation i.1.1 b=separation (caper i σ t) (ticket i σ t).1:= ((turn_sep σ t _ _).symm.trans (congrArg (separation (caper i σ t)) g))
 exact mem_image.mpr ⟨b,p (halo_spec.mpr ⟨_,mem_singleton_self _, he.trans_le ((Work.E04.slot_separation ..).trans (vouched ..))⟩),g⟩
def chordAllowance(q:Clip)(M:ℝ):ℝ:= M*(Real.sqrt q.direct)⁻¹
lemma beam_low {M:ℝ}(h:0≤M):0≤chordAllowance q M:=by unfold chordAllowance; positivity
lemma CPrice (z:ℝ) {w:ℝ} (_: |z| ≤ w) (U:Altar G n): |LpSign σ t q i z U| = |z| *(Real.sqrt q.direct)⁻¹ * |U (ticket i σ t,false,i.2)|:=by rw [pay_ag,abs_mul,abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt q.direct)⁻¹), show |lustFace i σ|=1 from skewSq ..]; ring
lemma coordinate (f:Cell n × Bool × G.ColorIndex)(p:f.1.1∈S)(x:Altar G n): |x f|≤ traceNorm S x:= by apply (sq_le_sq₀ (abs_nonneg _) (traceNorm_p ..)).mp; rw [traceNorm_sq,sq_abs]; exact single_le_sum (f:=fun i=> (x i)^2) (fun i _=> sq_nonneg _) (mem_filter.mpr ⟨mem_univ _,p⟩)
lemma coordinateG (x:G.Color)(i:G.ColorIndex):|x i|≤‖x‖:= by apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp; rw [EuclideanSpace.real_norm_sq_eq,sq_abs]; exact single_le_sum (f:=fun i=> (x i)^2) (fun i _=>sq_nonneg _) (mem_univ _)
lemma C_local (p:Lattice.halo (colorCash G) {i.1.1}⊆ S) (x z:Altar G n) (hp:|y|≤ v): |LpSign σ t q i y x-LpSign σ t q i y z| ≤ chordAllowance q v * traceNorm (S.image (affine σ t)) (x-z):=by rw [← _root_.map_sub,CPrice i _ _ _ hp]; exact mul_le_mul (mul_le_mul_of_nonneg_right hp (by positivity)) (coordinate (ticket i σ t,false,i.2) (ticketCover i σ t p) _) (abs_nonneg _) (beam_low ((abs_nonneg _).trans hp))
lemma C_unif (hp:|y|≤v): ‖(LpSign σ t q i y).toContinuousLinearMap‖ ≤ chordAllowance q v:=by
 let W:=LpSign σ t q i y; refine ContinuousLinearMap.opNorm_le_bound _ (beam_low ((abs_nonneg _).trans hp)) fun x=>?_ ; change |W x| ≤ _; unfold W; rw [CPrice i _ _ _ hp]; exact mul_le_mul (mul_le_mul_of_nonneg_right hp (by positivity)) ((coordinate (ticket i σ t,false,i.2) (mem_univ _) _).trans (norm_gains _)) (abs_nonneg _) (beam_low ((abs_nonneg _).trans hp))
lemma color_cash (U:Config G n)(p:pingS v S U)(h:i.1.1 ∈ S): |colorLeg i y U| ≤ |y| *v:=by
 unfold colorLeg; rw [abs_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
 apply ((coordinateG ..).trans (G.curvature_norm ..)).trans (p i.1 (Finset.not_disjoint_iff.mpr ⟨_,h,?_⟩)).le
 simp [touched,square,visits] -- tune
lemma grant_lane (h:TrustLogs (X+Y) U r A v)(p:0≤v)(u:v ≤ R.c)(hp:0<β)(t₁: stint r m A D (caper i σ t))(g:colorCash G ≤ m): |colorLeg i y (pull σ t U)- LpSign σ t q i (y*coupling β) (starFee H P r A D m Y β X)| ≤ |y| * slotError R (colorCash G) v:=by
 -- use grantSlot. face.Adhesion actual
 let s:=ticket i σ t; let j:=i.1.1; let W:= LpSign σ t q i; let b:=caper i σ t
 have he:zenith r D A m s:=by
    have ht: separation b s.1 ≤ m:= ((Work.E04.slot_separation ..).trans (vouched ..)).trans g
    refine ⟨t₁.1.shift ?_,(fun x a=>?_)⟩ -- shift explicit arg?
    · change separation b s.1+Sequest m ≤ _; unfold hallBill Sequest; omega
    have hu:=t₁.2 _ a; change hallBill m < separation x.1 b at hu
    rw [separation_comm b] at ht; have hz:=separation_triangle x.1 s.1 b; unfold hallBill Sequest at *; omega
 have hh: Etch.river q s (starFee H P r A D m Y β X)= (coupling β)⁻¹ • (faceCurl s (X+Y)):=by
    unfold starFee; rw [_root_.map_smul,here_s H P _ _ X Y q rfl _ he]
 let L:= faceLoan i.1.2; let z:=rake i σ; let Yp:=z.atSite U b
 have hv:L.atSite (pull σ t U) j= G.curvature (faceValue (pull σ t U) i.1):=by rw [atSite_path]; unfold L faceLoan; simp [slotFace,Slot.offset,Lattice.travel,stop,j]
 rw [colorLeg,←hv,show L.atSite (pull σ t U) j= lustFace i σ • Yp from reflects ..]; change |y*(lustFace i σ* (Yp i.2))- lustFace i σ*((y*coupling β)*(Etch.river q s (starFee ..) i.2))|≤_; rw [hh]; change |y*_ -lustFace i σ*(_*((coupling β)⁻¹*faceCurl s (X+Y) i.2))| ≤ _
 rw [show y*_-_ = y*lustFace i σ*((Yp-faceCurl s (X+Y)) i.2) from ?_, abs_mul,abs_mul, show |lustFace i σ|=1 from skewSq ..,mul_one]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); refine (coordinateG ..).trans (grantSlot h p u _ (t₁.1.shift ?_) (vouched ..)); simp [b,hallBill,Sequest]; omega
 have hc:= coupling_pos hp; change _ = _*(Yp i.2-faceCurl s (X+Y) i.2); field_simp
lemma pingCommutes : pingS v S (pull σ t U) ↔ pingS v (S.image (affine σ t)) U:=by
 let F:= Equiv.ofBijective (Face.send σ t) ⟨Face.injective_send σ t,Finite.injective_iff_surjective.mp (Face.injective_send σ t)⟩
 have he(i:Cell n) : Disjoint (S.image (affine σ t)) (touched (F i)) ↔ Disjoint S (touched i) :=by rw [show touched (F i)=_ from Work.H03.touched_send (σ) t i]; exact Finset.disjoint_image (turnSites σ t).injective
 have hC(i:Cell n): G.chord (faceValue (pull σ t U) i)=G.chord (faceValue U (F i)):= Face.send_price U i σ t G.chord G.chord_inv fun x y=>G.chord_conj y x
 constructor
 · intro h x a; obtain ⟨y,rfl⟩:=F.surjective x; rw [←hC]; exact h y ((he y).mpr.mt a)
 intro h x a; rw [hC]; exact h (F x) ((he x).mp.mt a)
lemma pingClear (g:fullLease A (weak v U) (S.image (affine σ t)) r m) (u:v≤v')(a:V⊆S): pingS v' V (pull σ t U):=by
 apply (pingCommutes _ _).mpr; intro i h; obtain ⟨j,f,t⟩:=Finset.not_disjoint_iff.mp h; apply LT.lt.trans_le _ u; apply lt_of_not_ge; intro p; have hv:= (g j (Finset.image_mono _ a f)).2 i ((weak_mem _).mpr p); have ht:= Work.E01.sep_touched i j t; unfold hallBill Sequest at hv; omega
-- budget on polynomial power of actual Gaussian.P
open Regis.Resonance Lull InnerProductSpace
variable {F:Type*}[DecidableEq F] (f:F→ ShapeLight G n) (W:List F)
noncomputable abbrev toCone (x:Altar G n→ₗ[ℝ] ℝ): Altar G n:= (toDual ℝ (Altar G n)).symm (x.toContinuousLinearMap.comp (stamen H P n).starProjection)
lemma cone (x:Altar G n→ₗ[ℝ] ℝ)(v:Altar G n): inner ℝ (toCone H P x) v= x ((stamen H P n).starProjection v):=by rw [toCone,InnerProductSpace.toDual_symm_apply]; rfl
lemma cone_p (x:Altar G n→ₗ[ℝ] ℝ): ‖toCone H P x‖ ≤ ‖x.toContinuousLinearMap‖:=by rw [toCone,LinearIsometryEquiv.norm_map]; refine (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) ?_); exact (stamen H P n).starProjection_norm_le
abbrev Sun (H:Z.Bounds q a C K) (P:Attached B Z)(y:ℝ)(i:ShapeLight G n):=toCone H P (lightC (q:=q) i y)
def axisSumC (W:List F)(f:F→ ShapeLight G n)(H:Z.Bounds q a C K)(P:Attached B Z)(y:ℝ):ℝ:=memo (W.map (Sun H P y ∘ f))
lemma axisCandle (y:ℝ): axisSumC W f H P y=priceW (pairP (Sun H P y ∘ f)) W:= (Lull.shining W.length W _ (fun _ _=> rfl) le_rfl).symm
-- algebraic cloud comparison on face moments
noncomputable abbrev sunDay (W:List F)(Y:F→ Altar G n→ₗ[ℝ] ℝ)(x:Altar G n):= (W.map fun i=> Y i x).prod
lemma sunDiff (Y:F→ Altar G n→ₗ[ℝ] ℝ): Continuous (sunDay W Y):=by induction W with| nil=>exact continuous_const| cons i W ih=> exact (Y i).toContinuousLinearMap.continuous.mul ih
lemma sunSkirt (Y:F→ Altar G n→ₗ[ℝ] ℝ) (x:Altar G n): sunDay W Y ((stamen H P n).starProjection x) = payday (W.map ((toCone H P) ∘ Y)) x:=by rw [Lull.innerU]; apply congrArg List.prod; apply List.map_congr_left; intro i a; exact (cone H P (Y i) x).symm
lemma sunCloud (Y:F→ Altar G n→ₗ[ℝ] ℝ): clouds H P (sunDay W Y) = memo (W.map ((toCone H P) ∘ Y)):=by simp_rw [←cloud_turn H P _ (sunDiff W Y),sunSkirt]
abbrev duskLeg (y:ℝ) (σ:Signed) (t:Site n)(q:Clip)(i:ShapeLight G n):= LpSign σ t q i y
include L O
lemma axisBonnet (y:ℝ): axisSumC W f H P y=memo (W.map (toCone H P ∘ duskLeg y σ t q ∘ f)):=by
 unfold axisSumC; change memo (W.map (toCone H P ∘ (fun i => lightC i y (q:=q)) ∘ f))=_
 simp_rw [← sunCloud H P W]; apply cover_calms σ t H P L O _ _ (sunDiff W _) (fun z=>?_) -- maybe simp_rw cloud
 apply congrArg List.prod; apply List.map_congr_left; intro i _; exact (tuning H P (f i) σ t z).symm
lemma bonnetBound (v:ℝ)(u:|y|≤v)(w:W.length≤ m) : |axisSumC W f H P y| ≤ 1+(m:ℝ)*PBound (chordAllowance q v) m:=by
 rw [axisBonnet H P L O (1:Signed) (0:Site n)]; exact Lull.innerPrice _ (beam_low ((abs_nonneg _).trans u)) _ (fun i _=>(cone_p H P _).trans (C_unif (f i) _ _ u)) w
omit L O
abbrev prism (W:List F) (q:Clip)(v y:ℝ)(f:F→ ShapeLight G n)(σ:Signed)(t:Site n)(x:Altar G n):ℝ:= (W.map fun i=> scarfLens v (duskLeg y σ t q (f i) x)).prod
lemma prismDiff (y v:ℝ) : ContDiff ℝ 1 (prism W q v y f σ t):=by induction W with| nil=> exact contDiff_const| cons i W ih=> exact ((scarfDiff v).comp (duskLeg y σ t q (f i)).toContinuousLinearMap.contDiff).mul ih
lemma prismSkirt (y v:ℝ) (x:Altar G n): prism W q v y f σ t ((stamen H P n).starProjection x)= scarfView W (toCone H P ∘ duskLeg y σ t q ∘ f) v x:=by
 apply congrArg List.prod; apply List.map_congr_left; intro i a; rw [show inner ℝ ((toCone H P ∘ duskLeg y σ t q ∘ f) i) x=_ from cone ..]; rfl
variable (p1:1≤v)(y:ℝ) {w':ℝ} (z:|y|≤w') (p0:W.length ≤ m)
include p1 p0
lemma compareFeeU  (x:Altar G n): |prism W q v y f σ t x|≤(2*v)^m:= (low (fun i=> scarfLens v (duskLeg y σ t q (f i) x)) W (by positivity : 0≤2*v) (fun i _=>(velvetBound v _ (zero_lt_one.trans_le p1)).2.1)).trans (pow_le_pow_right₀ (by linarith only [p1]) p0)
include z
lemma compareFeeV (h:∀ i∈W,Lattice.halo (colorCash G) {(f i).1.1}⊆ S) (x b:Altar G n): |prism W q v y f σ t x-prism W q v y f σ t b| ≤ m*(2*v)^m * (loan*(chordAllowance q w')) * traceNorm (S.image (affine σ t)) (x-b):=by
 let c:= zero_lt_one.trans_le p1; let D:= chordAllowance q w'; have hd:0≤D:=beam_low ((abs_nonneg _).trans z); let N:=traceNorm (S.image (affine σ t)) (x-b); have hN:0≤ N:=traceNorm_p ..; have hr(i:F)(x):= (velvetBound v (duskLeg y σ t q (f i) x) c).2.1; let F'(x) (i:F):= scarfLens v (duskLeg y σ t q (f i) x)
 refine (compareAt (F' x) (F' b) W (M:=2*v) (by linarith only [p1]) (η:=loan*(D*N)) (by positivity) (fun i _=>hr i x) (fun i _=>hr i b) (fun i a=> (hose_lp _ _ _ c).trans (mul_le_mul_of_nonneg_left (C_local (f i) _ _ (h i a) _ _ z) loan.prop))).trans ?_
 change _ ≤ _*(_*D)*N; rw [mul_assoc _ ((loan:ℝ)*D) N,mul_assoc _ D N]; have p:1 ≤ 2*v:= (by linarith only [p1]); gcongr
include O L
lemma compareFee (k:ℕ): |axisSumC W f H P y - ∫ i, prism W q v y f σ t ((stamen H P n).starProjection i)∂stdGaussian _| ≤(v^k)⁻¹*(2*((m:ℝ)*PBound (chordAllowance q w') (m+k))):=by
 simp_rw [axisBonnet H P L O σ t f W y,prismSkirt]; exact Lull.fare k _ (beam_low ((abs_nonneg _).trans z)) _ (fun i _ => (cone_p H P _).trans (C_unif (f i) σ t z)) p1 p0
#print axioms compareFee
#print axioms compareFeeV
#print axioms grant_lane
#print axioms C_local
#print axioms tuning
end Solace
end YM.Gleam.Luster.Risa.Gentle
