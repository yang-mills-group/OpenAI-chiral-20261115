import YM.SU5.SatinWard.Resolution.Juniper
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false -- positive/negative conditional split share
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey

open _root_.YM.Gleam.Luster.Risa Gentle Tiling
open BProof (scaleY PL)
open _root_.YM.Work.F03 _root_.YM.Regis
local notation "Uₛ" s:max i:max k:max => gram Y s i k
local notation "Kₛ" s:max k:max => Y.uv k - s
local notation "π₀"=> P.K.top.clip

-- uniform scalar exponents charges
open _root_.YM.Next.Rank.Spindle
open Gentle.Solace Rail
open _root_.YM.Regis.Resonance Lull
open Fineness
namespace Moon
-- genuine Mark polynomial & cost. Keep support and masks explicit; period registration asserted separately
variable {N:Side}{cN:Side}{r:Lattice.Ratio cN (More N)} (T:Tiling cN N r)
variable (S:Support (More N)){H₁:Bed} {Z:PathData SU.group}  {q:Clip} {η CS W t x β y:ℝ}
variable (R:Rules SU.group)(B:Z.Bounds q η CS W) (P₁:Attached H₁ Z)(L:Side)
variable {v' τ:ℝ}(M0:Floor H₁ q (More N) τ v') (O:Bid.Sworn H₁ (More N) SU.group)
open ProbabilityTheory
open Lifted Afterglow Satin Cygnet Loaves Horizons InnerProductSpace
open _root_.YM.Regis.Head
-- tan. build covariant matter pair & color path. actual replica estimators, phase winds paid at both
open FoliageP Lifted Loaves Horizons Afterglow.Tower
namespace Moonlit
-- public builders for the tensor optics. NB use Work.PointB convention. Not the interactive Ward certificate.
namespace SwitchC
namespace Garland
open CF.SU
-- vars
open Tapestry
namespace Terrace
namespace Juniper
-- Comptroller: on the way charge specific connected curvature through Wick books.
-- arbitrary width and T/kernel; note computations account even if zero or nonzero polynomial means
variable {o o':Cover} {hbytes:ℝ}
namespace Abacus
section
variable {ι J κ:Type*} [DecidableEq ι][DecidableEq J][DecidableEq κ] (A:Tab J) (B:Tab κ) (K:Finset ι)(W':ι→ Tab J) (w:ℂ)
noncomputable abbrev payT (f:Horizon→ℂ)(A:Tab J):=∑ i∈ A.cover,A.tax i * f (A.w i)
noncomputable abbrev varying (g:Horizon→ Horizon→ℂ):= payT (fun i=> payT (g i) B) A
variable (f:Horizon→ℂ)(g:Horizon→ Horizon→ℂ)
lemma co_change: payT f (mulT A B)= varying A B (fun i j=> f (coupler i j)):=by unfold varying payT; rw [mulT,sum_product]; simp_rw [mul_assoc, mul_sum]
lemma pay_pack : payT f (packT K W')=∑ i∈K,payT f (W' i):=by unfold payT packT; rw [sum_sigma]
lemma co_packL : varying (packT K W') B g=∑ i∈K,varying (W' i) B g:= pay_pack ..
lemma co_packR : varying B (packT K W') g=∑ i∈K,varying B (W' i) g:=by unfold varying; simp_rw [pay_pack]; unfold payT; simp_rw [mul_sum]; rw [sum_comm]
lemma pay_weight : payT f (weightT A w)= w*payT f A:=by unfold payT weightT; rw [mul_sum]; simp_rw [mul_assoc]
lemma pay_mul_const (q:Horizon→ℂ) : payT (fun k=> f k * q k) A=payT (fun k=> q k * f k) A:= by rw [show (fun k=> f k * q k)=(fun k=> q k * f k) from funext fun j=>mul_comm ..]
lemma pay_scl : payT (fun i=>w*f i) A=w*payT f A:= by unfold payT; rw [mul_sum]; simp_rw [mul_left_comm w]
lemma co_weightL: varying (weightT A w) B g=w*varying A B g:= pay_weight ..
lemma co_weightR: varying A (weightT B w) g=w*varying A B g:=by unfold varying; simp_rw [pay_weight]; exact pay_scl ..
lemma co_duo (f:Horizon→ℂ) : payT f A*payT f B=varying A B (fun i j=>f i*f j):=by unfold varying; simp_rw [pay_scl]; unfold payT; rw [sum_mul]; simp_rw [mul_sum,mul_assoc]
lemma pay_subT(g:Horizon→ℂ) : payT f A-payT g A= payT (fun i=>f i-g i) A:=by unfold payT; rw [←sum_sub_distrib]; simp_rw [mul_sub]
lemma co_sub (k:Horizon→ Horizon→ℂ) : varying A B g-varying A B k=varying A B (fun i j=>g i j-k i j):=by unfold varying; rw [pay_subT]; simp_rw [pay_subT]
noncomputable abbrev issuesBond (W:HorizonLens→HorizonLens→ℝ)(β t:ℝ):=(mulT A B).issues β W t-A.issues β W t*B.issues β W t
noncomputable abbrev road (f:Horizon→ℂ)(A B:Horizon):= f (coupler A B)- f A*f B
lemma intercity (W:HorizonLens→HorizonLens→ℝ)(β t:ℝ)(F:Horizon→ℂ)(h:F=Picker.colorWage W β t): issuesBond A B W β t=varying A B (road F):=by unfold issuesBond; rw [← show payT F A= _ from (by rw [h] : payT F A=A.issues β W t), ← show payT F B= _ from (by rw [h] : payT F B=B.issues β W t),← show payT F (mulT A B)= _ from (by rw [h] : payT F (mulT A B)=(mulT A B).issues β W t),co_change, co_duo]; exact co_sub ..
end
abbrev yoke (i j:Sage):ℂ:= if i=j then 1 else 0
lemma lieBasis (i j:Sage): Rail.cost 1 (Rail.lie i j)=yoke i j:=by unfold Rail.cost Rail.lieP Rail.f0 yoke; by_cases h:i=j <;> simp [eq_comm (a:=j),h]  -- h.symm inequality? .symm works
lemma selectCanon (f:Sage→ℂ)(i:Sage): ∑ j,yoke i j*f j=f i:=by
 rw [sum_eq_single i]
 · unfold yoke; rw [if_pos rfl,one_mul]
 · intro j _ h; rw [yoke,if_neg (Ne.symm h),zero_mul];
 simp -- indentation error
lemma duoK (W:HorizonLens→HorizonLens→ℝ)(a b:HorizonLens): Lull.priceW W [a,b]= W a b:=by simp [Lull.priceW,Lull.candle,Lull.candles] -- check reduction
lemma fourK (W:HorizonLens→HorizonLens→ℝ)(a b c d:HorizonLens): Lull.priceW W [a,b,c,d]= W a b*W c d+(W a c*W b d+ W a d* W b c):=by simp [Lull.priceW,Lull.candle,Lull.candles]
-- lens reductions. Compass.Warm.
variable {M₁ M₂:MaskShape} (Wk:HorizonLens→HorizonLens→ℝ){bill:ℝ}(A B:CSocket o) (A' B': CSocket o')
local notation "ϑ" => Picker.colorWage Wk bill (Real.sqrt bill)
variable (e:0<bill) (h:Loaves.zTariff []=1)
include e h
lemma kaleidoscope (V:Horizon)(v:V.song=[]): ϑ V=(V.cabin.map (fun i=>Rail.cost 1 i.step)).prod * (Lull.priceW Wk V.face:ℝ):= by rw [shirt (Wp:=fun _=>Wk) 0 (βm:=fun _=> bill) V e, v,h,mul_one] -- probably rw pattern fails
abbrev capsuleP {o:Cover}(A B:CSocket o)(M:MaskShape)(i j a b:Sage):= coupler (lensT M A i a) (lensT M B j b)
local notation "Z*" A:max B:max M:max => capsuleP A B M
lemma scholarCabin (M:MaskShape)(i j a b:Sage): ϑ (capsuleP A B M i j a b)= yoke i a*(yoke j b)*(Wk (A.p,a) (B.p,b):ℝ):=by
 rw [kaleidoscope Wk e h _ rfl]; unfold capsuleP coupler lensT
 simp [duoK, lieBasis]
-- Road.Lap use Prod prefixed. colours collapse ordered only at caller
abbrev nextSea (p q a b:Face ℤ)(i j u v:Sage) :ℂ:= ((Wk (p,i) (a,u)* Wk (q,j) (b,v)+Wk (p,i) (b,v)* Wk (q,j) (a,u):ℝ):ℂ)
lemma scholarRoad (i j p q a b c d:Sage): road ϑ (capsuleP A B M₁ i j a b) (capsuleP A' B' M₂ p q c d)=yoke i a * (yoke j b) * (yoke p c*(yoke q d))* nextSea Wk A.p B.p A'.p B'.p a b c d:=by
 unfold road; rw [kaleidoscope Wk e h _ rfl,scholarCabin _ _ _ e h, scholarCabin _ _ _ e h]; unfold capsuleP coupler lensT nextSea; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,List.cons_append,List.nil_append,fourK,lieBasis]; push_cast; ring
private abbrev baseCup {o:Cover}(M:MaskShape)(A B:CSocket o)(i:Sage):=mulT (lensBeam M A i) (lensBeam M B i)
omit h e in
lemma pickCup (f:Sage → Sage→ℂ)(k:Sage): ∑ a:Sage, ∑ b:Sage, yoke k a*yoke k b*f a b=f k k:=by simp_rw [mul_assoc]; simp_rw [←mul_sum,selectCanon]
lemma captainM {M:MaskShape}(i:Sage): payT ϑ (baseCup M A B i)=(Wk (A.p,i) (B.p,i):ℝ):=by
 unfold payT baseCup mulT; rw [sum_product]; -- simplify
 change (∑ a:Sage,∑ b:Sage,(1*1:ℂ)*ϑ (capsuleP A B M i i a b))=_; simp_rw [one_mul, scholarCabin Wk A B e h]; exact pickCup (fun i j=>_) _
omit h e in
private lemma spin_select (f:Horizon→ Horizon→ℂ)(d:Sage→ Sage→ Sage→ Sage→ℂ)(i j:Sage) (u:∀ a b c b', f (capsuleP A B M₁ i i a b) (capsuleP A' B' M₂ j j c b')=yoke i a*yoke i b*(yoke j c*yoke j b')*d a b c b') : varying (baseCup M₁ A B i) (baseCup M₂ A' B' j) f=d i i j j:=by
 unfold varying payT baseCup mulT; rw [sum_product]; simp_rw [sum_product]; change (∑ a:Sage,∑ b:Sage,(1*1:ℂ)*(∑ c:Sage,∑ b':Sage,(1*1:ℂ)*f (capsuleP A B M₁ i i a b) (capsuleP A' B' M₂ j j c b')))=_; simp_rw [u,one_mul,mul_assoc]
 simp_rw [←mul_sum]; simp_rw [selectCanon] -- may need reapply
lemma chiefRoad (i j:Sage): varying (baseCup M₁ A B i) (baseCup M₂ A' B' j) (road ϑ)= nextSea Wk A.p B.p A'.p B'.p i i j j:= spin_select _ _ _ _ _ _ i j (fun _ _ _ _=> scholarRoad _ _ _ _ _ e h ..)
-- pigment then combos. keep two case mean and contrast price.
lemma terraS (M:MaskShape): payT ϑ (Terra M M A B)=∑ i:Sage,(Wk (A.p,i) (B.p,i):ℂ):=by unfold Terra; rw [pay_pack]; exact sum_congr rfl fun i _=> captainM Wk A B e h i
abbrev chroma (A B:CSocket o) (A' B':CSocket o') := ∑ i:Sage,∑ j:Sage, nextSea Wk A.p B.p A'.p B'.p i i j j
lemma co_terra: varying (Terra M₁ M₁ A B) (Terra M₂ M₂ A' B') (road ϑ)=chroma Wk A B A' B':=by
 unfold Terra; rw [co_packL]; simp_rw [co_packR]; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=> chiefRoad _ _ _ _ _ e h _ _
variable (F G F' G':PlaqAxes) (O O':Cover) (t:ℝ)
def flatPairC (F G:PlaqAxes)(x:Cover)(c:CupCoin): Face ℤ × Face ℤ := ((cornerT F x c.1).p,(cornerT G x c.2).p)
abbrev employ (F G:PlaqAxes)(x:Cover):ℂ:= ∑ c:CupCoin,(1/16:ℂ)* (∑ i:Sage,(Wk ((flatPairC F G x c).1,i) ((flatPairC F G x c).2,i):ℂ))
abbrev employ2:ℂ:= ∑ c:CupCoin,(1/16:ℂ)*∑ d:CupCoin,(1/16:ℂ)* chroma Wk (cornerT F O c.1) (cornerT G O c.2) (cornerT F' O' d.1) (cornerT G' O' d.2)
lemma employPig : payT ϑ (pigment F G O t)= employ Wk F G O:=by unfold pigment; rw [pay_pack]; apply sum_congr rfl; intro i _; unfold hinge; rw [pay_weight,terraS _ _ _ e h]; rfl
lemma employPig2: varying (pigment F G O t) (pigment F' G' O' t) (road ϑ)= employ2 Wk F G F' G' O O':=by unfold pigment employ2; rw [co_packL]; apply sum_congr rfl; intro i _; rw [hinge,co_weightL,co_packR]; congr 1; apply sum_congr rfl; intro j _; unfold hinge; rw [co_weightR,co_terra _ _ _ _ _ e h]
end Abacus
end Juniper
end Terrace
end Garland
end SwitchC
end Moonlit
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
