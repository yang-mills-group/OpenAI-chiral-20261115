import ForceSatin.Cygnet
import ForceSatin.Falcon
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
-- Mark quilting, torus expression at any period (incl mask coiling)
open Lifted Afterglow Satin Cygnet Loaves
abbrev MaskShape:= ℝ × Finset Cover
abbrev HorizonLens := Face ℤ × SU.group.ColorIndex
structure HorizonCab where
 step : Rail
 root : Cover
 walk : Lattice.Walk
structure Horizon where
 song : List Bite
 face : List HorizonLens
 cabin : List HorizonCab
 mask : List MaskShape
-- use true ANY finite Support, wraps may collapse but AP care
namespace Horizons
noncomputable def DirN (N:Side) (i: HorizonLens): LensGauge N:= ((wrap (More N) i.1.1,i.1.2),i.2)
noncomputable def MaskN (N:Side)(i:MaskShape) : ℝ × Support (More N):=(i.1,Satin.region i.2 N)
noncomputable def CabN (N:Side)(i:HorizonCab): CablePrice N:= ⟨i.step,wrap (More N) i.root,i.walk⟩
noncomputable def Glass (N:Side)(A:Horizon) : Goblet N:=⟨chartP N A.song, A.face.map (DirN N), A.cabin.map (CabN N), A.mask.map (MaskN N)⟩
variable (N:Side)
abbrev FaceN (N:Side)(i:Face ℤ):Face (Per (More N)):= (wrap (More N) i.1,i.2)
abbrev toeL (i:Face ℤ): Finset Cover:= (visits i.1 (square i.2.val.1 i.2.val.2)).toFinset
lemma visitsM (L:Walk)(i:Cover): visits (wrap (More N) i) L=(visits i L).map (wrap (More N)):=by induction L generalizing i with| nil=>rfl| cons x L h=> rw [visits,visits,List.map_cons,←h (i+x.vec)]; simp [wrap_vec] -- reorder
lemma toeTurn (p:PlaqAxes)(x y:Cover): toeL (x+y,p)=(toeL (x,p)).image (fun j=> j+y):=by unfold toeL; simp_rw [square_corners]; ext i; simp [add_right_comm x y,add_right_comm (x+ step p.val.1) y]
lemma toeN (i:Face ℤ): touched (FaceN N i)=(toeL i).image (wrap (More N)):=by unfold FaceN touched toeL; simp only [square_corners]; ext; simp
lemma faceValueN(i:Face ℤ)(U:Pane N): faceValue (Lifted.onC N U) i=faceValue U (FaceN N i):=by unfold Lifted.onC FaceN faceValue; rw [travel_at,add_zero]
def pingC (S:MaskShape)(U:LinksC):Prop:= ∀ i:Face ℤ, ¬Disjoint S.2 (toeL i) → SU.group.chord (faceValue U i)<S.1
lemma pingN(i:MaskShape)(U:Pane N): pingC i (Lifted.onC N U) ↔ pingS (MaskN N i).1 (MaskN N i).2 U:=by
 let s:= wrap (More N)
 constructor
 · intro h x v
   obtain ⟨y,p,t⟩:= Finset.not_disjoint_iff.mp v; obtain ⟨j,t',rfl⟩:= mem_image.mp p; let z:Face ℤ:=(Lattice.lift x.1,x.2); have he:FaceN N z=x:=by simp [FaceN,z]
   rw [←he,toeN] at t; obtain ⟨u,h0,k⟩:=mem_image.mp t; let V:Face ℤ:=(z.1+(j-u),z.2); have hh: FaceN N V=x:=by rw [←he]; unfold V FaceN; congr 1; rw [map_add,map_sub,k,sub_self,add_zero]
   rw [←hh,←faceValueN]; apply h; refine not_disjoint_iff.mpr ⟨_,t',?_⟩; unfold V; rw [toeTurn]; exact mem_image.mpr ⟨_,h0,(by abel)⟩
 intro p x h; obtain ⟨i,b',v⟩:= not_disjoint_iff.mp h; rw [faceValueN]; apply p; refine not_disjoint_iff.mpr ⟨s i,mem_image_of_mem _ b',?_⟩; rw [toeN]; exact mem_image_of_mem _ v
lemma pingMeas (p:MaskShape):MeasurableSet {x:LinksC|pingC p x}:=by
 unfold pingC; simp_rw [Set.setOf_forall]; apply MeasurableSet.iInter; intro i; apply MeasurableSet.iInter; intro _; exact (isOpen_lt (SU.group.continuous_chord.comp (Cube.travel_cont ..)) continuous_const).measurableSet
variable {N}
variable {K:Calibration}{i j:ℕ}{S:Finset Cover}
lemma ping_ag (p:MaskShape)(U V:LinksC)(a: Agrees (↑S) U V) (h:∀ i:Face ℤ, ¬Disjoint p.2 (toeL i)→ toeL i⊆ S): pingC p U ↔ pingC p V:=by
 have he(i:Face ℤ)(t:¬Disjoint p.2 (toeL i)): faceValue U i=faceValue V i:= travel_local i.1 _ U V (fun i v w=> a i (h _ t (List.mem_toFinset.mpr v)) (h _ t (List.mem_toFinset.mpr w)))
 exact ⟨fun h i p=>by rw [←he i p]; exact h i p,fun h i p=>by rw [he i p]; exact h i p⟩
-- padding lemma on integer∞ for any Support. all in liner 2. Then support measure CH.
private lemma stepC_go (q:Face ℤ)(v:Cover)(h:v∈toeL q): v-q.1∈ Lattice.box 2:=by
 rcases q with ⟨x,i⟩
 simp only [toeL,square_corners,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h -- pair .1 maybe needs DS
 rcases h with rfl|rfl|rfl|rfl|rfl -- `x ∈...` etc
 all_goals rw [box_test]; constructor<;> intro j
 all_goals simp only [Pi.add_apply,Pi.sub_apply,Nat.cast_ofNat,step_apply] -- tune
 all_goals (try split_ifs) <;> omega
lemma toe_in (q:Face ℤ)(h:¬Disjoint S (toeL q)): toeL q⊆ Satin.liner S 4:=by
 obtain ⟨x,p,t⟩:= not_disjoint_iff.mp h; intro i g; apply mem_biUnion.mpr; refine ⟨x,p,mem_image.mpr ⟨i-x,?_,sub_add_cancel _ _⟩⟩
 have he:= box_test.mp (stepC_go q x t); have hv:=box_test.mp (stepC_go q i g); rw [box_test]; constructor <;> intro j <;> (obtain ⟨hp,hw⟩:= he; obtain ⟨h,t⟩:=hv; specialize hp j; specialize hw j; specialize h j; specialize t j; simp only [Pi.sub_apply] at *; omega)
abbrev colorC (i:HorizonLens)(U:LinksC) (u:ℝ):ℝ:= u* SU.group.curvature (faceValue U i.1) i.2
def carNC (i:HorizonCab)(U:LinksC):= Rail.cost (travel U i.root i.walk) i.step
def bakedC (L:Horizon)(U:LinksC)(y:ℝ):ℂ:= (L.cabin.map (fun i=>carNC i U)).prod * ((L.face.map (fun i=>colorC i U y)).prod:ℝ)
noncomputable def bakeFlag (L:Horizon)(U:LinksC)(y:ℝ):ℂ:= if ∀ i∈L.mask,pingC i U then bakedC L U y else 0
def bright (i:Bite):Prop:= (i.hand=false ↔ i.spin ∈plusHalf)
abbrev plotN (K:Calibration)(V:List Bite): Buffered.Family K:=fun n _=> chartP (K.c n) V
lemma qualifies (i:Bite) (h:bright i) (v:nodeC i.root∈S): InTest K true S true (plotN K [i]):=by
 cases x:i.hand
 · apply (show plotN K [i]=creation K i.root i.spin i.cost from ?_) ▸ InTest.creator (K:=K) i.cost (h.mp x) v -- direction
   funext n U; simp [plotN,chartP,vix,x]; rfl
 apply (show plotN K [i]=removal K i.root i.spin i.cost from ?_) ▸ InTest.remover (K:=K) i.cost (fun p=>by rw [h.mpr p] at x; contradiction) v
 funext n U; simp [plotN,chartP,vix,x]; rfl
def hex : List Bite→Bool | []=>false|_::Taℓ=>Bool.xor true (hex Taℓ)
lemma plot_cons (i:Bite)(L:List Bite): plotN K (i::L)=plotN K [i]* plotN K L:= by ext n U; simp [plotN,chartP]
lemma plot_qualified (L:List Bite)(h:∀ i∈L, bright i∧ nodeC i.root ∈ S): InTest K true S (hex L) (plotN K L):=by induction L with
 | nil=> exact InTest.one
 | cons i L ih=> rw [plot_cons]; apply InTest.mul (qualifies _ (h _ List.mem_cons_self).1 (h _ List.mem_cons_self).2) (ih fun i t=>h i (List.mem_cons_of_mem _ t))
variable (A:Horizon)
structure LoPrice (A:Horizon)(t x:ℝ)(S:Finset Cover)(m:ℕ):Prop where
 plot : ∀ i∈ A.song,nodeC i.root∈S ∧ bright i
 even_ : hex A.song=false
 spin : A.song.length ≤ m
 face : A.face.length ≤ m
 cabin : A.cabin.length ≤ m
 on_lens : ∀ i∈ A.face, Satin.liner {i.1.1} (colorCash SU.group) ⊆ S ∧ toeL i.1 ⊆ S
 stool : ∀ i∈ A.cabin,(visits i.root i.walk).toFinset⊆ S ∧ (i.walk.length:ℝ) ≤ voucher x
 mark : ∀ i∈ A.mask,i.2 ⊆ S ∧ t*temp x ≤ i.1 ∧ (∀ F:Face ℤ,¬Disjoint i.2 (toeL F) → toeL F⊆ S)
 eyes : ∀ i∈ A.face,∃ p∈ A.mask,i.1.1∈p.2 ∧ p.1≤ temp x
noncomputable abbrev softP (y:ℝ)(A:Horizon)(x:PairsC) := bakeFlag A x.1 y
noncomputable def Frost (y:ℝ)(K:Calibration)(A:Horizon):Buffered.Family K:= scalar K (softP y A) * plotN K A.song
namespace LoPrice
variable {x t y:ℝ} {A:Horizon} {m:ℕ}(v:LoPrice A t x S m)
include v
lemma form : Coeff true S (softP y A):=by
 let f:=fun x=> bakedC A x y; have he:Continuous f:=by
    have hh(W:List HorizonCab): Continuous (fun U:LinksC=>(W.map (fun i=>carNC i U)).prod):=by induction W with|nil=>exact continuous_const|cons i W ih=> exact ((Rail.regular ..).comp (Cube.travel_cont ..)).mul ih
    have hp(W:List HorizonLens): Continuous (fun U:LinksC=>(W.map (fun i=> colorC i U y)).prod):=by induction W with
     | nil=> exact continuous_const
     | cons i W ih=> exact (Continuous.mul (continuous_const.mul ((EuclideanSpace.proj _).continuous.comp (SU.group.continuous_curvature.comp (Cube.travel_cont ..)))) ih)
    exact (hh _).mul (Complex.continuous_ofReal.comp (hp _))
 let Z:LinksC→Prop:=fun U=>∀ i∈A.mask,pingC i U
 have hg:MeasurableSet {x|Z x}:=by rw [show {x|Z x}= ⋂ i∈ A.mask.toFinset,{U|pingC i U} from (by ext; simp [Z])]; exact MeasurableSet.biInter (A.mask.toFinset.countable_toSet) (fun i _=>pingMeas i)
 refine ⟨fun g=>by contradiction, (show Envelope (softP y A) from (?s : Envelope (fun b:PairsC=> if Z b.1 then f b.1 else 0))),?_⟩
 case s=>
    refine Env.along (F:=fun x=> if Z x then f x else 0) ?_ measurable_fst; obtain ⟨b,h⟩:=(Env.compact he).cost; refine ⟨(he.measurable.ite hg measurable_const), max b 0,fun x=>?_⟩; split; exact (h _).trans (le_max_left ..); exact norm_zero.trans_le (le_max_right ..)
 intro a b k _; have hv(Z:Finset Cover)(p:Z⊆S)(L:Walk)(x:Cover)(e:(visits x L).toFinset⊆ Z): travel a.1 x L=travel b.1 x L:= travel_local _ _ a.1 b.1 (fun i a b=>k i (p (e (List.mem_toFinset.mpr a))) (p (e (List.mem_toFinset.mpr b))))
 have hh: Z a.1 ↔ Z b.1:=⟨fun p i t=> (ping_ag i _ _ k (v.mark i t).2.2).1 (p i t),fun p i t=> (ping_ag i _ _ k (v.mark i t).2.2).2 (p i t)⟩
 by_cases h:Z a.1
 · unfold softP bakeFlag; rw [if_pos h,if_pos (hh.mp h)]; apply congrArg₂ (fun a (b:ℝ)=> a*(b:ℂ)) (congrArg List.prod (List.map_congr_left (fun i g=>?_))) (congrArg List.prod (List.map_congr_left (fun i g=>?_)))
   · exact congrArg (fun x=> Rail.cost x i.step) (hv S (Finset.Subset.refl _) _ _ (v.stool i g).1)
   exact congrArg (fun x=> y* (SU.group.curvature x i.2)) (hv S (Finset.Subset.refl _) _ _ (v.on_lens i g).2)
 unfold softP bakeFlag; rw [if_neg h,if_neg (hh.mpr.mt h)]
lemma eligible (y:ℝ)(K:Calibration): InTest K true S false (Frost y K A):=by
 unfold Frost; refine InTest.mul (c:=false) (.seed v.form) ?_; rw [←v.even_]; exact plot_qualified _ (fun i a=> and_comm.mp (v.plot i a)) -- InTest.seed
omit v
lemma physical (A:Horizon) (y:ℝ)(i:Side): Frost y K A i= toMark (craft (Glass (K.c i) A) y):=by
 let N:= K.c i; funext U; let V:=U.1; let W:=Lifted.onC N V; let Y:=Glass N A; let X:=chartP N A.song
 have hp:onGlow Y V ↔ ∀ i∈A.mask,pingC i W:=⟨fun h i t=> (pingN N i _).2 (h _ (List.mem_map.mpr ⟨_,t,rfl⟩)),fun h i t=> by obtain ⟨b,pb,rfl⟩:= List.mem_map.mp t; exact (pingN N b _).1 (h b pb)⟩
 have hh: carG Y V* (glare Y V y:ℂ)= bakedC A W y:=by
    unfold bakedC; apply congrArg₂ (fun a (b:ℝ)=>a*(b:ℂ))
    · unfold carG Y Glass SatinForce.cadence; rw [List.map_map]; apply congrArg List.prod; apply List.map_congr_left; intro i _; apply congrArg (fun x=>Rail.cost x i.step); symm; unfold W Lifted.onC; rw [travel_at,add_zero]; rfl
    unfold glare Y Glass; rw [List.map_map]; apply congrArg List.prod; apply List.map_congr_left; intro i _; exact congrArg (fun x=> y*SU.group.curvature x i.2) (faceValueN N i.1 V).symm
 change (bakeFlag A W y • 1)*X= craft Y y V; by_cases g:onGlow Y V; · rw [bakeFlag,craft,if_pos (hp.mp g),if_pos g,Algebra.smul_mul_assoc,one_mul,hh]; rfl
 rw [bakeFlag,craft,if_neg g,if_neg (hp.mpr.mt g),zero_smul,zero_mul]
include v
lemma scaled (N:Side): Scaled (Glass N A) (Satin.region S N) m t x:=by
 let U:=Satin.region S N; refine ⟨?_, (by rw [Glass,List.length_map]; exact v.face),(by rw [Glass,List.length_map]; exact v.cabin),?_,?_,?_,?_⟩
 · let f(i:Bite):=nodeC i.root; have he(i:Bite)(b:f i∈S):Street U 1 1 (vix N i):=by
     rw [←i.normP N]; apply Street.leg i.hand (wrap (More N) (f i)) (mem_image_of_mem _ b) _ (_ : withinM _ _); have e:Satin.region {f i} N = {wrap (More N) (f i)}:= Finset.image_singleton ..; rw [←e]; exact (i.pace N (mem_singleton_self _))
   have ht(l:List Bite)(e:∀ i∈l, f i∈S): Street U l.length 1 (chartP N l):=by induction l with
     | nil=>exact Street.one
     | cons i l ih=> rw [chartP,List.map_cons,List.prod_cons,List.length_cons,Nat.add_comm,← show (1:ℝ)*1=1 from mul_one (1:ℝ)]; exact (he i (e i List.mem_cons_self)).mul (ih (fun i g=> e i (List.mem_cons_of_mem _ g)))
   exact Street.enlarge le_rfl v.spin (ht _ (fun i a=> (v.plot i a).1))
 · intro i p; obtain ⟨i,wℓ,rfl⟩:= List.mem_map.mp p; have hv:= linen_contains {i.1.1} (colorCash SU.group) N; apply Finset.Subset.trans (_ : _ ⊆ Satin.region _ N) (Finset.image_mono _ (v.on_lens i wℓ).1); rwa [Satin.region,image_singleton] at hv
 · intro i p; obtain ⟨i,wℓ,rfl⟩:=List.mem_map.mp p; refine ⟨?_,(v.stool i wℓ).2⟩; unfold SatinForce.quilt CabN; dsimp only; rw [visitsM]; intro x h; obtain ⟨x,h1,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp h); exact mem_image_of_mem _ ((v.stool i wℓ).1 (List.mem_toFinset.mpr h1))
 · intro i p; obtain ⟨i,wℓ,rfl⟩:= List.mem_map.mp p; exact ⟨Finset.image_mono _ (v.mark i wℓ).1,(v.mark i wℓ).2.1⟩
 intro i p; obtain ⟨i,wℓ,rfl⟩:= List.mem_map.mp p; obtain ⟨p,h,w,g⟩:=v.eyes i wℓ; exact ⟨MaskN N p,List.mem_map.mpr ⟨_,h,rfl⟩, mem_image_of_mem (wrap _) w,g⟩
#print axioms physical
#print axioms eligible
#print axioms scaled
end LoPrice
end Horizons
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
