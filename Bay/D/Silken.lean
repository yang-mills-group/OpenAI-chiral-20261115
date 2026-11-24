import Bay.D.Mallow
import Bay.D.Skiff
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Papal
open Vale clocks
open YM.CF.Pannier.Chancel Journey Tower Tower.SlabMark VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal

abbrev inletO:Cover:= -1
lemma inlet_id(i:Axis):inletO i= -1:=rfl
lemma inlet_at (b:ℕ): inletO ∈ Band inletO b:= (pav_v ..).mpr fun i=>by omega
lemma inlet_width{b:ℕ}{x:Cover}(v:x∈Band inletO b)(j:Axis):
   -((b:ℤ)+14)≤x j ∧ x j ≤ (b:ℤ)+14 := by
 have w:=(pav_v _ _ _).mp v j;rw[inlet_id] at w;omega
lemma inlet_small(M:Side):pdist (wrap M inletO)≤3:= Work.E01.pdist_wrap_le
   (box_test.mpr ⟨fun i=>show -(3:ℤ)≤(-1) from by norm_num,fun i=>show (-1:ℤ)≤3 from by norm_num⟩)

variable {K:Calibration} {b d:ℕ}

/-- d counts whole tick translations from origin; x+ is distance in gauge lattice steps. -/
def rightD(K:Calibration)(d:ℕ):ℕ:= taps K*d
def wholeD(K:Calibration)(d:ℕ):ℕ:=2 * rightD K d
local notation "u₊"=>rightD K d
local notation "uₜ"=>wholeD K d
local notation "SΩ"=>Band inletO b
abbrev Cowl(K:Calibration)(b d:ℕ):= K.ℓ+b+14≤rightD K d
lemma ruler_cast (K:Calibration): ruler K.B = taps K:=by simp [ruler,taps]
lemma right_cast(K:Calibration)(d:ℕ):ruler K.B*d=rightD K d:=by simp[ruler_cast,rightD]

lemma plow_edge (a:ℤ){x:Cover}
 (h:x∈plow K 3 a SΩ)(j:Axis):
   let t:=if j=(3:Axis) then ruler K.B*a else (0:ℤ);
   -((b:ℤ)+14)+t≤x j∧x j≤ (b:ℤ)+14+t:=by
 obtain ⟨w,v,rfl⟩:=plow_stays K _ _ _ h
 dsimp only;rw[moves]
 have hx:=inlet_width v j
 split_ifs <;> omega

lemma paint_edge{y:Cover} (h:y∈ Lake.paint K SΩ d) (j:Axis):
  if j=(3:Axis) then -((b:ℤ)+14)-(u₊:ℤ) ≤y j∧ y j≤b+14+(u₊:ℤ)
   else -((b:ℤ)+14) ≤y j ∧ y j ≤(b:ℤ)+14:=by
 rcases mem_union.mp h with a|a
 · obtain ⟨v,hv,rfl⟩:=mem_image.mp a
   rw[fling_move]
   have:=plow_edge _ hv j; rw[right_cast] at this
   by_cases p:j=3
   · simp only [p,if_true] at *;omega
   simp only [if_neg p,if_neg (Ne.symm p)] at *;omega
 have :=plow_edge _ a j; rw[right_cast] at this
 dsimp only at this
 by_cases h:j=3 <;> simp only [h,if_false,if_true] at * <;> omega

lemma sits_right (p:Cowl K b d):region 3 0 K.ℓ (plow K 3 d SΩ):=by
 intro y v
 have := plow_edge _ v 3; rw[right_cast] at this; simp only[if_true] at this
 unfold Cowl at p;omega

lemma sits_both (p:Cowl K b d): Feeling K 3 (4*d) (4*u₊)
    (plow K 3 (2*(d:ℤ)) (Lake.paint K SΩ d)):=by
 unfold Cowl at p
 refine ⟨?_,fun _=>-((b:ℤ)+14),?_⟩
 · intro y h;obtain ⟨v,w,rfl⟩:=plow_stays K _ _ _ h
   have := paint_edge w 3
   have g(a):ruler K.B*(a*(d:ℤ))=a*(u₊:ℤ):=by rw[mul_left_comm,right_cast]
   rw[moves,if_pos rfl,g,Nat.cast_mul,g]
   simp only [if_true] at this;omega
 intro j l y h; obtain ⟨v,w,rfl⟩:=plow_stays K _ _ _ h
 rw[moves,if_neg l]
 have :=paint_edge w j; rw[if_neg l] at this;dsimp only
 omega

lemma cowlled {P:VacuumSelection.Spine}{s:ℕ}
 (p:Cowl P.calibration b d)
 (q: 4*(rightD P.calibration d :ℝ) ≤ atRate 12 (scale P s))
 (v:Able P.calibration (scale P s)):
 Noria P s (plow P.calibration 3 (2*(d:ℤ)) (Lake.paint P.calibration SΩ d)):=by
 refine ⟨v,4*d,4*rightD _ d,sits_both p,?_ ,?_⟩
 · rw[rightD,mul_left_comm]
 push_cast;exact q

variable {N:Side}
abbrev startL(N:Side):Seat N:= wrap (More N) inletO
abbrev prepL(K:Calibration)(N:Side)(d:ℕ):Seat N:=Lake.jumper K N d
abbrev tailL(K:Calibration)(N:Side)(d:ℕ):Seat N:=coup.act (prepL K N d)
local notation "Gℓ"=>prepL K N d
local notation "Hℓ"=>tailL K N d
local notation "pℓ"=>startL N
local notation "qℓ"=> ((u₊:ℤ) • step 3:Cover)

lemma turnL(y:Cover):
  coup.act (wrap (More N) y)=wrap (More N) ((plane 3 0).motion y):=by
 rw [←Shape.anno]
 simp only [Shape.anon,plane,zero_smul,smul_zero,map_zero,affine,add_zero,coup]
lemma lead:Gℓ= wrap (More N) qℓ:=by
 unfold prepL Lake.jumper;rw[right_cast]
lemma lineSplit:Gℓ-Hℓ=wrap (More N) (spireAxis uₜ):=by
 unfold tailL
 rw [lead,turnL,←map_sub]
 apply congrArg
 have l : (plane 3 0).motion qℓ = -qℓ:=by
    ext i;rw [fling_move]
    simp only[Pi.neg_apply, Pi.smul_apply, step_apply, smul_eq_mul]
    split_ifs <;> simp_all
 rw [l,sub_neg_eq_add]
 unfold wholeD spireAxis;rw[two_mul,add_smul];simp

lemma placed:
  (forward Gℓ).rise pℓ ∈Kspan N (Lake.paint K SΩ d) ∧
  (after Hℓ).rise pℓ ∈Kspan N (Lake.paint K SΩ d):=by
 have he:ruler K.B*d=rightD K d:=right_cast ..
 have v :2*gaugeT K d = (u₊:ℤ):=by rw [←he]; unfold ruler gaugeT Heat.gaugeShift;ring
 have l : inletO+ qℓ∈plow K 3 d SΩ:=by
    rw [←v];exact mem_image_of_mem _ (inlet_at b)
 let U:=inletO + qℓ
 constructor
 · have w:U∈Lake.paint K SΩ d:=mem_union_right _ l
   have u:= mem_image_of_mem (wrap (More N)) w
   rw [show (forward Gℓ).rise pℓ =wrap (More N) U from ?_]
   · exact u
   unfold Kite.rise affine forward; dsimp only
   rw [Signed.act_one,lead]
   unfold U;rw [map_add]
 have w:(plane 3 0).motion U∈Lake.paint K SΩ d:=mem_union_left _ (mem_image_of_mem _ l)
 have u:=mem_image_of_mem (wrap (More N)) w
 change _∈ Kspan _ _ at u
 rw [←turnL] at u
 change coup.act pℓ +coup.act Gℓ ∈_
 rw [←Signed.act_add,lead]
 exact (map_add (wrap (More N)) inletO qℓ) ▸ u

def Remote (K: Calibration)(m k d:ℕ):Prop:=
   (2*((k:ℝ)+12))*meander m≤wholeD K d
def VeryFine (N:Side)(K:Calibration)(m d:ℕ):Prop:=
   wholeD K d* Ember.pinch (More N) ≤ (meander m)⁻¹
lemma lineBore {m k:ℕ}
   (p:Remote K m k d)(q:VeryFine N K m d):
   Bore (More N) m k uₜ pℓ Gℓ Hℓ:=⟨inlet_small _,lineSplit,p,q⟩

lemma fencesF {α:ℕ→Side} (g:Tendsto (fun i=>(More (α i)).val) atTop atTop)
  (K:Calibration)(d m:ℕ):
  ∀ᶠ i in atTop,VeryFine (α i) K m d:=by
 have ht: Tendsto (fun i=>(wholeD K d:ℝ)*Ember.pinch (More (α i))) atTop (𝓝 0):=
    (mul_zero _).subst (motive:=fun t=> Tendsto _ _ (𝓝 t)) 
        (((tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp g))).const_mul _)
 exact ht.eventually (ge_mem_nhds (inv_pos.mpr (meander₀ m)))

end YM.CF.Bay.D
