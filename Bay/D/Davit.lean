import Bay.D.Oboe
import YM.SU5.Circuit.Lieble
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
open Resonance Brecht Circuit

variable {n:Side}
abbrev coup := Signed.mirror 3
abbrev orient (F:PlaqAxes):ℝ:=if F.1.2=3 then -1 else 1
def rudder(F:PlaqAxes):Cover:=if F.1.2=3 then -step 3 else 0
abbrev abaft(x:Site n)(F:PlaqAxes):=coup.act x + wrap n (rudder F)
variable (y : Head.Dir T4 n)
lemma davit_link(x:Site n)(i:Axis):
    collect T4 (dusk coup y) (x,i)=
      if i=3 then (-collect T4 y (coup.act x - step i,i)) else collect T4 y (coup.act x,i):=by
 unfold collect;change Bid.pulled y coup _=_
 simp only [Bid.pulled, show axisEquiv.symm (coord i)=i from Equiv.symm_apply_apply .., affine, add_zero]
 fin_cases i <;> rfl
lemma hit(i:Axis): coup.act (step i : Site n)= if i=3 then -step i else step i:=by
 ext j
 fin_cases i <;> fin_cases j <;> simp[coup,Signed.act,Signed.mirror,step]

lemma davit_face(x:Site n)(F:PlaqAxes):faceCurl (x,F) (dusk coup y)=
 orient F • faceCurl (abaft x F,F) y:=by
 simp only [faceCurl,←fundamental, AnalyticBridge.VerifiedReset.Square.cochain_square, davit_link, Signed.act_add,hit]
 have ha:F.val.1 ≠ 3:=by
   exact (show ∀F:PlaqAxes,F.val.1≠3 from by decide) F
 simp only [ha, if_false, orient, abaft,rudder]
 by_cases h:F.1.2=3
 · let c:=coup.act x
   let i:=F.val.1
   simp only[h, if_true,_root_.map_neg,wrap_step]
   rw[show c+step i-step 3=(c+ -step 3+step i:Site n) from by abel,
       show c + -step 3 +step 3=c from by abel,sub_eq_add_neg, neg_smul,one_smul]
   simp only[c,i] -- align
   abel
 simp[h] 

def forward(b:Site n):Kite n:=⟨1,b⟩
def after(b:Site n):Kite n:=⟨coup,b⟩
lemma davit_port(b:Site n)(i:Cella n):
   brine ((forward b).sail y) i=
   faceCurl (i.1+b,i.2.1) y i.2.2:=by
 trans brine (arbor b y) i
 · apply brine_eq; intro t;rw[Kite.sail,bank_at,arbor_at];rfl
 exact congrArg (· i.2.2) (face_drift b y i.2.1 i.1)
lemma davit_bow(b:Site n)(i:Cella n):
 brine ((after b).sail y) i=orient i.2.1* faceCurl (abaft i.1 i.2.1+b,i.2.1) y i.2.2:=by
 change faceCurl (_,_) (dusk coup (arbor b y)) i.2.2=_
 rw [davit_face,face_drift];rfl

section
variable {q:Clip}{H:Bed}{Z:PathData T4}{η f j:ℝ}(B:Z.Bounds q η f j)(P:Attached H Z)
local notation "Φ"=> stamen B P n
variable (b:Site n)(ρ:ℝ)
def south (i:Cella n): Φ:=plar B P (i.1+b, plaquette i.2.1) ρ i.2.2
def north (i:Cella n): Φ:= orient i.2.1 • plar B P (abaft i.1 i.2.1+b,plaquette i.2.1) ρ i.2.2
def rivax(q:Clip):ℝ:=2*(Real.sqrt q.direct)⁻¹
lemma south_norm (t:|ρ|≤2)(i:Cella n):
 ‖south B P b ρ i‖≤rivax q:=mintBudget _ _ _ _ t
lemma nor_sign(F:PlaqAxes):|orient F|=1:=by unfold orient;split <;>norm_num
lemma north_norm (t:|ρ|≤2)(i:Cella n):‖north B P b ρ i‖≤rivax q:=by
 rw[north,norm_smul,Real.norm_eq_abs,nor_sign,one_mul]
 exact mintBudget _ _ _ _ t
lemma south_val(x:Φ)(i:Cella n):
 delta q ρ (forward b) x i=spanX (south B P b ρ i) x:=by
 obtain ⟨y,rfl⟩:= (tiler B P).surjective_rangeRestrict x
 unfold south plar spanX
 erw [real_inner_smul_left (F:=Φ),joy,inspire]
 change ρ*sea q _ (tiler B P y) _=_ -- rhs?
 erw[at_sea,davit_port,river_now]

lemma north_val(x:Φ)(i:Cella n):
 delta q ρ (after b) x i=spanX (north B P b ρ i) x:=by
 obtain ⟨y,rfl⟩:= (tiler B P).surjective_rangeRestrict x
 unfold north plar spanX
 erw [real_inner_smul_left (F:=Φ),real_inner_smul_left (F:=Φ),joy,inspire]
 change ρ*sea q _ (tiler B P y) _=_
 erw[at_sea,davit_bow,river_now]
 ring

lemma south_quay(x:Φ)(K:ℝ)(A:Icey (Cella n)):
 quay q ρ K A (forward b) x=scrip K A (south B P b ρ) x:=by
 exact congrArg (splash A) (funext fun i=>congrArg (pur K) (south_val B P b ρ x i))
lemma north_quay(x:Φ)(K:ℝ)(A:Icey (Cella n)):
 star (quay q ρ K A (after b) x)=scrip K (creamM A) (north B P b ρ) x:=by
 rw[scrip_cream]
 exact congrArg star (congrArg (splash A) (funext fun i=>congrArg (pur K) (north_val B P b ρ x i)))

variable (b':Site n){D v w:ℝ}
/-- entrywise paid at arbitrary x poses. -/
lemma hash_price (i j:Cella n)(L:Floor H q n D v)
 (he: H.covered w v)(e:0<w)(t:Even n.val):
 hashes (south B P b ρ) (north B P b' ρ) i j =
    (ρ:ℂ)^2 * (sch (G:=T4) i.2.2 j.2.2) * (orient j.2.1) *
    rimble n H (i.1+b,plaquette i.2.1) (abaft j.1 j.2.1+b',plaquette j.2.1):=by
 have h:=chimes B P L he e i.2.2 j.2.2 (i.1+b,plaquette i.2.1) (abaft j.1 j.2.1+b',plaquette j.2.1) t
 simp_rw[←joy,appraisal] at h
 change (↑(inner ℝ (ρ • trill B P i.2.2 _) (orient _ • (ρ• trill B P j.2.2 _))):ℂ)=_
 erw[real_inner_smul_left (F:=Φ),real_inner_smul_right (F:=Φ),real_inner_smul_right (F:=Φ)]
 push_cast;rw[h];ring

end
end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.hash_price
