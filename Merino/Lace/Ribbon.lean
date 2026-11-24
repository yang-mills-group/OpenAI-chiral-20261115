import Merino.Lace.Train
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Lace
open Garter Regis.Circuit CF.Lat
open Stationary (Gaia)
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}
open Tree Filter Precision Next.Rank.Spindle Pressure ProbabilityTheory
open Gleam Next.SectorChange Next.SectorChange.Gaussian
open Etch -- (includes river)
open StepIn
variable {c:Side}{r:Ratio c n}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β:ℝ}{A:Support c}{N:Finset (Cell n)}{Z:PathData G}

variable (B:Z.Bounds q η C S)(P:Attached H Z)
local notation "wE"=>stamen B P n
local notation "χ"=>stdGaussian wE
local notation "J"=>Husk G n

open Ember Onyx Brecht

abbrev matinee (n:Side)(t:ℕ):StepIn n:= ⟨1,wrap n (noon t)⟩
abbrev soiree (n:Side)(t:ℕ):StepIn n:= ⟨Signed.mirror pole,- wrap n (noon t)⟩
abbrev showtime(n:Side)(t:ℕ):Duo n:=(matinee n t,soiree n t)
/-- Trivial room condition for rail rays (extremely loose eventually w^100). -/
def Reach(t m:ℕ):Prop:=(2*m+4:ℝ)^2≤ miles t


lemma morient(i:PlaqAxes):orient 1 i=1:=by
 simp [orient,i.property.not_gt,turnb]
lemma tplaq(i:Face (Per n))(t:ℕ):
 ((matinee n t).sent i).2=i.2 ∧ ((soiree n t).sent i).2=i.2 :=by
 have g:=i.2.property
 constructor <;>
   simp [sent,matinee,soiree,Signed.mirror,Face.send,PlaqAxes.rotate,
       PlaqAxes.ordered,min_eq_left g.le,max_eq_right g.le]


lemma midLag{t m:ℕ}(u:Reach t m)(i j:Face (Per n))
   (e:separation 0 i.1≤ m)(f:separation 0 j.1≤ m):
   let a:=(matinee n t).sent i
   let b:=(soiree n t).sent j
   ∃ z, Raill t z ∧ a.1-b.1=wrap n z:=by
 intro a b
 let x:=wrap n (noon t)
 let y:=a.1-b.1-wrap n (noon t+noon t)
 have r:pdist y ≤ 2*m+4:=by
    rw [show y=(a.1-x)+(-x-b.1) from by unfold y x;rw [map_add];abel]
    apply (pdist_triangle ..).trans
    have w:pdist (a.1-x)≤ m+2:=by
       rw [←separation,separation_comm]
       exact ((matinee n t).toll i).trans (Nat.add_le_add e le_rfl)
    have d:pdist (-x-b.1)≤ m+2:= ((soiree n t).toll j).trans (Nat.add_le_add f le_rfl)
    omega
 refine ⟨lift y+(noon t+noon t),?_,by rw [map_add,wrap_lift]; exact (sub_add_cancel ..).symm⟩
 intro k₀; rw [add_sub_cancel_right]
 have a₀:(lift y k₀).natAbs ≤ 2*m+4:=(Finset.le_sup (f:=fun a=>(lift y a).natAbs) (mem_univ k₀)).trans r
 apply le_trans _ u


 rw [← sq_abs]
 apply pow_le_pow_left₀ (abs_nonneg _) 
 exact_mod_cast (show |lift y k₀|≤ ((2*m+4:ℕ):ℤ) by apply abs_le.mpr; omega)

lemma spectralPay(i j:J):
 (↑(orient (Signed.mirror pole) j.1.2*sch (G:=G) i.2 j.2)* specter i.1.2 j.1.2 ray)=
 ↑(receiptVal armPay i j):=by
 rw [mul_comm _ (sch ..),Complex.ofReal_mul,mul_assoc,ray3,←Complex.ofReal_mul]
 simp [receiptVal,sch,ridge]
 split_ifs<;>grind
#check rimflare


lemma kissing {m t : ℕ}{e:ℝ}(e0:0 < e)(h: Reach t m)
 (y:Even n.val)(hw:0<w)(d:H.covered w v)(f:Floor H q n δ v)
 (r: ∀ a b z,Raill t z→ dist (sunLag a b H t z n) (specter a b ray) ≤ e):
   Kiss B P (showtime n t) armPay (miles t) e m :=by
 intro i j n₁ n₂
 obtain ⟨z,u,a⟩:=midLag h i.1 j.1 n₁ n₂
 have b :=tossed B P f d hw y (matinee n t) (soiree n t) i j
 rw [dartAt,dartAt,(tplaq _ _).1,(tplaq _ _).2,rimflare n H _ _ z a] at b
 let β:=orient (Signed.mirror pole) j.1.2*sch (G:=G) i.2 j.2
 rw [show (matinee n t).cost i.1=1 from morient _,one_mul] at b
 have t0: (↑(miles t ^4*crossing B P (showtime n t) i j):ℂ)=
    (β:ℂ)*sunLag i.1.2 j.1.2 H t z n:=by
    rw [Complex.ofReal_mul,b]
    unfold sunLag magnify
    rw [rimflare _ _ _ _ z (sub_zero _)]
    push_cast


    rw [mul_left_comm]
    rw [←Complex.ofReal_mul]
 have ab:‖(β:ℂ)‖≤1:=by
   rw [Complex.norm_real,Real.norm_eq_abs,show β=_ from rfl,abs_mul,orient_abs,one_mul]
   simp [sch];split<;>norm_num
 rw [←Real.norm_eq_abs, ←Complex.norm_real, Complex.ofReal_sub,t0,←spectralPay, ← mul_sub,norm_mul]
 exact (mul_le_mul ab ((dist_eq_norm ..).symm.trans_le (r _ _ _ u)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end YM.CF.Merino.Lace
