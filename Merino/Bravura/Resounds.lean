import Merino.Tiara.Majesty
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Bravura
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open BProof Hive Swell Hem Merino.Mitre Plume
open Afterglow Tower Lifted Journey

open Tiara Py.Rate.LocalLimit Preparation Tower.VacuumSelection
open Medal Lace Cuff
open scoped InnerProductSpace
universe v w

open Garter Py Rive RG Papal

variable (P:Spine)(p:Bolts)(s i k:ℕ)(C:Constellation)
local notation "β"=> (LedgerM P s i k).beta
local notation "x"=> (scaleM P s)
local notation "π₀"=>leadCoin hueInk C.α
local notation "ℒ"=>compass P.run i k s
variable (f:Pane (RegNum P s i)→ℂ)(T:InkFace (RegNum P s i))


abbrev geyser : ℝ:=armPay^2*C.L^2
local notation "M"=>miles
local notation "Z"=>P.par.V.L
abbrev shade(t:ℕ):ℝ:= (ℒ (photo (staged t β f))).re
abbrev hush:ℝ:= (pour T (toss (P.par.V.L.mood (P.run.uv k-s)) (P.par.V.L.tied (P.run.uv k-s)) 1 1))^2
abbrev flow:ℝ:=armPay^2*pigment T

lemma spurt {t:ℕ}(h:Strut x t)(w: Cameo P.run P.large (k:=k) C.ε f T)
 (b:C.α<dripQ T (needle _) (needle _)) :
 let z:=(M t)^8*(shade P s i k f t-hush P s i k T)
 flow P s i T≤ z ∧ z ≤ 3*flow P s i T:=by
 have j:π₀≤flow P s i T:=mul_le_mul_of_nonneg_left
   (rich_pos T hueInk C.α C.oa b.le) (sq_nonneg _)
 obtain ⟨_,r,v,u⟩:=w h


 let μ:=chat P.run s i k T (showtime _ t)
 have m:0≤(M t)^8:=by positivity
 have l:=mul_le_mul_of_nonneg_left (neg_le_of_abs_le r) m
 have o:=(mul_le_mul_of_nonneg_left (le_of_abs_le r) m).trans v
 change _≤ M t ^8 * (shade P s i k f t-μ) at l
 change M t ^8 * (shade P s i k f t-μ) ≤ _ at o
 change |M t ^8 * (μ-hush P s i k T)- 2*flow P s i T|≤_ at u
 constructor <;>
   linarith only [j,C.small,l,v,o,neg_le_of_abs_le u, le_of_abs_le u]

lemma riseCost (e:laden T≤C.L):flow P s i T ≤ geyser C:=by
 refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
 have u:= (batches_abs e zero_le_one (fun i j k l=>receiptVal 1 i k *receiptVal 1 j l)
   (by intros; unfold receiptVal; split_ifs <;> simp) : |squareb T (receiptVal 1)| ≤ C.L^2 * 1)
 change |squareb T (receiptVal 1)|≤ C.L^2*1 at u
 rw [Lace.chroma] at u
 simpa using (le_of_abs_le u)

def Heard(C:Constellation)(u z w q:ℝ):Prop:=
   Ct C*u^2≤z-w∧
   (Ct C*u^2≤ z-2*w+q∧z-2*w+q≤24*geyser C*u^2)


-- numerical lemma for each difference cost (A ≥ c/2 or ≤6d); A raw times M⁸. 
lemma relay {t:ℕ}(h:Strut x t) (g:matchedX x β)(u:0<x)
    (i0 i1 i2:ℕ) (y z w:ℝ)
 (r:
   (π₀/2 ≤(M t)^8*(y*shade P s i k f i0 + z*shade P s i k f i1+w*shade P s i k f i2) ∧
   (M t)^8*(y*shade P s i k f i0+z*shade P s i k f i1+w*shade P s i k f i2)≤6*geyser C)) (c:ℝ):
 let S(n:ℕ):= (ℒ (photo (staged n c f))).re
 Ct C*(c/(x*M t ^4))^2 ≤ y*S i0+z*S i1+w*S i2 ∧
 y*S i0+z*S i1+w*S i2 ≤24* geyser C*(c/(x*M t^4))^2:=by
 let A(n:ℕ):=(ℒ (icon (polka 1 (showtime _ n) (false,true) f))).re
 let B:=y*A i0 +z*A i1+w*A i2
 have e(d:ℝ): let W(m):=(ℒ (photo (staged m d f))).re; y*W i0 +z*W i1+w*W i2=d^2 * B:=by
     dsimp only; rw [scale_read,scale_read,scale_read]; unfold B A;ring
 dsimp only; rw [e]


 unfold shade at r; rw [e] at r
 have D:0 < M t:=by
    have a:0<t:=(strut_d h).1
    unfold miles;positivity
 have L:0<x/2:=half_pos u
 have R:0<π₀:=Lace.shines _ _ C.oa
 have d:0<B:=by 
    have t':=(half_pos R).trans_le r.1
    rw [←mul_assoc] at t'
    exact pos_of_mul_pos_right t' (by positivity)
 have E:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ L.le g.1 2) d.le) (show 0≤(M t)^8 by positivity)
 have F:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (L.le.trans g.1) g.2 2) d.le) (show 0≤(M t)^8 by positivity)
 rw [div_pow]
 have q(W:ℝ): W*(c^2/(x*M t^4)^2)=c^2*(W/(x*M t^4)^2):=by ring
 rw [q,q]
 constructor
 · refine mul_le_mul_of_nonneg_left ((div_le_iff₀ (by positivity)).mpr ?_) (sq_nonneg _)
   unfold Ct
   linarith only [r.1.trans F]
 refine mul_le_mul_of_nonneg_left ((le_div_iff₀ (by positivity)).mpr ?_) (sq_nonneg _)
 linarith only [E.trans r.2]

lemma ripples {t:ℕ}(h:Strut x t)(h':Strut x (2*t))(h'':Strut x (3*t))
   (w: Cameo P.run P.large (k:=k) C.ε f T)
   (b:C.α<dripQ T (needle _) (needle _))
   (a:laden T≤C.L)(g:matchedX x β)(u:0<x)(c:ℝ):
   let l(v:ℕ):=(ℒ (photo (staged v c f))).re
   Heard C (c/(x*M t ^4)) (l t) (l (2*t)) (l (3*t)):=by
 have q:= spurt P s i k C f T h w b
 have q':= spurt P s i k C f T h' w b
 have q'':= spurt P s i k C f T h'' w b
 rw [show M (2*t)=2*M t by unfold miles;push_cast;ring] at q'
 rw [show M (3*t)=3*M t by unfold miles;push_cast;ring] at q''
 have v:π₀≤flow P s i T:= mul_le_mul_of_nonneg_left
   (rich_pos T hueInk C.α C.oa b.le) (sq_nonneg _)
 have z:=Lace.shines hueInk C.α C.oa
 have j:=riseCost P s i C T a
 unfold Heard; dsimp only
 constructor
 · have R:=relay P s i k C f h g u t (2*t) (3*t) 1 (-1) 0 (by
      constructor <;> linarith only [q.1,q'.2,q.2,q'.1,v,z,j]) c
   simp only [one_mul,neg_mul,zero_mul,add_zero] at R
   exact R.1.trans_eq (sub_eq_add_neg ..).symm


 have R:=relay P s i k C f h g u t (2*t) (3*t) 1 (-2) 1 (by
      constructor <;> linarith only [q.1,q'.2,q''.2,q.2,q'.1,q''.1,v,z,j]) c
 simpa only [one_mul,neg_mul,sub_eq_add_neg] using R
end YM.CF.Merino.Bravura
