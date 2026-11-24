import Organdy.Puff
import YM.SU5.Circuit.Lieble
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset

open Regis Head Lattice Precision Wilson Pressure Work.F03 Exterior
open Larva (Chip Tint dot blush stains decree wet_iff)
variable {n N:Side}
local notation "G" => SU.group

open RG Gleam ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
variable {M:Bed}{Z:PathData G}{q: Clip}{ρ θ v a η C:ℝ}


open Brecht Circuit
variable (B:Z.Bounds q θ v a)(P:Attached M Z)(L:Floor M q n η C)(O:Bid.Sworn M n G)
local notation "tBody" => Body 2 n
local notation "t" => stamen B P n 
-- kernel on curls
def glass(n:Side)(M:Bed)(i j:Chip n):ℂ:= 
  (sch («G»:=SU.group) i.2 j.2:ℂ)*rimble n M (i.1.1,plaquette i.1.2) (j.1.1,plaquette j.1.2)
abbrev pit (i:Chip n):t:= trill B P i.2 (i.1.1,plaquette i.1.2)
abbrev heat (ρ:ℝ)(s:Signed)(b:Site n)(i:Chip n):t:=
  (ρ*draftSig s i) • pit B P (relay s b i)
lemma kiln (i:Chip n)(y:t):
 inner ℝ (pit B P i) y= Etch.river q i.1 y.val i.2:=by
 rw [pit,joy,inspire]
lemma sees(s:Signed)(b:Site n)(y:t):
 spec (heat B P ρ s b) y=sough q ρ s b y.val:=by
 funext i;rw [spec,heat,real_inner_smul_left (pit B P (relay s b i)) y,kiln];rfl

abbrev kilnBound(q:Clip):ℝ:= 2*(Real.sqrt q.direct)⁻¹
lemma tame (s:Signed)(b:Site n)(i:Chip n)(e:|ρ|≤2):
  ‖heat B P ρ s b i‖ ≤ kilnBound q:=
   mintBudget _ _ _ _ (show |ρ*draftSig s i|≤2 from by
      unfold draftSig;simpa [abs_mul,turn_one] using e -- reverse
 ) 

def start (ρ:ℝ)(i:Chip n):t:=heat B P ρ 1 0 i
lemma ember (i:Chip n):start B P ρ i=ρ • pit B P i:=by
 rw [start,heat,(relay_one i).1,(relay_one i).2,mul_one]
lemma casting(X:Larva.Dir n)(i:Chip n):
 inner ℝ (start B P ρ i) (starlet B P n X)=ρ*blush X i:=by
 rw [ember,real_inner_smul_left (pit B P i) (starlet B P n X),kiln]
 change _*Etch.river q i.1 (tiler B P X) i.2=_
 rw [Etch.river_now]

lemma lighting(s:Signed)(b:Site n)(i:Chip n)(X: Larva.Dir n):
 inner ℝ (heat B P ρ s b i) (starlet B P n X)
   =inner ℝ (start B P ρ i) (starlet B P n (bank s b X)):=by
 change spec (heat B P ρ s b) (starlet B P n X) i=_
 rw [sees,casting]
 exact sough_see ..
include L O in
lemma simmer (ρ:ℝ)(s:Signed)(b:Site n)(p:Freq (Chip n)):
   ‖combine (heat B P ρ s b) p‖=‖combine (start B P ρ) p‖:=by
 let x:= combine (heat B P ρ s b) p
 let y:= combine (start B P ρ) p
 obtain ⟨f,hf⟩:= banked s b B P L O
 have he(z:t):inner ℝ x z=inner ℝ y (f z):=by
    obtain ⟨u,hu⟩:=song B P z
    rw [←hu,hf]
    change inner ℝ x (starlet B P n u)= inner ℝ y (starlet B P n (bank s b u))
    unfold x y; simp_rw [combine_spec,lighting]
 have H:f x=y:=by
    apply ext_inner_right ℝ
    intro z
    obtain ⟨z,rfl⟩:= f.surjective z
    rw [LinearIsometryEquiv.inner_map_map];exact he z
 exact (f.norm_map x).symm.trans (congrArg norm H)

variable {σ:ℝ}
variable (U:M.covered σ C)(e:0<σ)(J:Even n.val)

include U e L J in
lemma glaze(i j:Chip n):
 ((inner ℝ (pit B P i) (pit B P j):ℝ):ℂ)=glass n M i j:=by
 have h:= chimes B P L U e i.2 j.2 (i.1.1,plaquette i.1.2) (j.1.1,plaquette j.1.2) J
 simp_rw [←joy,appraisal] at h
 exact h

-- contribution from GHOST of the opposing chip j
def ghost(n:Side)(M:Bed)(y:Site n)(i j:Chip n):ℂ:=
   draftSig mir j * glass n M i (relay mir y j)
include U e L J in
lemma smoke (y:Site n)(i j:Chip n):
 ((inner ℝ (start B P ρ i) (heat B P ρ mir y j):ℝ):ℂ)=(ρ:ℂ)^2*ghost n M y i j:=by
 rw [ember, real_inner_smul_left (pit B P i) (heat B P ρ mir y j),heat,
    real_inner_smul_right (pit B P i) (pit B P (relay mir y j))]
 push_cast
 rw [glaze B P L U e J, ghost];ring

variable {D m ε:ℝ}

abbrev Whisper(n:Side)(M:Bed)(w:ℕ)(D m ε:ℝ)(y:Site n):Prop:=
 ∀i∈stains 0 w,∀j∈stains 0 w,
 ‖(D:ℂ)^4 * ghost n M y i j - ((m*bell dot j (dot i):ℝ):ℂ)‖≤ ε

include U L J e in
lemma hear (hρ:|ρ|≤2){y:Site n}{w:ℕ}(ne:0≤ε)
 (r:Whisper n M w D m (ε/16) y)
 {i j:Chip n}(hi:i∈stains 0 w)(hj:j∈stains 0 w):
 |D^4*inner ℝ (start B P ρ i) (heat B P ρ mir y j)-m*ρ^2*bell dot j (dot i)| ≤ ε/4:=by
 rw [←Real.norm_eq_abs,←Complex.norm_real]
 push_cast; rw [smoke B P L U e J]
 have h:‖(ρ:ℂ)^2‖ ≤ 4:=by
   rw [norm_pow,Complex.norm_real, Real.norm_eq_abs]
   exact (pow_le_pow_left₀ (abs_nonneg _) hρ _).trans_eq (by norm_num)
 let z:= (D:ℂ)^4 * ghost n M y i j - ((m*bell dot j (dot i):ℝ):ℂ)
 have x:= (mul_le_mul h (r _ hi _ hj) (norm_nonneg _) (by norm_num))
 rw [←norm_mul] at x
 apply le_trans ?_ (x.trans_eq (show 4*(ε/16)=ε/4 by ring))
 apply le_of_eq; apply congrArg; push_cast; ring

lemma tapeta (k ρ:ℝ)(A:Ink (Chip n))(y:Site n):
 Optic.monetary B P k ρ A y =
   ∫x, (air k A (spec (start B P ρ) x) *
     conj (air k A (spec (heat B P ρ mir y) x))).re ∂ stdGaussian (t) :=by
 -- monetary unqualified conflict head.brecht
 unfold Optic.monetary clouds compose unfurl start
 simp_rw [sees,one_mul,affine,Signed.act_one,add_zero]

def premium (m δ:ℝ):ℝ:= trophy decree (m/4) δ
lemma premium_pos (u:0< m){δ:ℝ}(h:0<δ):0<premium m δ:=trophy_pos decree (by positivity) h

include U e L O J in
theorem droplets (y:Site n){c k δ:ℝ}{w:ℕ} (A:Ink (Chip n))
 (p:A.qty ≤ c)(u:δ≤Larva.dint A)(v:A.Within (stains 0 w))
 (sz:0< m)(pos:0<δ)
 (l:1/2 ≤ |ρ|)(r:|ρ|≤2)
 (e':0≤ε)(x:lapse ε (64*(m/4))*c^2 ≤ premium m δ/4)
 (pk:0<k)(price:D^8 * (due (2*kilnBound q)/k) ≤ ε)
 (w':Whisper n M w D m (ε/16) y):
 premium m δ ≤ D^8 * Optic.monetary B P k ρ A y:=by
 let h:=m*ρ^2
 rw [tapeta]

 have hn:0≤q.direct:= q.quadratic_pos.le
 have hb:0≤kilnBound q:=by unfold kilnBound;positivity
 have h₁:m/4 ≤ h:=by
    have f:= pow_le_pow_left₀ (by positivity:0≤(1:ℝ)/2) l 2
    rw [sq_abs] at f
    unfold h
    linarith [mul_le_mul_of_nonneg_left f sz.le]
 have h₂:h ≤16*(m/4):=by
    have f:=pow_le_pow_left₀ (abs_nonneg ρ) r 2
    rw [sq_abs] at f
    unfold h
    linarith [mul_le_mul_of_nonneg_left f sz.le]
 refine billows dot decree (by positivity) pos e' x pk hb price A _ v p u
   (fun i=>tame B P 1 0 i r)
   (fun i=> simmer B P L O ρ mir y i) h₁ h₂
   (fun i a j l'=>hear B P L U e J r e' w' a l')
