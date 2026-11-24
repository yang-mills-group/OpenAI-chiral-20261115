import Bay.D.Foil
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

variable {n:Side}
 {q:Clip}{Z:PathData T4}{H:Bed}{η C S:ℝ}

abbrev Yn (n:Side)(R:Type*) :=Config T4 n→R
abbrev Chalk(n:Side)(R:Type*) := Kite n → Dock n → R
def Packed {I:Type}(gs:I→Kite n)(o d:Site n) : Prop:=
 Injective (fun i=>(gs i).rise o) ∧ Injective (fun i=>(gs i).rise d)
variable {R T:Type} [NormedAddCommGroup R][NormedSpace ℝ R][MeasurableSpace R][BorelSpace R]
 [NormedAddCommGroup T][NormedSpace ℝ T][MeasurableSpace T][BorelSpace T]

structure Ion
 (B:Z.Bounds q η C S)(P:Attached H Z)
 (p:BudgetPoint)(β v:ℝ)
 (o d:Site n)(F:Yn n R)(W:Chalk n R)
 (M N E L:ℝ):Prop where
 perks: 0≤M ∧ 0≤N ∧ 0≤E ∧ 0≤L
 sane: Measurable F
 gauge: GaugeInvariant F
 limit(U): ‖F U‖≤M
 gloss(g): ContDiff ℝ 1 (W g)
 high(g x):‖W g x‖≤N
 alloy(I:Type)[Fintype I](gs:I→Kite n)(k:Packed gs o d)(x y:Dock n):
    ∑i,‖W (gs i) x-W (gs i) y‖ ≤ L * Real.sqrt (Fintype.card I)*‖x-y‖
 spins(g h:Kite n)(x:Head.Dir T4 n): W h (tiler B P (g.sail x))= W (g*h) (tiler B P x)

 day {c:Side}{G:Ratio c n}{X:Support c}{D:Finset (Cell n)}
    (U:Config T4 n)(V Y:Head.Dir T4 n)
    (g: Kite n):
    TrustLogs (V+Y) U G X v →
    ProbeBox (V+Y) (2*v)→
    meek p U=D →
    Deep G X D (hallBill p.B) (g.rise o)→
    Deep G X D (hallBill p.B) (g.rise d)→
    ‖F (g.swirl U)-W g (iceCost B P G X p.B D Y β V)‖≤E

variable {o d:Site n} {B:Z.Bounds q η C S}{P:Attached H Z}
 {p:BudgetPoint} {β v M N E L:ℝ}
 {F:Yn n R}{W:Chalk n R}
namespace Ion
lemma shift (u:Ion B P p β v o d F W M N E L)(g:Kite n):
 Ion B P p β v (g.rise o) (g.rise d)
    (F ∘ g.swirl) (fun h=>W (h*g)) M N E L:=by
 refine ⟨u.perks,u.sane.comp (continuous_pull (G:=T4) _ _).measurable,?_,fun i=>u.limit _,fun i=>u.gloss _,
    fun i j=>u.high _ _,?_,?_,?_⟩
 · intro k x; rw [Function.comp_apply,Kite.swirl,ProjectorNext.Equivariance.pull_gauge (G:=T4),u.gauge];rfl
 · intro I _ gs z x y; exact u.alloy I (fun i=>gs i*g) (by unfold Packed; simp_rw [Kite.r_mul]; exact z) x y
 · intro j k y; rw [mul_assoc];exact u.spins _ _ _

 intro c G A D U V Y h a b e m r
 rw [Function.comp_apply, Kite.union]
 exact u.day _ _ _ (h*g) a b e ((Kite.r_mul h g o).symm ▸ m) ((Kite.r_mul h g d).symm ▸ r)

lemma paint (u:Ion B P p β v o d F W M N E L)
    (px:R→L[ℝ]T)(h:∀x, ‖px x‖≤‖x‖):
    Ion B P p β v o d (px ∘ F) (fun g=> px ∘ W g) M N E L:=by
 refine ⟨u.perks,px.continuous.measurable.comp u.sane,fun i j=>congrArg px (u.gauge ..),
    fun i=>(h _).trans (u.limit i),fun i=>px.contDiff.comp (u.gloss i),fun i x=> (h _).trans (u.high i x),?_,fun g t j=>congrArg px (u.spins ..),?_⟩
 · intro I _ gs z x y; refine le_trans ?_ (u.alloy I gs z x y)
   exact sum_le_sum fun i _=>by simp only [Function.comp_apply,←map_sub]; exact h _
 intro c G A D U V Y t a b e m r
 simp only [Function.comp_apply,←map_sub]
 exact (h _).trans (u.day _ _ _ t a b e m r)

lemma relax (u:Ion B P p β v o d F W M N E L)
 {a b c t:ℝ}(h:M≤a)(j:N≤b)(g:E≤c)(r:L≤t):
    Ion B P p β v o d F W a b c t:=by
 obtain ⟨ta,tb,tc,tψ⟩:=u.perks

 refine ⟨⟨ta.trans h,tb.trans j,tc.trans g,tψ.trans r⟩,u.sane,u.gauge,fun i=>(u.limit _).trans h,u.gloss,fun i d=>(u.high _ _).trans j,fun I _ J w x y=>(u.alloy I J w x y).trans
    (by gcongr),u.spins,
    fun U V Y k a b z m l=>(u.day U V Y k a b z m l).trans g⟩

-- binary channels for pair moments. improved accuracy: E*2M+E² (not E*N)
variable {F T:Yn n ℂ}{W Y:Chalk n ℂ}
lemma hinge (u:Ion B P p β v o o F W M N E L)
    (h:Ion B P p β v d d T Y M N E L):
    Ion B P p β v o d (F*T) (W*Y) (M^2) (N^2) ((2*M+E)*E) (2*N*L):=by
 obtain ⟨ta,tb,tc,tψ⟩:=u.perks
 refine ⟨⟨sq_nonneg _,sq_nonneg _,by positivity,by positivity⟩,
  Measurable.mul u.sane h.sane,fun i j=>congrArg₂ (·*·) (u.gauge i j) (h.gauge i j),
  fun i=>?_,fun i=>ContDiff.mul (u.gloss i) (h.gloss i),
  fun i a=>?_,?_,fun g t j=>congrArg₂ (·*·) (u.spins g t j) (h.spins g t j),?_⟩
 · rw [Pi.mul_apply,norm_mul,sq]; exact mul_le_mul (u.limit i) (h.limit i) (norm_nonneg _) ta
 · rw [Pi.mul_apply,Pi.mul_apply,norm_mul,sq]
   exact mul_le_mul (u.high i a) (h.high i a) (norm_nonneg _) tb

 · intro I _ gs z x y
   have l:= u.alloy I gs ⟨z.1,z.1⟩ x y
   have r:= h.alloy I gs ⟨z.2,z.2⟩ x y
   refine le_trans (b:=∑i, (N*‖W (gs i) x-W (gs i) y‖+N*‖Y (gs i) x-Y (gs i) y‖)) ?_ ?_
   · refine sum_le_sum fun i _=>?_ 
     let k:=gs i
     let f:=W k; let g:=Y k
     change ‖f x*g x-f y*g y‖ ≤ N *‖f x-f y‖ + N*‖g x-g y‖
     rw [show f x*g x-f y*g y=g x*(f x-f y)+f y*(g x-g y) from by ring]
     apply (norm_add_le ..).trans; rw[norm_mul,norm_mul]
     exact add_le_add (mul_le_mul_of_nonneg_right (h.high k x) (norm_nonneg _)) (mul_le_mul_of_nonneg_right (u.high k y) (norm_nonneg _))
   rw [sum_add_distrib,←mul_sum,←mul_sum]
   exact (add_le_add (mul_le_mul_of_nonneg_left l tb) (mul_le_mul_of_nonneg_left r tb)).trans_eq (by ring)

 intro c G A D U V J k a b z m r
 let x:=k.swirl U
 let y:=iceCost B P G A p.B D J β V
 have p₀: ‖F x -W k y‖ ≤E:=u.day U V J k a b z m m
 have p₁: ‖T x-Y k y‖≤E:=h.day U V J k a b z r r
 change ‖F x*T x-W k y*Y k y‖≤_

 have pv: ‖W k y‖≤E+M:= (norm_le_norm_sub_add _ (F x)).trans
     (add_le_add (by rw [norm_sub_rev];exact p₀) (u.limit _))
 rw[show F x*T x-W k y*Y k y=T x * (F x-W k y)+W k y*(T x-Y k y) from by ring]
 refine (norm_add_le ..).trans ?_
 rw [norm_mul,norm_mul]
 exact (add_le_add (mul_le_mul (h.limit _) p₀ (norm_nonneg _) ta)
   (mul_le_mul pv p₁ (norm_nonneg _) (add_nonneg tc ta))).trans_eq (by ring)

lemma cream (u:Ion B P p β v o d F W M N E L):
    Ion B P p β v o d (star F) (star W) M N E L :=u.paint
     Complex.conjCLE.toContinuousLinearMap (fun z=>show ‖star z‖≤_ from (norm_star _).le)
end Ion

open Next.Rank.Spindle
lemma wheelIon {N:Side}{o:Seat N}{d r u b k:ℝ}{f:Pane N→ℂ}
 {A:Icey (Cella (More N))}
 (R:Rules T4)(t:Vessel p o (p.B/10) r d u f A)
 (s:Shutter p)
 (i:0≤v)(w:v≤R.c)(h:2*v≤r)(a:0<k)
 (m:0≤b)(n:0<β)(j:|b*coupling β|≤2):
 Ion B P p β v o o (wheel b f)
    (quay q (b*coupling β) k A)
    (mast p b u) (u*k^2)
    (rope R p u b v k)
    (u*ratioC q*k):=by
 have hu:=t.vinyl.nonneg; have :=ratioC_p q

 refine ⟨⟨by unfold mast; positivity,by positivity,by unfold rope;positivity,by positivity⟩,
    measurable_const.smul t.vinyl.meas,
    fun x y=>congrArg (b^2 • ·) (t.vinyl.hue x y),wheel_max t,
    quay_smooth q _ k A,fun g x=>quay_height q _ g x t.skin.rake a,
    fun _ _ gs p' x y=>quay_charge q _ j t.skin.rake a o gs p'.1 x y, ?_,
    fun U V Y g l f z d _=> drives B P V Y R t g k i w h m l f z s d n⟩
 intro g h x
 rw [quay,quay,delta, delta,sea_mul g h B P x]
end YM.CF.Bay.D
