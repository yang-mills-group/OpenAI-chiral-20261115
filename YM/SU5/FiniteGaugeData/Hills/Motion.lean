import YM.SU5.FiniteGaugeData.Hills.Orbitals
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Nacre Heat Charm Chrono SalonG Journey
namespace Hills
-- LoosePair stamps.Rewind across some axes.Tick legal.Later fees irrelevant.
abbrev StampK := Axis×ℤ
def StampK.neg (r:StampK): StampK:= (r.1,-r.2)
-- Use general list and shifts parameter arbitrary.. stamp.Portal
variable {B:Type*}(K:Calibration)(Δ:B→ StampK)(p:List B)(x:W K)
abbrev era (K:Calibration)(a:StampK): W K→ W K:= clockW K a.1 a.2
def disperse (K:Calibration) (Δ:B→StampK): List B→ W K→ W K
 | [], x=> x
 | k::p,x=> era K (Δ k) (disperse K Δ p x)
-- abelian.TStamp
lemma disperse_comm (j:StampK): disperse K Δ p (era K j x)=era K j (disperse K Δ p x):=by induction p with
 | nil=> rfl
 | cons i p ih=> rw [disperse,disperse,ih]; exact clock_cross ..
lemma disperse_mul (y: W K): disperse K Δ p (x*y)=disperse K Δ p x * disperse K Δ p y:=by induction p with
 | nil=> rfl
 | cons i p ih=> rw [disperse,ih]; exact clock_mul ..
lemma disperse_inv : disperse K (StampK.neg ∘ Δ) p (disperse K Δ p x)=x:=by
 induction p with
 | nil=> rfl
 | cons i p ih=> rw [disperse,disperse, disperse_comm, ih]; unfold Function.comp StampK.neg era; rw [clock_add,neg_add_cancel,tic_zero]
end Hills
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
namespace Hills
open Nacre Heat Charm Chrono SalonG Journey
variable (a j:Axis)(z:ℤ)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)
local notation "T"=> StructureH Y h a W' R A
local notation "U"=> (StructureH Y h a W' R A).Unity
local notation "P'"=> planeP (U)
local notation "D"=> dip (U)
local notation "δ"=> cpo (U)
local notation "C"=> Camera Y h a W' R A
variable {x:W (tent Y h)}(f:Plan Y h a d x) (q:0<d) (c:Allows a j z)
include A f q c
lemma pictureT : ∃ (n:ℕ) (v:0<n) (w:Plan Y h a n (clockW Kₜ j z x)), (Wedge Y h s a n W' R A w v)*planeP (U)= tock Y h s W' R a j A z c * Wedge Y h s a d W' R A f q * planeP (U):= by
 by_cases he:j=a
 · subst j; obtain ⟨k,rfl⟩:= Int.eq_ofNat_of_zero_le (c rfl); let u:=plan_steps Y h a d x f (k:ℤ) (by positivity) (show (d:ℤ)+k≤↑(k+d) from by omega); refine ⟨k+d,by omega,u,?_⟩; rw [wicket_adv Y h s a d (k+d) x W' R A f q k rfl u] -- maybe ↑k vs ofNat k
 let u:= plan_walk Y h a j d _ z he f; refine ⟨d,q,u,?_⟩; let M:= tock Y h s W' R a j A z c; have hx: M*P'=P':= (T).unity_pay s j z c; rw [← wicket_tangent Y h s a j d _ W' R A f q z he u c,mul_assoc,hx]
omit c
variable {B:Type}(Δ:B→StampK)(p:List B)(e:∀ i:B,Allows a (Δ i).1 (Δ i).2)
include e
abbrev passingH (Δ:B→StampK)(e:∀ i:B,Allows a (Δ i).1 (Δ i).2) := fun i:B=> tock Y h s W' R a (Δ i).1 A (Δ i).2 (e i)
abbrev conveying (Δ:B→StampK)(p:List B) (e:∀ i:B,Allows a (Δ i).1 (Δ i).2) := (p.map (passingH Y h s a W' R A Δ e)).prod
local notation "S'" i:max=> passingH Y h s a W' R A Δ e i
local notation "W'0"=> Wedge Y h s a d W' R A f q
lemma pictureR : ∃ (n:ℕ) (v:0<n) (w:Plan Y h a n (disperse Kₜ Δ p x)), Wedge Y h s a n W' R A w v *planeP (U)= conveying Y h s a W' R A Δ p e * Wedge Y h s a d W' R A f q * planeP (U):= by
 induction p with
 | nil=> exact ⟨_,q,f,by change _=1* _*_; rw [one_mul]; rfl⟩
 | cons i p ih=>
    obtain ⟨n,v,w,g⟩:=ih; obtain ⟨m,b,l,u'⟩:= pictureT Y h s a _ _ n W' R A w v (e i); refine ⟨m,b,l, u'.trans ?_⟩; rw [mul_assoc,g]; change (S' i)*_= ((S' i)*_)* _*_; simp only [mul_assoc]; rfl -- assoc
omit e f q in
lemma wander : (route Y h s a W' R A) (disperse Kₜ Δ p x)= route Y h s a W' R A x:=by
 induction p with
 | nil=> rfl
 | cons i p ih=> rw [disperse,era,stayP,ih]
-- ANY overall A*P, equality preserves in social.
omit A f q e in
private lemma cram {H:Hilbert}{U0:ClosedSubmodule ℂ H}{P X:H.Op} (p:P*planeP U0=X*planeP U0): social U0 P=social U0 X:=by
 ext1 v; change dip U0 (P (cpo U0 v))= dip U0 (X (cpo U0 v)); apply congrArg; have he(I:H.Op):(I*planeP U0) (cpo U0 v)= I (cpo U0 v):=by rw [mul_apply_eq_comp,inlet (among v)]
 exact Eq.trans (he P).symm ((congrArg (fun t:H.Op=>t (cpo U0 v)) p).trans (he X))
-- two group.Actual geometry f*shift noise v
lemma looseP {y:W (tent Y h)}(v:Plan Y h a n y)(p':0<n) :
 route Y h s a W' R A (Swing Kₜ a d x (disperse Kₜ Δ p y)) = social (U) (Wedge Y h s a d W' R A f q * conveying Y h s a W' R A Δ p e * Wedge Y h s a n W' R A v p'):= by
 obtain ⟨n',v',g,u⟩:= pictureR Y h s a n W' R A v p' Δ p e; rw [route_formula Y h s a _ W' R A (couplePlan Y h a d n' f g) (by omega), ← wedge_glues Y h s a d n' W' R A f q g _ v']
 apply cram -- include fields drop? in
 rw [mul_assoc,u]; simp only [mul_assoc]
-- base additive offset across other licensed axis, specialized proof with clock list. Time shift before or after arbitrary.Op account.Both.
lemma flashR {x':W (tent Y h)}(b:Allows a j z)(v:j≠a)(r:Plan Y h a n x')(t:0<n) :
    route Y h s a W' R A (Swing Kₜ a d x (disperse Kₜ Δ p (clockW Kₜ j z x')))=social (U) (Wedge Y h s a d W' R A f q *conveying Y h s a W' R A Δ p e * tock Y h s W' R a j A z b * Wedge Y h s a n W' R A r t):=by
 obtain ⟨n',v',g,u⟩:= pictureT Y h s a j z n W' R A r t b; rw [looseP Y h s a d n' W' R A f q Δ p e g v']; apply cram; rw [mul_assoc,u]; simp only [mul_assoc]
#print axioms flashR
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
