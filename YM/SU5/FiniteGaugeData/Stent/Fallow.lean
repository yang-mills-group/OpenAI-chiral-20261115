import YM.SU5.FiniteGaugeData.Stent.Upright
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
/-!
  Pullback test: one generation stack (all colors across all generations, SPIN selected). AtSupport 
  one coarse matter site (constant matrix, no physical gauge mark). Lift *one step* while 
  saturating BOTH Fermi chiral spaces at upper (SPEC), leave only slots at ONE chosen
  fine site at two chosen spins. Product detects the inter-axis difference of the routes to
  that fine matter site at issue. Phase winding canceled for sale. -/
variable {N P: Side}(R:Patch)
local notation "ℱ"=> FC (Single P)
local notation "η"=> specialM R.L
variable (G:Ratio N P)(p:G.count=R.L)(h:4≤R.L.val){d:ℕ} (q:LaurentRadius R.J G.count d) (t:2*d < N.val) (e:Odd G.count.val)
variable (Q:Op SU.Slot)(M:Male)(u':Nom N P)
local notation "Ξ"=> Fin (projCard 1)
local notation "F"=> reamW R d
-- species stacks.T
variable (f: Fin (n+1)→ X)(g': Fin (n+1)→ Y₀)(vₚ:Hosp (reamW R d) P)(he:Rack true (reamW R d) f)(hu:Rack false (reamW R d) g')
variable (f₀:f 0=starlit (specialM R.L))(g₀:g' 0=reedW (specialM R.L))
local notation "V"=> TextK (f ∘ Fin.succ) (g' ∘ Fin.succ) P
local notation "c₁" i:max => (collar 1 i).1
local notation "U"=> QuestU R G M u' Q
local notation "B"=> QuestL R G M u' Q
local notation "W"=> onC P u'.1
local notation "D"=> Fin (projCard 1)
local notation "Up"=> starlit η
local notation "Lo"=> reedW η
abbrev baronH (R:Patch)(P:Side):= Umo (roseone (starlit (specialM R.L))) P
abbrev baronL (R:Patch)(P:Side):= Bmo (roseone (reedW (specialM R.L))) P
local notation "C₁"=> portionA N P R Q W
local notation "C₂"=> portionB N P R Q W
local notation "u₁"=> baronH R P
local notation "u₂"=> baronL R P
local notation "M₁"=> Reform u₁ C₁
local notation "M₂"=> Reform u₂ C₂
section
include p h t q
private lemma TicketZero (b:Bool)(i:SpinIdx)(x y:SU.Slot): (byMode G R.J Q M u' b (basisC N 0 i y)).ofLp (Lifted.index P (specialM R.L) i x) / Lifted.winding P (specialM R.L)=(driftW R N P • IssueP R Q b i W) x y:=by
 rw [mirrorEntry R G p h q t, Matrix.smul_apply,smul_eq_mul, driftW,mul_div_right_comm]; -- maybe order.Or `ring`.
include e vₚ
include he f₀
private lemma momentH(i:D): TextK (f ∘ Fin.succ) (g' ∘ Fin.succ) P* create (U (c₁ i))=V*M₁ i:=by
 let H:= driftW R N P • IssueP R Q true 0 W; change _= V*(Reform (fun i:D=>create (quantum P Up (c₁ i))) (Cuter (roseone (Hᵀ))) _); rw [chiffonH _ vₚ f g' he (areaU R G p q e ..) (weightU R G e ..), scaleOne Hᵀ (fun i=> create (quantum P Up i)) i,f₀]; refine congrArg (fun x:ℱ=>V*x) (sum_congr rfl fun j _=>?_); exact congrArg (fun a:ℂ=> a • create (basisC P (specialM R.L) 0 j)) (TicketZero R G p h q t Q M u' true 0 j _)
omit he f₀
include hu g₀
private lemma momentL(i:D): TextK (f ∘ Fin.succ) (g' ∘ Fin.succ) P* Fock.remove (B (c₁ i))=V*M₂ i:=by
 let H:= driftW R N P • IssueP R Q false 2 W; change _= V*(Reform (fun i:D=>Fock.remove (quantum P Lo (c₁ i))) (Cuter (roseone (star H))) _); rw [chiffonL _ vₚ f g' hu (areaL R G p q e ..) (weightL R G e ..), scaleOne (star H) (fun i=> Fock.remove (quantum P Lo i)) i,g₀]; refine congrArg (fun x:ℱ=>V*x) (sum_congr rfl fun j _=>?_); exact congrArg (fun a:ℂ=> star a • Fock.remove (basisC P (specialM R.L) 2 j)) (TicketZero R G p h q t Q M u' false 2 j _)
#print axioms momentH
#print axioms momentL
end
section
variable {ι:Type*} [Monoid ι] (a b c x y:ι)
private lemma two_op (h:Commute a x)(he:a*b=a*x)(v:a*c=a*y): a*(b*c)=a*(x*y):=by
 rw [←mul_assoc,he,h.eq,mul_assoc,v,←mul_assoc,←h.eq,mul_assoc]
private lemma rove (u v:Fin n→ι) (p:∀ i,Commute a (v i))(h:∀ i,a*u i=a*v i): a*(List.ofFn u).prod=a*(List.ofFn v).prod:=by
 induction n with
 | zero=> simp
 | succ n ih=> simp_rw [List.ofFn_succ,List.prod_cons]; exact two_op _ _ _ _ _ (p 0) (h 0) (ih (fun i=>u i.succ) (fun i=>_) (fun i=>p i.succ) (fun i=>h i.succ))
end
include vₚ p h t q he hu f₀ g₀ e
local notation "A₁"=> TextK (f ∘ Fin.succ) (g' ∘ Fin.succ) P
local notation "L₁"=> PaceLock R Q
lemma folies: TextK (f ∘ Fin.succ) (g' ∘ Fin.succ) P* subF G R.J Q M e u' (Whip N 0)= (PaceLock R Q*Nylon R W) • TextK f g' P:=by
 rw [shorn]; let u(x:Ξ):= create (U (c₁ x)); let v(x:Ξ):= Fock.remove (B (c₁ x)); have h' {Z:Fin (projCard 1)→ ℱ}(A: Op Ξ)(z:∀ i,Z i∈TF P true)(i): (Reform Z A) i∈TF P true:= Fine.sumF _ _ (fun j _=> (show Fine .. from z j).scale _)
 let z(i):=h' (Z:=baronH R P) C₁ (fun i=> Upper (N:=P) Up (c₁ i)) i
 let s₁(i):=h' (Z:=baronL R P) C₂ (fun i=> Lower (N:=P) Lo (c₁ i)) i
 let Z:= TorqueP (N:=P) (f ∘ Fin.succ) (g' ∘ Fin.succ); have he': A₁*Tile u v=A₁* Tile M₁ M₂:= rove V _ _ (fun i=> TCommute Z (show _∈TF P false from Fine.grow (show Fine .. from z i) (show Fine .. from s₁ i))) (fun i=> two_op _ _ _ _ _ (TCommute Z (z i)) (momentH R G p h q t e Q M u' f g' vₚ he f₀ i) (momentL R G p h q t e Q M u' f g' vₚ hu g₀ i))
 -- tune two_op `..` syntax eats args.
 change A₁*(Tile u v)=_; rw [he', Plush.Museum u₁ u₂ C₁ C₂ (mojo _) (djinn _) (buzz _ _), pacezone, Algebra.mul_smul_comm, Bramble f g',f₀,g₀]; -- exact
#print axioms folies
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
