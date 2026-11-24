import YM.SU5.Reconstruction.Quanta.Touch
import YM.SU5.Reconstruction.Based.Residual
set_option autoImplicit false
set_option synthInstance.maxSize 32000
set_option maxRecDepth 5000
set_option maxHeartbeats 900000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Rooted
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Fock Lat Cube SU Spire Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Next.Free Bloch Drapes Lifted Skye Girt Nacre Sound Tapestry Satin MeasureTheory Rush
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open WalkRoots Push.SectorMeasure
set_option quotPrecheck false
variable {S:Finset Cover}(R:RouteMap S)
open Tapestry Tower
/-! # ALL tests in exactly that Ward support, **no need connected S**, with the loop hierarchy
and Wilson lines through real frames. Need pay at most root-gauge transformations. -/
variable (K:Calibration)
inductive Test (wide:Bool): Bool → Family K→ Prop where
 | loops {f:PairsC→ℂ}: Coeff wide S f → Test wide false (scalar K (ask R f))
 | create {x:Cover}{i:SpinIdx}(b:SU.Slot): i∈plusHalf → nodeC x ∈ S→ Test wide true (rootCreate R K x i b)
 | remove {x:Cover}{i:SpinIdx}(b:SU.Slot): i∉plusHalf → nodeC x ∈ S→ Test wide true (rootRemove R K x i b)
 | zero {b}: Test wide b 0
 | one : Test wide false 1
 | add {f g b}: Test wide b f→ Test wide b g→ Test wide b (f+g)
 | scale (z:ℂ){f b}: Test wide b f → Test wide b (z • f)
 | mul {f g b c}: Test wide b f → Test wide c g → Test wide (b.xor c) (f*g)
variable {R K} {wide w' b:Bool}{f: Family K}
namespace Test
lemma visits (p: Test R K wide b f): InTest K wide S b f:=by
 induction p with
 | loops p=> exact .seed (certified R p)
 | create b p u=> exact rootCreate_test R K wide u p b
 | remove b p u=> exact rootRemove_test R K wide u p b
 | zero=>exact .zero
 | one=>exact .one
 | add _ _ p q => exact .add p q
 | mul _ _ p q => exact .mul p q
 | scale z _ p=> exact .smul z p
lemma harmony (p:Test R K wide b f): BeforeRoots R K f:=by
 induction p with
 | loops p=> exact .loop R K p
 | create b _ u=> exact .creation R K _ u _ b
 | remove b _ u=> exact .removal R K _ u _ b
 | zero=>exact .zero R K
 | one=>exact .one R K
 | add _ _ p q=> exact p.add q
 | mul _ _ p q=> exact p.mul q
 | scale z _ p=> exact p.scale z
end Test
variable (R K)
lemma expand_any (p: InTest K wide S b f):∃ v, Test R K wide b v∧ReadAs R K f v:=by
 induction p with
 | seed p=> exact ⟨_,.loops p,.gaugeCoe R K p⟩
 | creator b p u=> exact ⟨_,.create b p u,.createLink R K u⟩
 | remover b p u=> exact ⟨_,.remove b p u,.removeLink R K u⟩
 | zero=> exact ⟨_,.zero,.zero R K⟩
 | one=> exact ⟨_,.one,.one R K⟩
 | add _ _ p q=> obtain ⟨v,a,p⟩:=p; obtain ⟨w,c,q⟩:=q; exact ⟨_,.add a c,p.add q⟩
 | mul _ _ p q=> obtain ⟨v,a,p⟩:=p; obtain ⟨w,c,q⟩:=q; exact ⟨_,.mul a c,p.mul q⟩
 | smul z _ p=> obtain ⟨v,a,p⟩:=p; exact ⟨_,.scale z a,p.scale z⟩
lemma fits (p: InTest K wide S b f): InTest K true S b f:=by cases wide; exact p.widen; exact p
lemma expanding_neutral {v:Family K}(p:InTest K wide S b f)(q:InTest K w' S b v)(a: Neutral K f)(h:ReadAs R K f v):f=v:=by
 obtain ⟨m,u⟩ := (Buffered.separates K (Satin.tips S)).exists; have e:Tivoli S (K.c m):=⟨⟨u⟩⟩
 refine Tower.Garret.orb e (fits K p) (fits K q) (funext fun x=> ?_); obtain ⟨g,s⟩:= Tapestry.scoreTrace (fun y=> fromRoot R y (onC _ x.1)) e.hosp; exact (twist (quantU (tradew _ g))).injective ((a m g x).symm.trans (h m x g s)) -- implicit

lemma all_neutral_test(p:InTest K wide S b f)(a:Neutral K f):Test R K wide b f := by
 obtain ⟨v,h,e⟩:= expand_any R K p; exact (expanding_neutral R K p h.visits a e).symm ▸ h
/-- Exact method for the determination. For the support S even when disconnected. -/
structure LocalSing (wide b:Bool)(f:Family K):Prop where
 routed: Test R K wide b f
 checked: ∃ m, Tivoli S (K.c m) ∧ RootsChecked R K f m

theorem localized : LocalSing R K wide b f ↔ InTest K wide S b f ∧ Neutral K f:=by
 constructor
 · rintro ⟨p,m,u,h⟩ -- flatten exist?
   refine ⟨p.visits, Tower.Garret.onceCov (fits K p.visits) u (roots_warrant R K p.harmony h u.hosp)⟩
 rintro ⟨p,u⟩; obtain ⟨m,t⟩:= (Buffered.separates K (Satin.tips S)).exists; exact ⟨all_neutral_test R K p u,⟨_,⟨⟨t⟩⟩,fun v _=> u m v⟩⟩ -- exact syntax
end YM.CF.Buffered.Afterglow.Rooted
#print axioms YM.CF.Buffered.Afterglow.Rooted.localized
