import YM.SU5.FiniteGaugeData.Lapis.Rotate
import YM.Work.F03.Flat
import YM.Work.G06.TurnSlot
/-! # Frame. Ambient tangent Gaussian and projection prices for growth occupancy.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Punch
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Lumi
open Bid Affiche Artis
variable {ι:Type} [Fintype ι] [DecidableEq ι]
-- lens data. chosen orientation before integration using real $turn at each place.
structure Duct (G:Gauge)(ι:Type)[Fintype ι] where
 beam:ι→RG.Slot
 seen : (ι →G.Color)→ℝ
 registered : ContDiff ℝ 1 seen
 h : ℝ
 c : ℝ
 charge : 0≤h
 grant : 0 ≤ c
 enough (x:ι→ G.Color): ‖seen x‖≤ h
 cheer(x y:ι→G.Color): |seen x - seen y|≤ c*‖x-y‖
 orbs (u:G.El)(x:ι→ G.Color): seen (fun i=> G.adjoint u (x i))=seen x
variable {G:Gauge} (T:Duct G ι){n:Side}
omit [DecidableEq ι] -- PAC.check
variable (i:ι) (s:Signed) (x:Site n)
local notation "Λ" => T.seen
noncomputable def pick(u:RG.Slot):RG.Slot × ℝ:=
 ⟨Classical.choose (Work.G06.slot_pull (G:=G) s u), Classical.choose (Classical.choose_spec (Work.G06.slot_pull (G:=G) s u))⟩
-- pick implicit G proof? def doesn't know G in type. tune
lemma marker(q:RG.Slot): let r:= (pick (G:=G) s q); (r.2=1 ∨ r.2=-1) ∧ ∀ U:CoverConfig G, q.eval (pull s 0 U)= r.2 • r.1.eval U:= Classical.choose_spec (Classical.choose_spec (Work.G06.slot_pull s q))
abbrev Γ(s:Signed)(i:ι):=pick (G:=G) s (T.beam i)
abbrev probe(s:Signed)(x:Site n) (V: Config G n)(i:ι):= (T.beam i).atSite (pull s x V) (0:Site n)
lemma looks(V:Config G n): probe T s x V i=(Γ T s i).2 • (Γ T s i).1.atSite V x:=by unfold probe; simp_rw [Slot.atSite,expandAt_pull]; simpa [affine] using (marker (G:=G) s (T.beam i)).2 (expandAt x V) -- tune
lemma admits(V:Config G n)(q:Site n→G.El): probe T s x (gauge q V) i= G.adjoint (q x) (probe T s x V i):=by
 simp_rw [looks T i]; rw [Work.F03.atSite_path,Work.F03.atSite_path,face_gauge,G.curvature_conjugate, travel_gauge, ← G.adjoint_mul]; -- slotFace stop path need unify

 let q':= (Γ T s i).1
 have h:stop x q'.walk=(slotFace q' x).1:=by unfold slotFace Slot.offset; rw [wrap_stop_cover,map_zero, add_comm,← Work.E03.stop_add_left]; simp
 rw [map_smul,←G.adjoint_mul,h]; unfold q'; rw [inv_mul_cancel_right]
-- raw at Sample height scalar t= κ√β. include sqrt clip. W.Read payout.
def live(K:Clip)(y:ℝ)(s:Signed)(x:Site n)(U:Config G n):ℝ:= T.seen ((y*Real.sqrt K.direct) • probe T s x U)
lemma lived_g(K:Clip)(y:ℝ)(U:Config G n)(g:Site n→G.El): live T K y s x (gauge g U)=live T K y s x U:=by unfold live; nth_rw 2 [←T.orbs (g x)]; apply congrArg; ext i j; simp_rw [Pi.smul_apply,admits T i s x U g,map_smul] -- tune
variable {P:Bed}{u:Stage}{R:PathData G}{C a Δ:ℝ}
-- linear momentum
local notation "Ω" => LogField G n
lemma poseL(q:Cell n) : ∃ L: LogField G n→ₗ[ℝ] G.Color, ∀ x:LogField G n,faceCurl q x=L x:=by
 let V: LogField G n→ₗ[ℝ] G.Color:=⟨⟨faceCurl q,fun x y=> (by ext i; change (d 1 n*ᵥ parts _ _ _ _) _=_; exact congrFun (mulVec_add (d 1 n) (parts G 1 x i) (parts G 1 y i)) _)⟩,fun k x=>(by ext i; change (d 1 n*ᵥ parts _ _ _ _) _=_; exact congrFun (mulVec_smul (d 1 n) k (parts G 1 x i)) _)⟩
 exact ⟨V,fun x=>rfl⟩
def torso(q:Cell n) : LogField G n→ₗ[ℝ] G.Color:= Classical.choose (poseL (G:=G) q)
lemma pitchA (q:Cell n)(Z:Ω): torso q Z=faceCurl q Z:=(Classical.choose_spec (poseL q) Z).symm
-- representative, no quaternion.S.Pin
def pollen(s:Signed)(x:Site n): LogField G n →ₗ[ℝ] (ι→G.Color) := LinearMap.pi fun i=> (Γ T s i).2 • torso (slotFace (Γ T s i).1 x)
lemma pollT(Z:Ω): pollen T s x Z i=(Γ T s i).2 • faceCurl (slotFace (Γ T s i).1 x) Z:=by simp only [pollen,LinearMap.pi_apply,LinearMap.smul_apply,pitchA]
lemma pollenTrend : Trend (pollen T s x):=by intro y z g; ext i j; simp_rw [pollT]; simp only [PiLp.smul_apply]; rw [show (faceCurl (slotFace (Γ T s i).1 x) y: G.Color) j= faceCurl (slotFace (Γ T s i).1 x) z j from (by change (d 1 n *ᵥ parts G 1 y j) _ = _; rw [g j]; rfl)] -- tune
lemma needleL(Z:Ω): (pollen T s x Z) i=faceCurl (slotFace (T.beam i) 0) (harbor s x Z):=by
 -- symbol via limit both ways
 rw [pollT T i]; have ht(t:ℝ): (Γ T s i).2 • (Γ T s i).1.atSite (represent (t•Z)) x =(T.beam i).atSite (represent (t • harbor s x Z)) (0:Site n):=by rw [← tilt_node s x]; exact (looks T i s x _).symm
 apply HasDerivAt.unique (f:=fun t:ℝ=> (T.beam i).atSite (represent (t • harbor s x Z)) (0:Site n)) ?_ (slot_deriv ..); simp_rw [←ht]; exact (slot_deriv (Γ T s i).1 x Z).const_smul (Γ T s i).2
-- origin Poll base (we used arbitrary G06 ratio even when s is identity; don't assume choice matches)
lemma baseNeed (y:Ω): (pollen T 1 (0:Site n) y) i=faceCurl (slotFace (T.beam i) 0) y:=by
 rw [pollT]; apply HasDerivAt.unique (f:=fun t:ℝ=> probe T 1 0 (represent (t•y)) i) (by simp_rw [looks]; exact (slot_deriv (Γ T 1 i).1 0 y).const_smul (Γ T 1 i).2) (by simp only [probe,pull_id]; exact slot_deriv ..)
lemma trace_inverse (Z:Ω): (pollen T s x (harbor s⁻¹ (-(s⁻¹).act x) Z)) i= (pollen T 1 0 Z) i:=by
 rw [baseNeed,pollT]; have ht(t:ℝ): (Γ T s i).2 • (Γ T s i).1.atSite (represent (t•harbor s⁻¹ (-(s⁻¹).act x) Z)) x=(T.beam i).atSite (represent (t•Z)) (0:Site n):=by rw [←looks,probe,←tilt_node, tilt_inverse]
 apply HasDerivAt.unique (f:=fun t:ℝ=> (T.beam i).atSite (represent (t•Z)) (0:Site n)) ?_ (slot_deriv ..); simp_rw [←ht]; exact (slot_deriv (Γ T s i).1 x (harbor s⁻¹ (-(s⁻¹).act x) Z)).const_smul (Γ T s i).2
variable (D:Floor P u.clip n a C)(h:0<a)(W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(Z:Sworn P n G)
-- true same momentum slope.
local notation "E"=> Vault (Plush G (denim n))
def divanF (f:(ι→G.Color)→ℝ) (r:ℝ):ℝ:=∫ x:E, f (r • pollen T 1 (0:Site n) (olive D h G x)) ∂stdGaussian _
include D h W A Z
lemma tenor(f:(ι→G.Color)→ℝ)(e:Continuous f)(r:ℝ): (∫ y:E,f (r • pollen T s x (olive D h G y))∂stdGaussian _)= divanF T D h f r:= by
 let Y:=pollen T s x; let V:=pollen T 1 (0:Site n); refine Artis.interest D h W A Y V (pollenTrend T s x) (pollenTrend T 1 0) ?_ ?_ (fun x=> f (r •x)) (e.measurable.comp (by fun_prop))
 · intro U; exact ⟨harbor s⁻¹ (-(s⁻¹).act x) U, funext fun i=> trace_inverse T i s x _,(chalice s⁻¹ _ D W A Z _).le⟩
 intro U; refine ⟨harbor s x U,funext fun i=>?_,(chalice s x D W A Z _).le⟩; exact (baseNeed T i _).trans (needleL T i s x _).symm -- tune
end Lumi
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Lumi.tenor
