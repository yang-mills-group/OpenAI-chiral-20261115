import YM.SatinExist.Dovecote
/-!
 # Each stencil lab on a field union. Budget strict product authority.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry TopologicalSpace
namespace Spine
open Aria Casting
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld LineDeriv
open _root_.YM.Boundary Spectral Poin
open SatinTails SatinJets Ballad
variable (P:Spine) (x:P.Spectrum0 3) (A:ℕ→P.Apron) (j:Axis)
local notation "ξ"=>P.advocate 3 x j
local notation "CX"=> P.ManyF j (P.advocate 3 x j)
local notation "ν"=> P.seasons j (P.advocate 3 x j)
local notation "λ'"=> P.ColorHil j (P.advocate 3 x j)
local notation "ω"=> P.heaven j (P.advocate 3 x j)
local notation "g"=>P.pillar j (P.advocate 3 x j)
local notation "G"=> P.cartage j (P.advocate 3 x j)
local notation "Φ"=> Bench (P.seasons j (P.advocate 3 x j))
local notation "η"=> (P.seasons j (P.advocate 3 x j)).E
local notation "T"=> M (P.seasons j (P.advocate 3 x j))
local notation "K"=> Cache (P.seasons j (P.advocate 3 x j))
local notation "χ" i:max J:max=> (A i).pivot P J
section Morph
variable (F:(P.ManyF j (P.advocate 3 x j)).Op) (r:ℕ)
variable (l:List Axis) (U:ℝ → (P.ManyF j (P.advocate 3 x j)).Op)(t:P.ActualScarab x A j l U)(h:RealMint (P.seasons j (P.advocate 3 x j)) r U F)
lemma reflectsW (i:ℕ)(l:List Axis)(u:ℝ): g (χ i (j::l)) (-u) u 0= star (g (χ i l) (-u) u 0):=by
 rw [Apron.pivot_cons]; unfold pillar; let Y:= χ i l; let B:=Y.engine P j ξ; let C':=Y.realWidth P j; let Q:=η (u-C').toNNReal; have ht: star Q= Q:= (ν).sym _
 unfold Apron.time_panel Apron.time_edge; simp only [Pi.zero_apply, zero_sub,zero_add, neg_sub_neg]
 change Q*(P.tableau j ξ 0 ((Y.kiss P j).engine P j ξ)*Q)=star (Q*(P.tableau j ξ 0 B *Q)); rw [star_mul,star_mul, ht, P.lives_twin]; rw [show mirrorΩ j 0=0 from ?_]; simp only [mul_assoc]
 funext x; by_cases x=j <;> simp [mirrorΩ, *] -- parse
include t h
lemma mirror_mint (V:ℝ→(P.ManyF j (P.advocate 3 x j)).Op)(Q:P.ActualScarab x A j (j::l) V): RealMint (ν) r V (star F):=by
 intro s p
 have he := (Q.prices.paid s (show (0:ℝ)<s from p))
 have ht := (t.prices.paid s (show (0:ℝ)<s from p))
 simp_rw [one_smul] at ht he
 rw [show V s=star (U s) from ?_,h s p, star_mul, star_mul,(parRev (ν) _ _ p).star_eq,mul_assoc]
 apply he.uniqueR; exact ht.starR.sameC (Eventually.of_forall fun i=>(P.reflectsW x A j _ _ _).symm) rfl
lemma reflected_mink (L:(CX).Op)(n:ℕ)(V:ℝ→(P.ManyF j (P.advocate 3 x j)).Op)(Q:P.ActualScarab x A j (j::l) V)(R:RealMint (ν) n V L) (f:Test4) : ℑ (ν) L f n= ℑ (ν) (star F) f r:=by
 have hp:=P.mirror_mint x A j F r l U t h V Q
 rw [price_same (ν) n L r f, show (K r*L*K r)=(K n*(star F)*K n) from ?_,add_comm, ← price_same]
 apply mint_unique (ν) (r+n) V _ _ (R.increases _ _ _ _ r); rw [add_comm]; exact hp.increases _ _ _ _ n -- include tune
end Morph

structure PowerNames (P:Spine) (x:P.Spectrum0 3) (A:ℕ→P.Apron):Type where
 rate (a:Axis) : List Axis → ℕ
 fields (a:Axis) : List Axis → (P.ManyF a (P.advocate 3 x a)).Op
 trace (a:Axis)(l:List Axis) : ℝ → (P.ManyF a (P.advocate 3 x a)).Op
 price(a:Axis)(l:List Axis) : ActualScarab P x A a l (trace a l)
 paid(a:Axis)(l:List Axis) : RealMint (P.seasons a (P.advocate 3 x a)) (rate a l) (trace a l) (fields a l)
lemma naming (p:∀ j l,∃ U, P.ActualScarab x A j l U): Nonempty (P.PowerNames x A):=by
 choose f g' U h k using fun j l=> P.wanna x A j l (p j l); exact ⟨⟨f,g',U,h,k⟩⟩

variable (V:P.PowerNames x A)
local notation "F"=>V.fields j
local notation "Ψ"=> V.trace j
local notation "r"=> V.rate j
abbrev PowerNames.action (l:List Axis) : Test4 →ₗ[ℂ] ((Bench (P.seasons j (P.advocate 3 x j))) →ₗ[ℂ] (Bench (P.seasons j (P.advocate 3 x j)))):= σV (ν) (V.fields j l) (V.rate j l) -- order
local notation "W"=>PowerNames.action P x A j V
lemma PowerNames.adj_rule (l:List Axis)(f:Test4)(X Y:Bench (P.seasons j (P.advocate 3 x j))):inner ℂ ((PowerNames.action P x A j V l f X).val) Y.val = inner ℂ X.val ((PowerNames.action P x A j V (j::l) (Probe.bar f) Y).val) :=by
 change inner ℂ (ℑ (ν) _ _ _ X).val _=inner ℂ X.val (ℑ (ν) _ _ _ Y).val
 rw [P.reflected_mink x A j (V.fields j l) _ l _ (V.price j l) (V.paid j l) _ _ _ (V.price j (j::l)) (V.paid j (j::l)) (Probe.bar f)]
 exact sees_κ ..
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
