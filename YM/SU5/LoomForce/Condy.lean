import YM.SU5.LoomForce.FingerMosaic
import YM.SU5.LoomForce.Rally
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
open Next.Rank Spindle
open Buffered Pannier Pannier.Chancel Rous Afterglow
open Py Py.Rate Py.Rate.LocalLimit Preparation Preparation.Yoke
open Afterglow.Tower.VacuumSelection.Spine Afterglow.Tower.VacuumSelection.Spine.LoomForce
open Gleam Gleam.Wake Regis Regis.Head Regis.Head.Brecht Regis.Circuit Precision
open ProbabilityTheory Regis.Wake Exterior
variable {P: Preparation}{j:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus j))(s i n B:ℕ)
variable (R:ℤ)(x:Site (Journey.side Y i s))
local notation "F_"=> readingFob B R x
local notation "N"=> Journey.side Y i s
local notation "τ"=> Panels B
local notation "vθ"=> Sheds B
local notation "M_"=> Y.uv n-s
local notation "Θ"=> P.V.L.mood (Y.uv n - s)
local notation "Υ"=> P.V.L.tied (Y.uv n - s)
local notation "M"=> P.V.L.H (Y.uv n - s)
local notation "Pθ"=> P.K.top.clip
local notation "ϵ"=> stamen (P.V.L.mood (Y.uv n - s)) (P.V.L.tied (Y.uv n - s)) (More (Journey.side Y i s))
variable (W:ℝ)-- reach factor
local notation "φ" R:max b:max x:max => readingFob b R x
lemma roller1(z:ϵ)(G: (τ→ℝ)→ℂ): (F_).basin W G Pθ z.val=G fun i=> W*Etch.river Pθ ((F_).ua i) z.val ((F_).lens i):=by
 obtain ⟨a,rfl⟩:= (tiler Θ Υ (n:= More N)).surjective_rangeRestrict z; rw [show ((tiler _ _).rangeRestrict a).val=_ from (show ((tiler Θ Υ).rangeRestrict a).val=(tiler Θ Υ) a from rfl), Vessel.belly]; apply congrArg G; funext i; rw [Etch.river_now Pθ Θ Υ]

abbrev bodyV (x:Site (Journey.side Y i s)) (R:ℤ)(B:ℕ)(z:Panels B): Body 2 (More (Journey.side Y i s)):= ((readingFob B R x).origin z,plaquette ((readingFob B R x).ua z).2)
noncomputable def rawLight (z:τ):ϵ:= W • trill Θ Υ ((F_).lens z) (bodyV Y s i x R B z)
lemma readBody (z:ϵ)(u:τ): inner ℝ (rawLight Y s i n B R x W u) z=W * Etch.river Pθ ((F_).ua u) z.val ((F_).lens u):=by
 let B':=(F_).ua u; let α:= bodyV Y s i x R B u; let A:ϵ:= trill Θ Υ ((F_).lens u) α
 change inner ℝ (W • A) z=W* _; refine (real_inner_smul_left A z W).trans (congrArg (W * ·) ?_)
 have ht: beamZ Θ Υ α z= Etch.river Pθ B' z.val:= inspire Θ Υ B'.2 B'.1 z
 exact (joy Θ Υ ((F_).lens u) α z).trans (congrArg (fun t:SU.group.Color=> t ((F_).lens u)) ht)
variable {a b d t w v:ℝ}{r k:ℕ} {Z T :SOp (Journey.side Y i s)}
variable (m:ℝ)(h: 2*(B+1)<(More (Journey.side Y i s)).val)(E:Pattern Z T r d a v) -- Z overloaded
local notation "K"=> rawLight Y s i n B R x W
abbrev sailDir {B:ℕ}(x:Bool)(i: Sheds B) :ℝ:= if x then realDir i.1.val.2 else 1
noncomputable def springLight (a:Bool)(u:vθ):ϵ:= m^2 • sailDir a u • K (a,u)
local notation "D"=> springLight Y s i n B R x W m
local notation "ℓ" b:max => polynomialPad B h x E k (m^4) b
local notation "F"=> cashY B h x E k
local notation "A_" b:max => fun z:ϵ=> ζPay b (Finger.account F (fun i=> inner ℝ (D b i) z))
lemma taxBody (a:Bool)(z:ϵ): (F_).basin W (ℓ a) Pθ z.val = (A_ a) z := by
 let U:Panels B→ℝ:= fun i=>W * Etch.river Pθ ((F_).ua i) z.val ((F_).lens i); let f:=F; let G' := fun p:Sheds B→ℝ=>Finger.account f p
 rw [roller1]; have hp (i:vθ): inner ℝ (D a i) z= m^2 * peeler B a U i:=by
    rw [springLight,real_inner_smul_left _ z (m^2),real_inner_smul_left _ z (sailDir a i),readBody]; unfold sailDir peeler; cases a; simp only [Bool.false_eq_true,ite_false,one_mul]; rfl; rfl
 unfold polynomialPad; change (↑(m^4:ℝ):ℂ)*ζPay a (G' (peeler B a U)) = ζPay a (G' _)
 rw [show (fun i:vθ=> inner ℝ (D a i) z)=m^2 • peeler B a U from funext hp]; rw [show G' (m^2 • _) = _ from evaluator_roll B h x E k (m^2) (peeler B a U)] -- maybe need infer?
 cases a
 · unfold ζPay; simp only [Bool.false_eq_true,ite_false]; change _*G' _=(↑(m^2:ℝ):ℂ)^2*G' _; push_cast; ring
 unfold ζPay; simp only [ite_true]; push_cast; change (m:ℂ)^4 *star (G' _) = star ( ((m:ℂ)^2)^2 * G' _ ); rw [star_mul',star_pow,star_pow,show star (m:ℂ)=(m:ℂ) from Complex.conj_ofReal _]; ring
#check @rawLight
local notation "Rμ"=> reachCost Y s i n W
local notation "Sμ"=> springLight Y s i n B R x Rμ m
local notation "Pν" b:max=> seatT Y s i n F_ (ℓ b) W
local notation "Vν" => seatT Y s i n F_ ( (ℓ true)*(ℓ false) ) W
local notation "ξ"=> stdGaussian ϵ
local notation "ς"=> F_
local notation "Q_" u:max=> bodyV Y s i x R B u
local notation "Σ0" x:max=> sailDir true x
local notation "E0" a:max=> reachCost Y s i n a

noncomputable def crossFee (u v:vθ):ℂ:= ((m:ℂ)^4*((sailDir true u):ℂ)*(reachCost Y s i n W:ℂ)^2)* (sch (G:=SU.group) u.2 v.2 :ℂ)*rimble (More N) M (bodyV Y s i x R B (true,u)) (bodyV Y s i x R B (false,v))
lemma earTrace (u v:vθ): WickG.grainG (Sμ true u) (Sμ false v)= crossFee Y s i n B R x W m u v:=by
 let a:= (true,u); let b:= (false,v); let X:=Q_ a; let Z:=Q_ b
 obtain ⟨B',w,-⟩:=P.V.L.roof (Y.uv n-s)
 have h:= chimes Θ Υ (w _) B' P.K.width u.2 v.2 X Z (show Even (More N).val from ⟨(N).val, mul_two _⟩) -- notation shadow
 simp_rw [←joy,appraisal] at h
 let A:ϵ:=trill Θ Υ u.2 X; let Z':ϵ:= trill Θ Υ v.2 Z; let t:=reachCost Y s i n W; let b:=sailDir true u
 have he(x y:ϵ)(i j a b c d:ℝ): (↑(inner ℝ (a • c • i • x) (b • d • j • y)):ℂ)= (a:ℂ)*(b:ℂ)*(c:ℂ)*(d:ℂ)*(i:ℂ)*(j:ℂ)*(↑(inner ℝ x y):ℂ):=by
    rw [real_inner_smul_left (c • i • x) _ a, real_inner_smul_left (i • x) _ c, real_inner_smul_left x _ i, real_inner_smul_right x (d • j • y) b,real_inner_smul_right x (j • y) d,real_inner_smul_right x y j]; push_cast; ring
 change WickG.grainG (m^2 • b • t • A) (m^2 • sailDir false v • t • Z')= _; unfold WickG.grainG; rw [he,show sailDir false v=1 from rfl, show (↑(inner ℝ A Z'):ℂ)= _ from h]; change _= ((m:ℂ)^4*(b:ℂ)*(t:ℂ)^2)* (sch (G:=SU.group) u.2 v.2:ℂ)*rimble (More N) M X Z; push_cast; ring

lemma valuation : Vν-Pν true*Pν false= Finger.Ledger (cashY B h x E k) (crossFee Y s i n B R x W m):=by
 rw [show crossFee Y s i n B R x W m= fun u v=> WickG.grainG (Sμ true u) (Sμ false v) from funext₂ fun i j=> (earTrace Y s _ n B R x W m i j).symm,←Finger.bookFull];
 unfold seatT; simp only;
 let f(q:Bool)(v:ϵ):= (F_).basin Rμ (ℓ q) Pθ v.val
 change (∫ x, f true x*f false x∂ξ)-(∫ x,f true x∂ξ)*(∫ x,f false x∂ξ) = _
 unfold f; simp_rw [taxBody]; rfl
#print axioms valuation
end YM.CF.LitCurrent.Surplus
