import YM.SU5.Same.PoweredElection
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets
/-! # Bound all of the jets of the CP18 limit on the chosen vacuum.
    This step together with `powered_prism_labs` is toward unpadding. It is
    not about point values *at* 0, and not asserting an op estimate for the limit.
    Primes ultimately only service the actual SoldTrumpet ket as a vacuum field.
    See the construction notes to understand distinction from ingredient stencil
    scales. Do not infer a tempered boundary value of the actors themselves yet. -/

variable {H : Hilbert}{Y X:ℝ→H}
private lemma larger_power {n m:ℕ}{t C:ℝ}(p: 0 < t)(u:t ≤ 1)(h:n ≤ m)(w:t^n*‖Y t‖ ≤ C) : t^m * ‖Y t‖ ≤ C:=
 le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one p.le u h) (norm_nonneg _)) w
lemma TemperedAtEdge.addEdge (p:TemperedAtEdge H X)(u:TemperedAtEdge H Y) : TemperedAtEdge H (fun t=> X t+Y t):=by
 obtain ⟨m,C,h,c⟩:=p; obtain ⟨n,D,h',d⟩:=u; refine ⟨max m n,C+D,add_nonneg h h',fun t ht v=>?_⟩
 exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (pow_nonneg ht.le (max m n))).trans ((mul_add _ _ _).le.trans (add_le_add (larger_power ht v (le_max_left m n) (c t ht v)) (larger_power ht v (le_max_right m n) (d t ht v))))
lemma TemperedAtEdge.scaleEdge (p:TemperedAtEdge H X)(c:ℂ): TemperedAtEdge H (fun t => c • X t):=by
 obtain ⟨m,C,h,d⟩:=p; refine ⟨m, ‖c‖*C,mul_nonneg (norm_nonneg _) h,fun t u q=>?_⟩; rw [norm_smul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (d t u q) (norm_nonneg _)
lemma TemperedAtEdge.sum {ι:Type*}(f:ι→ℝ→H)(s:Finset ι)(u:∀ i,TemperedAtEdge H (f i)): TemperedAtEdge H (fun t=> ∑ i∈s,f i t):=by
 classical
 induction s using Finset.induction_on with
 | empty=> refine ⟨0,0,le_rfl,fun t v q =>?_⟩; simp
 | @insert i s h ih=> simp_rw [Finset.sum_insert h]; exact (u i).addEdge ih

variable {j:Axis}(S:OS.Semigroup H j)
lemma deriv_heat_cost (z:ℂ) (w:0<z.re) : ‖deriv S.F z‖ ≤ 1 / (z.re/2):=by
 apply CF.Floral.c_deriv (AnalyticOnNhd.differentiableOn S.localHeat) (half_pos w) _ (fun z h=> S.norm_row h); intro x p
 apply (half_pos w).trans_le (?_ : z.re/2≤x.re); have he: _≤ z.re/2:= mem_closedBall.mp p; rw [dist_eq_norm] at he; have hx:= (abs_le.mp ( (Complex.abs_re_le_norm (x-z)).trans he)).1; rw [Complex.sub_re] at hx; linarith
lemma jet_at_edge (p: Positive S X)(u:TemperedAtEdge H X): ∀ i:ℕ,TemperedAtEdge H (fun t:ℝ=>jet S X i (t:ℂ)):=by
 intro i; induction i with
 | zero=> obtain ⟨m,C,h,t⟩:=u; refine ⟨m,C,h,fun s u v=>?_⟩; unfold jet; simp only [iteratedDeriv_zero, SatinJets.lifted_heat S X p u]; exact t s u v
 | succ i ih =>
   obtain ⟨m,C,h,w⟩:=ih; refine ⟨m+1, (2^(m+1):ℝ)*(2*C), by positivity,fun s u v=>?_⟩
   let t:ℝ:=s/2; have ht:0<t:= half_pos u; let F:=jet S X i (t:ℂ)
   let T₁:=S.F
   have he: ‖jet S X (i+1) s‖ ≤ (1/(t/2)) * ‖F‖:=by
      have hx: (s:ℂ)=(t:ℂ)+(t:ℂ):=by rw [←Complex.ofReal_add]; unfold t; ring_nf
      rw [hx, jet_tick S X p i _ _ ht ht]; exact ((deriv S.F (t:ℂ)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (deriv_heat_cost S (t:ℂ) ht) (norm_nonneg _))
   apply (mul_le_mul_of_nonneg_left he (pow_nonneg u.le (m+1))).trans
   have hx:t^m*‖F‖ ≤ C:= w t ht ((half_lt_self u).le.trans v)
   rw [show s^(m+1) = 2^(m+1)*t^(m+1) by nth_rw 1 [show s=2*t from by unfold t; ring]; rw [mul_pow], mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
   calc t^(m+1)*(1/(t/2)*‖F‖)= 2*(t^m*‖F‖):= by field_simp; ring
        _ ≤ 2*C:= by linarith only [hx]
lemma prism_at_edge (p:Positive S X)(u:TemperedAtEdge H X)(W:Prism): TemperedAtEdge H (prism S X W):=by
 rw [show prism S X W= fun t:ℝ=>∑ i∈W.support, W i • jet S X (i+1) (t:ℂ) from funext fun _ => prism_ret S X W]; exact TemperedAtEdge.sum (fun i (t:ℝ)=> W i • jet S X (i+1) (t:ℂ)) W.support fun i=> (jet_at_edge S p u (i+1)).scaleEdge _

variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Ε"=> P.seasons 3 ξ
local notation "π'"=> P.wealth 3 ξ
variable (A:ℕ→ P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ SatinJets.Prism)(z:Lead.Clan)
variable (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
variable (Y:P.HandleWith x c r A n)
local notation "T" => P.ThinArmada x A c r n w Y V g h
lemma prior_temper (p:PoweredHeat P x V): TemperedAtEdge H (P.route_before z x V):= (p 3 []).scaleEdge _
lemma prism_both_edges (p:PoweredHeat P x V)(U:T) : TemperedAtEdge H (P.profilesH x w z V)∧ TemperedAtEdge G (P.profilesZ x V w z):=by
 let R₁:= P.profilesH x w z V; let R₂:= P.profilesZ x V w z
 have hv:TemperedAtEdge H R₁:= prism_at_edge S (U.fusion.profile z) (P.prior_temper x z V p) (w z)
 refine ⟨hv,?_⟩; obtain ⟨m,B,h',u⟩:= hv; refine ⟨m,‖π'‖ * B,mul_nonneg (norm_nonneg (π')) h',fun t f ht=>?_⟩
 have hb:π' (R₁ t)=R₂ t:=P.illuminate_bank x A c r n w V g h Y U z t f
 change t^m*‖R₂ t‖≤_; rw [← hb]; apply (mul_le_mul_of_nonneg_left ((π').le_opNorm _) (pow_nonneg f.le m)).trans; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (u t f ht) (norm_nonneg (π'))

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.prism_both_edges
