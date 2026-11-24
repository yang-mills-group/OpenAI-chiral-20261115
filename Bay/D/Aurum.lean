import Bay.D.Cratelet
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
open Resonance Brecht Circuit
open CF.Onyx CF.Ember
open Stationary (Gaia)
open Maxwell

variable {N:Side}{k m R:ℕ}{A:Icey (Cella (More N))}
   {o b c:Seat N}
   {q:Clip}{H:Bed}{Z:PathData T4}{η C S:ℝ}
local notation "𝓷"=> (More N)
variable (B:Z.Bounds q η C S)(P:Attached H Z)
local notation "𝕊"=> stamen B P (More N)
local notation "Ⓣ" => stdGaussian (stamen B P (More N))
def beanCrop (w:Group3) :ℂ:=synopsis w
abbrev tata (F G:Dock (More N)→ℂ):Fin 3→Dock (More N)→ℂ:= ![F,G,F*G]

/-- clipped Gaussian estimate for signal (∆), star-mirror (∇), compound (∆∇) -/
def crop(ρ K:ℝ)(A:Icey (Cella (More N)))(b c:Seat N)(i:Fin 3):ℂ:=
 ∫ x:𝕊,
   tata (quay q ρ K A (forward b)) (star (quay q ρ K A (after c))) i x ∂ Ⓣ

lemma crop_forms(ρ K:ℝ)(A:Icey (Cella (More N)))(b c:Seat N):
 let f:=scrip K A (south B P b ρ)
 let g:=scrip K (creamM A) (north B P c ρ)
 crop B P ρ K A b c= ![∫ x:𝕊,f x∂ Ⓣ, ∫x,g x∂ Ⓣ, ∫x,f x*g x∂ Ⓣ]:=by
 intro f g
 funext i; fin_cases i
 · change (∫ x:𝕊,quay q ρ K A (forward b) x∂ Ⓣ)=∫x,f x∂ Ⓣ
   simp_rw[f,south_quay]
 · change (∫ x:𝕊,star (quay q ρ K A (after c) x)∂ Ⓣ)=∫x,g x∂ Ⓣ
   simp_rw[g,north_quay]
 · change (∫ x:𝕊,quay q ρ K A (forward b) x*star (quay q ρ K A (after c) x)∂ Ⓣ)=∫x,f x*g x∂ Ⓣ
   simp_rw[f,g,south_quay,north_quay]

variable {σ v ε f x ρ D d:ℝ}
/-- Signed/chamber target tolerant of per-component pressure loss and further limits.
Requires corruptions up to twice the pressure transfer.
-/
def CrownRank(x R ε lc:ℝ)(w:Group3):Prop:=
   ∀g:Group3, (∀i,‖g i-w i‖≤2*twB x)→ ‖ranked R g-lc‖≤ε

lemma aurum
 (h: Rake (Lagoon k o) f A)
 (y:H.covered σ v)(l:Floor H q (More N) D v)(a:0<σ)
 (u:Upbraid q σ v D m d)(t:0≤d)
 (e:ρ∈Set.Icc (1/2:ℝ) 2)(w:0<x)
 (g:Bore (More N) m k R o b c)
 (r:(R:ℝ)≤r_R x)
 (s:crust q f x + din f d ≤ ε):
 CrownRank x R ε (lscore ρ A) (crop B P ρ (bWindow x) A b c):=by
 let F:=crop B P ρ (bWindow x) A b c
 let T:= south B P b ρ
 let W:= north B P c ρ
 let J:= creamM A
 let α:= dip A (wick T)
 let β:= dip J (wick W)
 let γ:= dips A J (passes (hashes T W))
 let Q:Group3:=![α,β,α*β+γ]
 have hs: synopsis Q=γ:=by change α*β+γ-α*β=_; abel
 have ee: |ρ|≤2:= abs_le.mpr ⟨e.1.trans' (by norm_num),e.2⟩
 have p: 0 < bWindow x:=by unfold bWindow atRate;positivity

 have m₁:=south_norm B P b ρ ee
 have m₂:=north_norm B P c ρ ee
 obtain ⟨t₁,t₂,t₃⟩:= nick_fit q h.nonneg w

 have h₁:= mink h p m₁
 have h₂:= mink (cream_fee h) p m₂
 have h₃:= sable h (cream_fee h) p m₁ m₂

 intro G ht
 have hz:∀i,‖G i-Q i‖≤ nick q f x:=by
    intro i
    refine (norm_sub_le_norm_sub_add_norm_sub _ (F i) _).trans 
      ((add_le_add (ht i) le_rfl).trans ?_)
    unfold F
    rw[crop_forms]
    fin_cases i
    · exact (add_le_add le_rfl h₁).trans t₂
    · exact (add_le_add le_rfl h₂).trans t₂
    exact (add_le_add le_rfl h₃).trans t₃
 have h₄:‖α‖≤bigM q f:= wick_fee h (by unfold rivax;positivity) m₁
 have h₅:‖β‖≤bigM q f:= wick_fee (cream_fee h) (by unfold rivax;positivity) m₂
 have he:‖ranked R G-ranked R Q‖≤ crust q f x:=by
    have hv:=within3 Q G ((norm_nonneg _).trans h₄) t₁ h₄ h₅ hz
    rw[ranked,ranked,←mul_sub,norm_mul,norm_pow]
    have hi:‖(↑(R:ℝ):ℂ)‖≤ r_R x:=(Complex.norm_of_nonneg (Nat.cast_nonneg _)).trans_le r
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hi _) hv (norm_nonneg _) (by positivity)

 apply (norm_sub_le_norm_sub_add_norm_sub _ (ranked (R:ℝ) Q) _).trans
 apply le_trans _ s
 apply add_le_add he
 have rbn:=ribbon_LE e
 have ep:Even (More N).val:=⟨N.val,by change N.val*2=_;omega⟩
 rw[ranked,hs,lscore,Complex.ofReal_mul,Complex.ofReal_mul,
     Complex.ofReal_pow,Complex.ofReal_ofNat]
 exact woodworth h (rbn.1.le.trans rbn.2.1) rbn.2.2 (mul_nonneg (by norm_num) t)
    (fun _ i _ j=>gannet_pair B P u y l a ep ee (tine_here g i j))

abbrev reedR := r_R
def Aurum (q:Clip)(D σ v f x ε:ℝ)(m:ℕ):Prop:=
 ∀ (H:Bed)(Z:PathData T4){η C S:ℝ}(B:Z.Bounds q η C S)(P:Attached H Z){N:Side}
   {k R:ℕ}{o b c:Seat N}{ρ:ℝ}{A:Icey (Cella (More N))},
    H.covered σ v → Floor H q (More N) D v→ Rake (Lagoon k o) f A →
    Bore (More N) m k R o b c → (R:ℝ)≤reedR x → ρ∈Set.Icc (1/2:ℝ) 2 →
    CrownRank x R ε (lscore ρ A) (crop B P ρ (bWindow x) A b c)
theorem golden(q:Clip)(D σ v f ε:ℝ)(t:0<ε)(a:0<σ)(h:0<v):
    ∃ m,∀ᶠ x in atTop,Aurum q D σ v f x ε m:=by
 obtain ⟨d,r,u⟩:=din_le f _ (half_pos t)
 obtain ⟨m,p⟩:=gannets q a h D r
 refine ⟨m,?_⟩
 filter_upwards [crust_lim q f _ (half_pos t), eventually_gt_atTop (0:ℝ)] with x g gx H Z η C S B P N k R o b c ρ A l w j v r' z
 exact aurum B P j l w a p r.le z gx v r' ((add_le_add g u).trans (add_halves ε).le)
end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.golden
