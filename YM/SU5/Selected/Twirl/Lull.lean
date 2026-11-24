import YM.SU5.Selected.Twirl.Spice
import YM.SU5.Selected.Twirl.Pearl
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
open Stencil (pulseNode pval)
open Rubric
open Afterglow Afterglow.Tapestry
attribute [local instance] opCStarAlgebra
-- narrow neutral algebra including products. Need separate ambient eval & comm proof. keep support. Compare Nation.
open Commission
namespace Mezz
set_option synthInstance.maxSize 26000
attribute [local instance] opCStarAlgebra
namespace Grant
open Sermon Tower.SlabMark
-- Pricing secant and gauge independence on same marked candidate and ONE χ. For any t:Family K→ℂ: need Scopes at every X charged/wide (read χ).
variable (A:Mezz)(K:Calibration){W:Window.Family}(F F':Sermon A K W) (e:A.Legate)(s:Finset A.Lot)(d:A.BlockDay)(b:Bool)
variable {T:Buffered.Family K → ℂ}
local notation "X"=> A.Broad
local notation "κ"=> A.Zumba
local notation "U"=> A.coast_b true
local notation "R"=> A.coast_b false
local notation "L" b:max=> quarry A K d b
local notation "r₀" b:max=> quay A K d b
local notation "η" i:max=> embrace A K e i s
local notation "Θ" i:max=> (stage_at A K F F' i)
local notation "V" x:max y:max=> glaze A K F F' e s d x y
variable {c:ℕ}(S:Duet K A c F F')(φ:∀ s,Scopes K s T)
local notation "L'" b:max x:max y:max w:max=> icing A K F F' e s d b x y w d
local notation "b₀"=> d.val
local notation "past"=> (Θ b₀)
local notation "forward"=> (Θ (b₀+1))
local notation "ξ" i:max=> η (Θ i)
local notation "Π" b:max x:max y:max=> T (L' b x y c)
local notation "Φ" x:max y:max=> T (V x y).val
local notation "η₀" f:max=> T (η f).val
local notation "ρ" b:max f:max=> tripty A K f e s d b c
include S φ e
lemma locus_x (f:addgap K ≤ A.ℓ.val) (u:Sermon A K W): InTest K true ((L b) ∪ plow K 3 c (r₀ b)) false (ρ b u):= InTest.mul ( ((quarry_x A K u e s d b f).widen).mono subset_union_left) ((Tower.flow_port K 3 _ (quay_x A K u e s d b f).widen).mono subset_union_right)
-- Scopes. define numeric signs knots. Knows coherent regular.
omit S φ e
local notation "β"=> portion A /8
private lemma tilt_l {i: ℝ}(a b w:ℂ)(t:i < ‖a-b‖): i/2 < ‖a-w‖ ∨ i/2<‖b-w‖:=by
 by_contra! p
 rw [show a-b=(a-w)-(b-w) from by abel] at t; linarith [p.1,p.2,norm_sub_le (a-w) (b-w)]
private lemma tilt_f {i:ℝ}(c d:ℂ)(t:i<‖c‖): i<‖c+d‖ ∨ i<‖c-d‖:=by
 by_contra! p; have ht: ‖(2:ℂ)*c‖ ≤ ‖c+d‖ + ‖c-d‖:=by rw [show 2*c=(c+d)+(c-d) from by ring]; exact norm_add_le ..
 rw [norm_mul,show ‖(2:ℂ)‖=(2:ℝ) by norm_num] at ht; linarith [p.1,p.2]
def sponsorT (x:ℂ): Prop:= x=0 ∨ x=1 ∨ x=-1
lemma sponsorPay {x:ℂ}(t:sponsorT x): ‖x‖≤ 1:=by rcases t with t|t|t <;> subst x <;> simp
private lemma tilt_h {i:ℝ}(p:0 ≤ i)(z a q b:ℂ)(t:i< ‖z-a‖)(s:i/2<‖q‖): ∃ x y:ℂ,sponsorT x∧ sponsorT y ∧ i/8 < ‖x*z+y*a‖ ∧ i/8< ‖x*q+y*b‖:=by
 have hp:= tilt_f q b s; have e:i/8< ‖q‖:= (by linarith); by_cases f: i/8< ‖z‖; exact ⟨1,0,Or.inr (Or.inl rfl),Or.inl rfl,(by simpa using f),(by simpa using e)⟩;
 have hu:i/8< ‖z+a‖:= by
    rw [show z-a=z+z-(z+a) from by abel] at t; linarith [norm_sub_le (z+z) (z+a),norm_add_le z z] -- covers negation
 obtain ht|ht:=hp; exact ⟨1,1,Or.inr (Or.inl rfl),Or.inr (Or.inl rfl),(by simpa using hu), (by simp; linarith only [p,ht])⟩
 exact ⟨1,-1,Or.inr (Or.inl rfl),Or.inr (Or.inr rfl),(by rw [one_mul,neg_one_mul,←sub_eq_add_neg]; linarith only [t,p]),(by rw [one_mul,neg_one_mul,←sub_eq_add_neg]; linarith only [ht,p])⟩
-- headline flag for T on all. grants. marble counts. Explicit F→F' alignment on manufacturing at positive time amount. ç. norm bound delta.
include S φ e
variable (f:addgap K≤ A.ℓ.val)
include f
lemma expectation_b (x y:ℂ): Φ x y=x* (η₀ past)+y*(η₀ forward)∧ Π b x y=x*T (ρ b past)+y*T (ρ b forward):=by
 let g:= Sermon.transit A K (φ (X)); constructor; exact g.map_add (x • ξ b₀) (y • ξ (b₀+1))|>.trans (congrArg₂ (·+·) (map_smul g ..) (map_smul g ..)) -- parent issue `|>` term and map_smul fully applied twice? tune
 let p':= φ ((L b)∪ plow K 3 c (r₀ b)); let a:= locus_x A K F F' e s d b S φ f past; let a':= locus_x A K F F' e s d b S φ f forward; unfold icing; rw [p'.plus_v _ _ (a.smul x) (a'.smul y),p'.scale _ a,p'.scale _ a']; rfl -- tune
omit f S φ
structure Divert (r c:ℕ)(T:Buffered.Family K→ℂ)(x y:ℂ):Prop where
 count : s.card=Stencil.load r
 sponsor: sponsorT x ∧ sponsorT y
 actual: portion A/8< ‖T (V x y).val‖ -- `V` cap operative; potential `V` notation
 reveals: ¬Challenged K W (κ) U R X (10*s.card) (10*s.card) s.card T
 tilt: portion A/8< ‖T (V x y).val-T (L' b x y c)‖
#print Divert.mk
local notation "z"=> η₀ past
local notation "z'" => η₀ forward
local notation "Z₁" b:max=> T (ρ b past)
local notation "Z₂" b:max=> T (ρ b forward)
include S φ f
lemma occurs (t: portion A < ‖(z)-(z')‖)(r:ℕ)(hp:s.card=Stencil.load r):∃ (b:Bool)(x y:ℂ), Divert A K F F' e s d b r c T x y:=by
 let v:= portion A; have h:0<v:= fortune A
 have he:= rounds A K F F' e s d S; let α(b:Bool)(x y:ℂ):= Divert A K F F' e s d b r c T x y; have hv(x y:ℂ)(b:Bool)(k:sponsorT x)(q:sponsorT y)(p:v/8< ‖x*z+y*z'‖)(u:v/8<‖x*((z)-(Z₁ b))+y*((z')-(Z₂ b))‖) : α b x y:=by
    obtain ⟨l,t⟩:= expectation_b A K F F' e s d b S φ f x y; have p': portion A/8 < ‖Φ x y‖:= (by rw [l]; exact p); refine ⟨hp,⟨k,q⟩,p',fun Q=>norm_pos_iff.mp (lt_trans (by change 0<v/8; linarith) p') (promises (φ (X)) ?_ ?_ (glaze_mar A K F F' e s d x y) Q), ?_⟩ -- norm not type placeholder
    · unfold cameo; simp
    · rw [hp]; unfold Stencil.load; omega
    rw [l,t]; rw [mul_sub,mul_sub] at u; rw [add_sub_add_comm]; exact u -- `u` ring
 obtain k|k:= tilt_l (z) (z') (T (ρ false past)) t; · obtain ⟨x,y,v₁,v₂,l,e⟩:= tilt_h h.le (z) (z') ((z)-Z₁ false) ((z')-Z₂ false) t k; exact ⟨false,x,y,hv x y false v₁ v₂ l e⟩
 rw [he] at k; obtain ⟨x,y,l,l',e,hg⟩:= tilt_h h.le (z') (z) ((z')-Z₂ true) ((z)-Z₁ true) (t.trans_eq (norm_sub_rev ..)) k; exact ⟨true,y,x,hv y x true l' l (by rw [add_comm]; exact e) (by rw [add_comm]; exact hg)⟩
lemma hands (p: ‖T (F.solitude A K e).val‖ < 1/2)(q:‖T (F'.solitude A K e).val‖ <1/2) : ∃ (s:Finset A.Lot)(n:ℕ)(d:A.BlockDay)(b:Bool)(x y:ℂ),n<A.vowP ∧ Divert A K F F' e s d b n c T x y:=by obtain ⟨n,s,d,h,v,k⟩:= prize_day A K F F' e S T (φ X) p q; obtain ⟨b,x,y,h⟩:= occurs A K F F' e s d S φ f k n v; refine ⟨s,n,d,b,x,y,?_,h⟩; assumption
end Grant
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz.Grant
#print axioms occurs
#print axioms Divert.tilt
#print axioms hands
#print axioms expectation_b
#print axioms sponsorPay
