import YM.SU5.FiniteGaugeData.Tower.Reflect
import YM.CF.Buffered.Application
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)

/-!
# Fixed-separation candidate (reader diagnostic, Base + Control + Reflect)

K0's vertex R≥1 once and for all, before period, cutoff removal (chosen
from ordered Λ and l). At level **zero**, units of level-zero fermion spacing,
line length R with gauge and the 5 slots of generation zero in the shared
generation system. E is the limiting functional of this election; tests at
higher fixed levels have separation in THOSE levels' lattice units. Here is a
direct reduction of the conclusion on these words, quantitative and even with
finite centering, needing only finite word estimates on this actual course
(no Printed; only need them cofinally along the Crimson strip).

Witness meaning: This is the `Buffered` corollary's actual word. Do *not*
interpret its comparison or connected reflected cost as a non-Wick estimate:
`Application.P20` is a Weyl kernel component and `compared` is the Wick
comparison value (`Buffered/Fluxion.lean`). A gauge test with matter letters
doesn't automatically distinguish an interacting state from a free one; nor
does an unselected connected reading automatically exclude vacuum mixtures.
See the additional criteria separately.
-/
open Bilinear Fock
section support
variable (K':Calibration)
local notation "S₀"=> Bilinear.support K'
local notation "w"=> word K'
local notation "θ"=> thetaK K'
variable (wide:Bool)
lemma linked_clear :goodSet K' (S₀):=by
 intro x p
 obtain ⟨r,_,rfl⟩:= Cube.range_leg _ (posDir 3) (2*K'.vertex) _ (List.mem_toFinset.mp p)
 have h:K'.plane0+(K'.ℓ:ℤ) ≤ 0:=by
    let d:=K'.vertex/(2*K'.B.val)
    have ht: 2*K'.ℓ ≤ 4*K'.B.val*d:= K'.line
    have hv: K'.plane0 = -(↑(4*K'.B.val*d):ℤ) := by unfold Calibration.plane0 Heat.gaugeShift; unfold Calibration.ζ d; simp only [Nat.cast_mul,Nat.cast_ofNat]; ring
    rw [hv]; omega
 refine h.trans ?_
 simp [Lifted.nodeC,creatorSite]; omega

lemma linked_in : InTest K' wide (Bilinear.support K') false (word K'):=by
 -- Word.prodWord with explicit support
 have ht: Lifted.nodeC (removerSite K')∈Bilinear.support K':=by
    rw [←end_node,Bilinear.support,List.mem_toFinset]
    apply show ∀ s : Cover, ∀ l:Walk, stop s l∈visits s l from ?_
    intro s l; induction l generalizing s <;> simp_all [stop,visits]
 have he:Lifted.nodeC creatorSite∈ Bilinear.support K':=by
    cases e : Bilinear.segment K' <;> simp [Bilinear.support,e, visits]
 refine .smul _ (InTest.sum _ _ fun p _=> InTest.sum _ _ fun q _ =>.mul (.seed (Coeff.fromC _ _ ?_ ?_)) (.mul (.remover q (by decide) ht) (.creator p (by decide) he)))
 · exact (matter_cont.comp (Wilson.continuous_travel _ _)).matrix_elem p q
 intro X Y h; unfold D5; exact congrArg (fun t:SU.E=> (matter t).val p q) (travel_local _ _ X Y (fun l u v=> h l (List.mem_toFinset.mpr u) (List.mem_toFinset.mpr v)))

-- norms on all period fields, even with no Hosp
noncomputable def price_w (K':Calibration):ℝ:=‖-((K'.vertex:ℂ)^3/5)‖*(five.card*five.card)
lemma linked_pay : pay (word K') (price_w K'):=by
 let F(p q:SU.Slot):Family K':= Buffered.scalar K' ((D5 K' p q) ∘ Prod.fst) * (removal K' (removerSite K') 2 q * creation K' creatorSite 0 p)
 let u(p:SU.Slot):Blot:=(creatorSite,0,p); let v(q:SU.Slot):Blot:=(removerSite K',2,q)
 have hp(p q:SU.Slot):pay (F p q) 1:=by
    have ha:pay (Buffered.scalar K' ((D5 K' p q) ∘ Prod.fst)) 1:=by
       intro t x; change ‖D5 K' p q _ • (1:FC (Single (K'.c t)))‖≤_
       rw [norm_smul,norm_one,mul_one]; exact (norm_entry ..).trans_eq (CStarRing.norm_of_mem_unitary (matter _).property)
    have ht:removal K' (removerSite K') 2 q=Sound.chord K' (v q):= by rw [Sound.chord,if_neg (show (2:SpinIdx)∉plusHalf from by decide)]
    have hs:creation K' creatorSite 0 p=Sound.chord K' (u p):= by rw [Sound.chord,if_pos (show (0:SpinIdx)∈plusHalf from by decide)]
    unfold F; rw [hs,ht]
    have t:pay (Sound.chord K' (v q)) 1:= fun t x=> moderate K' t x _
    have l:pay (Sound.chord K' (u p)) 1:= fun t x=> moderate K' t x _
    simpa only [one_mul] using pay_mul ha (pay_mul t l)
 let c : ℂ := -((K'.vertex:ℂ)^3 / 5); let d : ℝ := five.card*five.card; change pay (c • (∑ p∈five,∑ q∈five,F p q)) (‖c‖*d); refine pay_scale (F:=∑ p∈five,∑ q∈five, F p q) (A:=d) ?_ c
 intro t x; simp_rw [Finset.sum_apply]; apply (norm_sum_le ..).trans; calc
    (∑ p∈five,‖∑ q∈five,F p q t x‖) ≤∑ p∈five,∑ q∈five,(1:ℝ):= Finset.sum_le_sum fun p _=> (norm_sum_le ..).trans (Finset.sum_le_sum fun q _=> hp p q t x)
    _= _:=by simp [d]

-- boxes for each centered version and product, no claims of uniform
-- thresholds when separation R varies
abbrev pairBox:= S₀ ∪ reflectedBox 3 K'.plane0 (S₀)
def center (f:Family K')(a:ℂ) : Family K':= f-a • 1
lemma candled (x:ℂ):InTest K' wide (S₀) false (center K' w x):= InTest.subOp (linked_in ..) (.smul _ InTest.one)
lemma cent_el (x:ℂ): Eligible K' wide (center K' w x):= (eligible K' wide).sub_mem (allowed K' wide) ((eligible K' wide).smul_mem _ Eligible.oneT)
lemma candled_rate (x:ℂ):pay (center K' w x) (price_w K'+‖x‖):=by unfold center; simpa using pay_sub (linked_pay K') (pay_scale pay_unit x)
lemma pair_in (x y:ℂ): InTest K' wide (pairBox K') false (θ (center K' w x)*center K' w y):= .mul (((candled K' wide x).reflection _).mono subset_union_right) ((candled K' wide y).mono subset_union_left)
lemma raw_pair_in: InTest K' wide (pairBox K') false (θ w*w):=by have e:= pair_in K' wide 0 0; simpa [center] using e
lemma pair_pay (x y:ℂ):pay (θ (center K' w x)*center K' w y) ((price_w K'+‖x‖)*(price_w K'+‖y‖)):= pay_mul (pay_ref (candled_rate K' x) _) (candled_rate K' y)
lemma raw_pair_pay:pay (θ w*w) (price_w K'^2):=by simpa [sq] using pay_mul (pay_ref (linked_pay K') _) (linked_pay K')
end support

section read
local notation "w"=> word K
local notation "A"=> price_w K
local notation "θ"=> thetaK K
local notation "S₊"=> Bilinear.support K
local notation "B"=> pairBox K
local notation "W" x:max=> center K w x
local notation "z₀"=> E s w
include V
lemma vertex_energy (x:ℂ):
 E s (θ (W x)*(W x)) = E s (θ w*w)-((‖z₀‖^2:ℝ):ℂ)+((‖x-z₀‖^2:ℝ):ℂ):=by
 let T:= (wing K 3 (Heat.gaugeShift Λ.block ((K).ζ))).toSubmodule
 have e: ((K).plane0)= Heat.gaugeShift Λ.block (K).ζ := rfl
 let R:= Tower.form Y H V s 3 ((K).ζ)
 let c:T:=⟨w,(show w∈wing K 3 ((K).plane0) from ⟨S₊,linked_in K true,linked_clear K⟩)⟩
 let u:T:=⟨1,(wing K 3 (K).plane0).one_mem⟩
 have ht:R u c=z₀:=by change E s (θ 1 * w)=_; unfold thetaK; rw [ref_identity,one_mul]
 have h1:R u u=1:=by change E s (θ 1 * 1)=_; unfold thetaK; rw [ref_identity,mul_one,E_unit Y H V]
 have hp:R c u=star (z₀):=by rw [←ht]; exact (boson_hermitian Y H V s 3 (K).ζ c u).symm -- index?
 change R (c-x • u) (c-x • u)=R c c - _+_
 rw [map_sub R, LinearMap.sub_apply,map_smulₛₗ (f:=R)]; simp only [map_sub,map_smul,LinearMap.smul_apply,ht,h1,hp,starRingEnd_apply,smul_eq_mul,mul_one]
 rw [←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_conj_mul_self, map_sub]
 change _ = _ - star (z₀)*z₀ + (star x-star (z₀))*(x-z₀); ring

lemma reflected_mean : E s (θ w)=star (z₀) := by
 exact mirror_band Y H V s 3 (K).ζ ⟨S₊,linked_in K true,linked_clear K⟩

variable {q:ℕ→ℕ}(Q:CrimsonLine (i:=i) (k:=k) (I:=I) (E:=E) Y H q)
include Q
local notation "d" r:max=> (1/2:ℝ)^r
local notation "σ" n:max t:max => sharp Y H s n t

lemma line_diagnostic : ∀ᶠ r in atTop, let n:=i (q r); let t:=momentm Y n s
 Hosp (B) ((K).c t) ∧
 (‖I s w n-z₀‖≤d r * A ∧ ‖I s (θ w*w) n-E s (θ w*w)‖≤ d r * A^2 ∧
    ∀ x y:ℂ, ‖I s (W x) n-E s (W x)‖≤ d r*(A+‖x‖) ∧
      ‖I s (θ (W x)*(W y)) n-E s (θ (W x)*(W y))‖≤ d r * ((A+‖x‖)*(A+‖y‖))) ∧
 (∀ j, legacy Y n (k j)→
    Ferry Y s n (k j)∧‖(σ n (k j)) w-z₀‖≤d r*A ∧ ‖(σ n (k j)) (θ w*w)-E s (θ w*w)‖≤ d r*A^2∧
      ∀ x y:ℂ, ‖(σ n (k j)) (W x)-E s (W x)‖≤ d r*(A+‖x‖) ∧ ‖(σ n (k j)) (θ (W x)*(W y))-E s (θ (W x)*(W y))‖≤ d r*((A+‖x‖)*(A+‖y‖))) :=by
 filter_upwards [Q.budget s B] with r p
 have ht:= p.2.2 _ ((linked_in K true).mono (T:=B) subset_union_left) _ ((linked_pay K) _)
 have hp:= p.2.2 _ (raw_pair_in K true) _ ((raw_pair_pay K) _)
 have h(x):= p.2.2 _ ((candled K true x).mono (T:=B) subset_union_left) _ ((candled_rate K x) _)
 have g(x y):=p.2.2 _ (pair_in K true x y) _ ((pair_pay K x y) _)
 exact ⟨p.1,⟨ht.1,hp.1,fun x y=>⟨(h x).1,(g x y).1⟩⟩,fun j v=>⟨p.2.1 j v, ht.2 _ v,hp.2 _ v,fun x y=> ⟨(h x).2 _ v,(g x y).2 _ v⟩⟩⟩

local notation "E²" x:max=> E s (θ (W x)*(W x))
-- quantitative decor to common E(s), even when centering by the financial answer
-- at whichever array entry, no RP on sharp. Use uniform pay + variation strictly
-- on E there. Needn't even transfer a separate sharp approximation to hermiticity.
lemma shifting :
 ∀ᶠ r in atTop, let n:=i (q r); let t:=momentm Y n s; let u:= I s w n
 Hosp (B) ((K).c t)∧
 ‖I s (θ (W u)*(W u)) n-E² z₀‖≤
 d r*(A+‖u‖)^2+(d r * A)^2 ∧
 ∀ j, legacy Y n (k j)→ let v:=sharp Y H s n (k j) w
 Ferry Y s n (k j)∧
 ‖(σ n (k j)) (θ (W v)*(W v))-E² z₀‖ ≤ d r*(A+‖v‖)^2+(d r*A)^2 :=by
 filter_upwards [line_diagnostic Y H V s Q] with r p
 have hp(x Z:ℂ)(ht:‖Z - E s (θ (W x)*(W x))‖≤ d r * ((A+‖x‖)*(A+‖x‖)))(h:‖x-z₀‖≤d r*A) : ‖Z-E² z₀‖≤ d r*(A+‖x‖)^2+(d r*A)^2:=by
    apply (norm_sub_le_norm_sub_add_norm_sub Z (E s (θ (W x)*W x)) (E s (θ (W z₀)*W z₀))).trans; refine add_le_add (by simpa only [sq] using ht) ?_
    rw [vertex_energy Y H V s x,vertex_energy Y H V s z₀,sub_self,norm_zero]; rw [add_sub_add_left_eq_sub]; push_cast; simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow, sub_zero,norm_pow,Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; gcongr
 exact ⟨p.1,hp _ _ ((p.2.1.2.2 _ _).2) p.2.1.1, fun i v=>let a:= p.2.2 i v; ⟨a.1,hp _ _ ((a.2.2.2 _ _).2) a.2.1⟩⟩

-- only two FINITE prices (cofinal; inclusive) needed for this reduction on word
-- n = index into Course, k j = cutoff index, σ uses signed actual partition; see CrimsonLine.approx.
def seen (s n t:ℕ)(e:ℝ):Prop := ‖sharp Y H s n t (word K)-P20‖≤e ∧ ‖sharp Y H s n t (word K*thetaK K (word K))-(compared:ℂ)‖≤e
def Wanted (s:ℕ) (e:ℝ):Prop := ∃ᶠ r in atTop, ∃ j, let n:=i (q r); legacy Y n (k j) ∧ seen Y H s n (k j) e
local notation "ψ"=> word K * thetaK K (word K)
omit V Q
private lemma lim_le {c:ℝ}(a:ℕ→ℝ)(h:Tendsto a atTop (𝓝 c)){r:ℝ}(u:∃ᶠ i:ℕ in atTop,r≤ a i): r≤c:=by
 by_contra! g; exact u ((h.eventually (gt_mem_nhds g)).mono fun i v=> not_le.mpr v)
include V Q
lemma reduction {e:ℝ}(t:Tol e)(P:Wanted Y H (i:=i) (k:=k) (q:=q) s e): z₀ ≠ 0 ∧ (∀ b:Bool,Eligible K b (W z₀)) ∧ 0 < E² z₀:=by
 have hw: θ w*w=w*θ w:= ((allowed K true).forget.ref).comm (allowed K true).forget
 have g : ∃ᶠ r:ℕ in atTop, ‖z₀-P20‖ ≤ d r*A+e ∧ ‖E s (θ w*w)-(compared:ℂ)‖≤ d r*A^2+e := ((P.and_eventually (line_diagnostic Y H V s Q)).mono fun r h=>by
    obtain ⟨⟨j,v,y,Z⟩,g⟩:=h
    obtain ⟨p,h₁,h₂,_⟩:= g.2.2 j v; rw [←hw] at Z
    exact ⟨(norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add ((norm_sub_rev ..).le.trans h₁) y), (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add ((norm_sub_rev ..).le.trans h₂) Z)⟩)
 have hd(x:ℝ):Tendsto (fun r:ℕ=>d r*x+e) atTop (𝓝 e):=by
    have h:Tendsto (fun r:ℕ=>(1/2:ℝ)^r) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using (h.mul_const x).add_const e
 have h₁:= lim_le _ (hd A) (g.mono fun i u=> u.1); have h₂:= lim_le _ (hd (A^2)) (g.mono fun i u=>u.2)
 have hz: E s w≠0:=by intro p; rw [p,zero_sub,norm_neg] at h₁; linarith [t.small,normP20]
 let x:= z₀; let y:= E s (θ w*w); let z:= E s (θ (W z₀)*(W z₀))
 have hb : ‖x‖≤ ‖P20‖+e := by have hh:= (norm_sub_norm_le x P20); change ‖x-P20‖≤_ at h₁; linarith
 change ‖y-(compared:ℂ)‖≤e at h₂
 have hu: compared-e ≤ y.re :=by have hg:= Complex.abs_re_le_norm (y-compared); rw [Complex.sub_re,Complex.ofReal_re,abs_le] at hg; linarith only [hg.1,h₂]
 have hg: z = y-((‖x‖^2:ℝ):ℂ):=by unfold z; rw [vertex_energy Y H V s x,sub_self,norm_zero,zero_pow (by decide),Complex.ofReal_zero,add_zero]
 have nn:0≤ z:=boson_axial Y H V s (z:=(K).ζ) (candled K true x) (linked_clear K)
 have gl:0<z.re:=by rw [hg,Complex.sub_re,Complex.ofReal_re]; nlinarith [norm_nonneg x,t.gap]
 exact ⟨hz, fun b=> cent_el K b _,Complex.lt_def.mpr ⟨gl,(Complex.le_def.mp nn).2⟩⟩
end read

end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.reduction
