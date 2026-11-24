import YM.SU5.SatinWard.Resolution.Frame

/-!
# Character frames (physics-specific Sweep reps)
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]

namespace ResolutionFrame
abbrev atScale (F:ResolutionFrame ι)(h q:ℝ): Coords ι→ₗ[ℝ] ArcΦ := (scaleBasis q h).comp F.code
abbrev deg (F:ResolutionFrame ι):ℕ:= if F.fourth then 4 else 3
abbrev mu (L:Side):ℝ:=(L.val:ℝ)⁻¹
abbrev chiLoss (F:ResolutionFrame ι)(L:Side):ℝ:= mu L ^ F.deg
abbrev nullLoss(L:Side):ℝ:= mu L ^ (5:ℕ)
lemma mu_pos (L:Side):0< mu L:=by unfold mu; positivity
lemma chi_pos (F:ResolutionFrame ι)(L:Side):0<chiLoss F L:= pow_pos (mu_pos L) _
lemma null_pos(L:Side):0<nullLoss L:=pow_pos (mu_pos L) _
lemma chi_inverse (F:ResolutionFrame ι)(L:Side): (chiLoss F L)⁻¹=(L.val:ℝ)^F.deg:=by simp only [chiLoss, mu, inv_pow, inv_inv]
lemma chi_dimension (F:ResolutionFrame ι)(L:Side): L.val*(nullLoss L) ≤ F.chiLoss L :=by
 have h:1 ≤ (L.val:ℝ):=by exact_mod_cast L.property
 have hz:0 ≤ mu L:=(mu_pos L).le
 have hx:L.val*(nullLoss L)=mu L^(4:ℕ):=by unfold nullLoss; rw [pow_succ',←mul_assoc,show L.val * mu L= (1:ℝ) from mul_inv_cancel₀ (zero_lt_one.trans_le h).ne',one_mul]
 unfold chiLoss deg; rw [hx]; split; rfl
 apply pow_le_pow_of_le_one hz (inv_le_one_of_one_le₀ h) (by decide)
local notation "exp1" => Real.exp (1:ℝ)

variable (F:ResolutionFrame ι) (L:Side) (X Y:BudgetPoint)(h κ:ℝ)
abbrev typical (F:ResolutionFrame ι) (L:Side) (X Y:BudgetPoint)(κ:ℝ)(i:ι):ℝ:= κ * if F.gauge i then Tune.qCorset X.threshold Y.threshold (L.val:ℝ) else F.chiLoss L

lemma «rates» (q:ℝ)(i:ι) :
    let W:= F.atScale h q (leg i); let r:= F.typical L X Y κ i
    r • W.1=ζtap L X Y (κ:ℂ) W ∧ r • W.2.1= ζVtap L (κ:ℂ) W ∧ r • W.2.2=ξtap L (κ:ℂ) W:=by
 intro W r
 have hA:= F.basis i; have hB:= F.polar (leg i); let U:=F.code (leg i); dsimp only at hB
 cases w:F.fourth
 · rw [if_neg (by rw [w]; decide)] at hB; have hp₁:W.1=0:=by change q • (F.code (leg i)).1=0; rw [hB.1,smul_zero] -- tune change
   have hp₂:W.2.2=0:=by change (q/h^2) • (F.code (leg i)).2.2=0; rw [hB.2,smul_zero]
   have hz: F.gauge i=false:= by cases hs:F.gauge i; rfl; rw [F.gauge_weight i hs] at w; contradiction
   refine ⟨by unfold ζtap; rw [hp₁]; simp,?_,by unfold ξtap; rw [hp₂]; simp⟩
   unfold r typical chiLoss deg ζVtap; rw [hz,w, ←Complex.ofReal_pow, (peach L).1,Complex.coe_smul,Complex.coe_smul,smul_smul,mul_comm κ]; rfl -- tune true
 rw [if_pos w] at hB; have hp:W.2.1=0:=by change (q/h^2) • (F.code (leg i)).2.1=0; rw [hB,smul_zero];
 refine ⟨?_,by unfold ζVtap; rw [hp]; simp,?_⟩ <;> cases t:F.gauge i
 · rw [if_neg (by rw [t]; decide)] at hA; unfold ζtap; rw [show W.1=0 from (show q • (F.code (leg i)).1=(0:Skate) from by rw [hA,smul_zero])]; simp
 · unfold r typical ζtap; rw [if_pos t,Complex.coe_smul,Complex.coe_smul,smul_smul,mul_comm]; -- if_true
 · unfold r typical chiLoss deg ξtap; rw [t,w,← Complex.ofReal_mul,(peach L).2,Complex.coe_smul,Complex.coe_smul,smul_smul,mul_comm κ]; rfl
 rw [if_pos t] at hA; unfold ξtap; rw [show W.2.2=0 from (show (q/h^2) • (F.code (leg i)).2.2=0 from by rw [hA]; exact smul_zero _)]; simp

lemma ratio_scale (x:Coords ι)(q Q:ℝ)(p:Q≠0): F.atScale h Q ((q/Q) • x) = F.atScale h q x:=by
 rw [map_smul]; have he {V:Type}[AddCommGroup V][Module ℝ V](i:V)(a:ℝ): (q/Q) • ((Q/a) • i)=(q/a) • i:=by rw [smul_smul,show q/Q*(Q/a)=q/a by rw [div_mul_div_cancel₀ p]] -- tune
 exact Prod.ext (show (q/Q) • (Q • (F.code x).1)= q • (F.code x).1 from by rw [smul_smul,div_mul_cancel₀ _ p]) (he _ _)

lemma shape_toll (x:Coords ι)(q:ℝ)(p:0≤q)(u:1≤h) : let W:=F.atScale h q x
   ‖W.1‖=q*‖(F.code x).1‖ ∧ ‖W.2.1‖*h^2=q*‖(F.code x).2.1‖ ∧ ‖W.2.2‖*h^2=q*‖(F.code x).2.2‖ := by
 intro W; have p':0< h^2:=by positivity
 have he {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V](i:V): ‖(q/h^2) • i‖*h^2=q* ‖i‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]; field_simp
 refine ⟨?_, he _ , he _⟩; change ‖q • (F.code x).1‖ =_; rw [norm_smul,Real.norm_of_nonneg p]

lemma typical_bounds (p:Real.exp (-1) ≤ |κ|)(t:|κ|≤ exp1)
   (hu:(mu L)^(4:ℕ)/4≤ Tune.qCorset X.threshold Y.threshold (L.val:ℝ))
   (hv:Tune.qCorset X.threshold Y.threshold (L.val:ℝ)≤4*mu L^(4:ℕ))(q Q:ℝ)(hq:0<q)(hQ:q≤Q)(tQ:Q≤2*q)(i:ι) :
    Real.exp (-1)/8 * F.chiLoss L ≤ |F.typical L X Y κ i * (q/Q)| ∧ |F.typical L X Y κ i * (q/Q)| ≤ (4*exp1)*F.chiLoss L :=by
 let K:= if F.gauge i then Tune.qCorset X.threshold Y.threshold (L.val:ℝ) else F.chiLoss L
 have s:= F.chi_pos L; let v:=(F.chiLoss L); change 0<v at s
 have k: v/4 ≤ K∧ K≤ 4*v:=by
    unfold K; split_ifs with w; · unfold v chiLoss deg; rw [if_pos (F.gauge_weight i w)]; exact ⟨hu,hv⟩
    change v/4 ≤ v∧ v ≤ 4*v; constructor<;> linarith only [s]
 have a₀:(1/2:ℝ)≤ q/Q:=(le_div_iff₀ (hq.trans_le hQ)).2 (by linarith only [tQ]); have v₀: q/Q ≤1:=div_le_one_of_le₀ hQ (hq.trans_le hQ).le
 have b₀:=lt_of_lt_of_le (by positivity:0<v/4) k.1; have hp:(0:ℝ) ≤ q/Q:=le_trans (by norm_num) a₀
 unfold typical; change _≤ |κ*K*(q/Q)| ∧ |κ*K*(q/Q)| ≤ _; rw [abs_mul,abs_mul,abs_of_nonneg b₀.le,abs_of_nonneg hp]; constructor
 · exact (by calc
    _ = Real.exp (-1)*(v/4)*(1/2):=by unfold v; ring
    _ ≤ _ := by gcongr; exact k.1)
 calc
    _ ≤ exp1*(4*v)*1:=by gcongr; exact k.2
    _ = _:=by unfold v; ring

lemma scaleZero (x:Coords ι)(q:ℝ): let W:=F.atScale h q x
    (F.fourth=true → W.2.1=0) ∧ (F.fourth=false→ W.1=0 ∧ W.2.2=0) :=by
 intro W; have hv:=F.polar x; dsimp only at hv
 constructor
 · intro g; rw [if_pos g] at hv; change (q/h^2) • (F.code x).2.1=0; rw [hv,smul_zero]
 intro g; rw [if_neg (by rw [g]; decide)] at hv; exact ⟨show q • (F.code x).1=0 from (by rw [hv.1,smul_zero]),show (q/h^2) • (F.code x).2.2=0 from (by rw [hv.2,smul_zero])⟩

structure Stretch (F:ResolutionFrame ι)(C:ℝ):Prop where
 large : 1 ≤ C
 pay : ∀ x, ‖F.code x‖ ≤ C * ‖x‖ ∧ ‖x‖ ≤ C * ‖F.code x‖

variable {L X Y h κ F} {C A q Q:ℝ} (s:Stretch F C) {T X₀ X₁ X₂:ℝ}
local notation "Ψ" => exp1*C
local notation "μL" => mu L
local notation "wL" => chiLoss F L
local notation "μK" => nullLoss L
abbrev basePay (C:ℝ) :ℝ:= 2*exp1*C+1
abbrev nullPay (C A:ℝ) :ℝ:= 3*exp1*C+A+1
variable (p:0<q)(u:1≤h)(k:|κ|≤exp1)
include p u k s
lemma tariff_build (x:Coords ι)(e:‖x‖≤1): let W:=F.atScale h q x
    ‖(κ:ℂ)‖*‖W.1‖≤ Ψ*q ∧ ‖(κ:ℂ)‖*‖W.2.1‖*h^2≤ Ψ*q ∧ ‖(κ:ℂ)‖*‖W.2.2‖*h^2≤ Ψ*q:=by
 intro W; obtain ⟨a,b,v⟩:= F.shape_toll h x q p.le u; change ‖W.1‖=_ at a; change ‖W.2.1‖*h^2=_ at b; change ‖W.2.2‖*h^2=_ at v
 have g:‖F.code x‖ ≤ C:= (s.pay x).1.trans (mul_le_of_le_one_right (zero_le_one.trans s.large) e)
 have hx(t:ℝ)(z:0≤ t)(y:t ≤ ‖F.code x‖): ‖(κ:ℂ)‖ * (q * t) ≤ Ψ*q:=by
    rw [Complex.norm_real,Real.norm_eq_abs,mul_assoc,mul_comm C q]
    exact mul_le_mul k (mul_le_mul_of_nonneg_left (y.trans g) p.le) (mul_nonneg p.le z) (Real.exp_pos ..).le
 rw [a, mul_assoc _ _ (h^2),mul_assoc _ _ (h^2), b,v]
 exact ⟨hx _ (norm_nonneg _) (norm_fst_le _),hx _ (norm_nonneg _) ((norm_fst_le _).trans (norm_snd_le _)), hx _ (norm_nonneg _) ((norm_snd_le _).trans (norm_snd_le _))⟩

variable (s₀:1≤A)(b:|T|≤nullLoss L*q)
include s₀ b
lemma estimate_mint (x:Coords ι)(e:‖x‖≤1)(g:A+1≤L.val):
    |κprobe mintR L h (A*q) T (κ:ℂ) (F.atScale h q x)|≤ basePay C * wL*q:=by
 let W:= F.atScale h q x; obtain ⟨v₁,v₂,v₃⟩:=tariff_build s p u k x e
 let a:= ‖(κ:ℂ)‖*‖W.1‖; let d:= ‖(κ:ℂ)‖*‖W.2.1‖*h^2; let c:= ‖(κ:ℂ)‖*‖W.2.2‖*h^2
 change a≤_ at v₁; change d≤_ at v₂; change c≤_ at v₃
 have hv:μK*(A*q)+|T| ≤ wL*q:=by
    refine (add_le_add_right b _).trans ?_ -- binder left-right
    calc
     _ = (A+1)*μK*q := by ring
     _ ≤ _:=mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right g (null_pos L).le).trans (F.chi_dimension L)) p.le
 have hm:= mu_pos L; have hz:=null_pos L; have h0:=zero_lt_one.trans_le s₀; have hx:= zero_lt_one.trans_le s.large
 change |μL^4*a+μL^3*d+μL^4*c+μK*(A*q)+T| ≤ _; refine (abs_add_le ..).trans ?_; rw [abs_of_nonneg (?_:0 ≤ μL^4*a+μL^3*d+μL^4*c+μK*(A*q)),add_assoc _ (μK*(A*q))]; swap; · unfold a c d W; positivity
 apply (add_le_add_right hv _).trans ?_ -- tune
 unfold basePay; let f:= F.scaleZero h x q
 change (F.fourth=true→ W.2.1=0)∧(F.fourth=false→W.1=0 ∧ W.2.2=0) at f
 cases w:F.fourth
 · have h0:=f.2 w; rw [show wL=μL^3 from (by unfold chiLoss deg; rw [w]; rfl),show a=0 from (by simp [a,h0.1]),show c=0 from (by simp [c,h0.2]), mul_zero, add_zero,zero_add]; refine (add_le_add_left (mul_le_mul_of_nonneg_left v₂ (pow_nonneg hm.le 3)) _).trans ?_
   nlinarith only [mul_nonneg (pow_nonneg hm.le 3) (show 0≤ exp1*C*q by positivity)]
 rw [show wL=μL^4 from (by unfold chiLoss deg; rw [w]; rfl),show d=0 from (by unfold d; rw [f.1 w,norm_zero,mul_zero,zero_mul]),mul_zero,add_zero]; apply (add_le_add_left (add_le_add (mul_le_mul_of_nonneg_left v₁ (pow_nonneg hm.le _)) (mul_le_mul_of_nonneg_left v₃ (pow_nonneg hm.le _))) _).trans_eq; ring

omit s u k in
lemma estimate_hidden:
 |κprobe mintR L h (A*q) T (κ:ℂ) 0|≤ (A+1)*μK*q:=by
 simp only [κprobe,mintR,Prod.fst_zero,Prod.snd_zero,norm_zero,mul_zero,zero_mul, zero_add]
 apply (abs_add_le ..).trans; change |μK*(A*q)| +|T|≤_; rw [abs_of_nonneg (mul_nonneg (null_pos L).le (mul_nonneg (zero_le_one.trans s₀) p.le))]; apply (add_le_add_right b _).trans_eq; ring -- tune binder common
lemma estimate_nax (x:Coords ι)(e:‖x‖≤1):
 |κprobe naxR L h (A*q) T (κ:ℂ) (F.atScale h q x)|≤ nullPay C A*μK*q:=by
 let W:= F.atScale h q x; obtain ⟨v₁,v₂,v₃⟩:=tariff_build s p u k x e
 let a:= ‖(κ:ℂ)‖*‖W.1‖; let d:= ‖(κ:ℂ)‖*‖W.2.1‖*h^2; let c:= ‖(κ:ℂ)‖*‖W.2.2‖*h^2
 change a≤_ at v₁; change d≤_ at v₂; change c≤_ at v₃; have hm:= null_pos L; have hx:= zero_lt_one.trans_le s₀
 change |μK*(a+d+c+A*q)+T|≤_; apply (abs_add_le ..).trans
 rw [abs_of_nonneg (?_:0≤ μK*(a+d+c+A*q))]; swap; · unfold a d c; positivity
 apply (add_le_add (mul_le_mul_of_nonneg_left (add_le_add_left (add_le_add (add_le_add v₁ v₂) v₃) _) hm.le) b).trans_eq; unfold nullPay; ring
-- general alpha error: estimate in coords after comparing to target f=e*g∘diag, uniform before h. absolute ok
abbrev accuracy (C K A:ℝ):ℝ:= C*(K*nullPay C A)
include p u k s s₀ b
lemma estimate_correction (K:ℝ)(hK:1≤K)(hQ:q≤Q)(z z' x:Coords ι)(e:‖x‖≤1)
 (x₀:|X₀|≤K)(x₁:|X₁|≤K)(x₂:|X₂|≤K)
 (E:αPrice L h (A*q) T X₀ X₁ X₂ (F.atScale h q x) (F.atScale h Q z') X Y (κ:ℂ))
 (H₀:(F.atScale h Q z).1=ζtap L X Y (κ:ℂ) (F.atScale h q x))
 (H₁:(F.atScale h Q z).2.1=ζVtap L (κ:ℂ) (F.atScale h q x))
 (H₂:(F.atScale h Q z).2.2=ξtap L (κ:ℂ) (F.atScale h q x)) :
 ‖z'-z‖ ≤ accuracy C K A*μK:=by
 let V:= F.atScale h q x; let W:=F.atScale h Q; let D:=z'-z; obtain ⟨he,hv,hw⟩:= E
 let r:= nullPay C A*μK; let R:= K*r; let c:=F.code D; have ht:=estimate_nax s p u k s₀ b x e
 have hPositive:0<K:= zero_lt_one.trans_le hK; let hC:= zero_lt_one.trans_le s.large; let hA:=zero_lt_one.trans_le s₀; let hz:= p.trans_le hQ; let hm:=null_pos L; have hr:0≤ r:=by unfold r nullPay; positivity
 have bound (a:ℝ)(hq:|a|≤K) : a*(κprobe naxR L h (A*q) T (κ:ℂ) V) ≤ Q*R:=by -- h binder conflict
    let g:=κprobe naxR L h (A*q) T (κ:ℂ) V -- tune h overwritten; h doesn't resolve
    refine (le_abs_self (a*g)).trans ?_; rw [abs_mul];  calc
     _ ≤ K*(r*q) := mul_le_mul hq ht (abs_nonneg _) (zero_le_one.trans hK)
     _ = q*R:=by unfold R; ring
     _ ≤ _:=mul_le_mul_of_nonneg_right hQ (mul_nonneg (zero_le_one.trans hK) hr)
 rw [←H₀,← Prod.fst_sub, ← map_sub (F.atScale h Q), (F.shape_toll h D Q hz.le u).1] at he
 rw [←H₁,← Prod.fst_sub,←Prod.snd_sub,←map_sub (F.atScale h Q), (F.shape_toll h D Q hz.le u).2.1] at hv
 have hZ: ‖c‖≤ R:=by
    rw [Prod.norm_def]; refine max_le ((mul_le_mul_iff_right₀ hz).mp (he.trans (bound _ x₀))) ?_
    rw [Prod.norm_def]; refine max_le ((mul_le_mul_iff_right₀ hz).mp (hv.trans (bound _ x₁))) ?_
    cases g:F.fourth
    · let e:= (F.polar D); dsimp only at e; rw [if_neg (by rw [g]; decide)] at e; rw [show c.2.2=0 from e.2,norm_zero]; exact mul_nonneg (zero_le_one.trans hK) hr
    rw [←H₂,← Prod.snd_sub,←Prod.snd_sub,←map_sub (F.atScale h Q), (F.shape_toll h D Q hz.le u).2.2] at hw
    have p:κprobe nagR L h (A*q) T (κ:ℂ) V=κprobe naxR L h (A*q) T (κ:ℂ) V:=by unfold κprobe nagR; rw [show V.2.1=0 from (F.scaleZero h x q).1 g,norm_zero,mul_zero,zero_mul,mul_zero,add_zero]
    change _≤ X₂*(κprobe nagR L h (A*q) T (κ:ℂ) V) at hw
    rw [p] at hw; exact (mul_le_mul_iff_right₀ hz).mp (hw.trans (bound _ x₂))
 refine ((s.pay D).2.trans (mul_le_mul_of_nonneg_left hZ hC.le)).trans_eq ?_; unfold accuracy R r; ring

end ResolutionFrame
end ShapeLab
end YM.CF.QuadClock
