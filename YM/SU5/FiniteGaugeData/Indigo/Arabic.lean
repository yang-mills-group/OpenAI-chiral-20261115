import YM.SU5.FiniteGaugeData.Indigo.Mayla
import YM.SU5.FiniteGaugeData.Indigo.Bearing
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxSize 23000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche Work.F06
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
set_option quotPrecheck false
namespace WinkQ
open Nectar
open Nosh Apoth Real Vulcan Willow Lumi Cordon Tulipe
open Tulipe Vulcan Willow CF -- name Op.Descript
open CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight.Succulent.SpineV Licor.Lychee
open YM.SU5.FiniteGaugeData.Indigo Brew Sweat Taper Tulipe.IndigoLX
variable {n:Side} {ρ C Δ σ K β α t v u' ε: ℝ} {P:Bed}{u:Stage}
local notation "G"=> CF.SU.group
variable {R: PathData CF.SU.group}(F:Floor P u.clip n ρ C)(d:0<ρ)(W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(p:P.metric.strip σ K)(hr:0<σ) (x: Cover)(b:Site n)(r:ℝ)
local notation "M"=> CF.SU.group.ColorIndex
local notation "E"=> Vault (Plush G (denim n))
local notation "μ"=> stdGaussian (Vault (Plush G (denim n)))
local notation "uV"=> olive F d CF.SU.group
-- predicted weights for stencil.
abbrev spun(p:Fin 4):Cover:= (lyre p).offset
noncomputable abbrev flare1(i:Fin 4):= beamsS («G»:=CF.SU.group) F d (wrap n (spun i)) r -- Mayla imports LapisQ Figura→Musc.
noncomputable abbrev Neb(a:CF.SU.group.ColorIndex) : Vault (Plush CF.SU.group (denim n)) := ∑ i:Fin 4, flare1 F d r i a
noncomputable abbrev Qua(a:CF.SU.group.ColorIndex): Vault (Plush CF.SU.group (denim n)):= beamsS F d (wrap _ x) r a
-- origin calibrate & patch.H. use sums.
local notation "N₀"=> Neb F d r
local notation "Πx"=> Qua F d x r
lemma legP (a: Fin 4): (lyre a).plaq= Nest:=by fin_cases a <;> rfl
variable {V:Lumi.Duct CF.SU.group XiCore}(vp: V.beam= August x)
include vp
private lemma radical (i:Fin 4)(y:E): r • (Lumi.pollen V 1 0 (uV y) (some i)) = opus (flare1 F d r i) y:=by
 rw [baseNeed, vp]; rw [show slotFace (August x (some i)) (0:Site n)=(wrap n (spun i),Nest) from ?_]; exact rim ..; unfold slotFace; -- rfl.V.
 change (wrap n (spun i)+0,(lyre i).plaq) = _; rw [legP,add_zero]
lemma payloadJ (y:E): Shekel (r • Lumi.pollen V 1 0 (uV y)) = opus (Neb F d r) y:=by
 let K:=r • Lumi.pollen V 1 0 (uV y); let P(i:Fin 4):= K (some i);
 change Obl P=_; unfold Obl; ext j; simp_rw [PiLp.add_apply]; change _=inner ℝ (Neb F d r j) y; have he(i):P i=opus (flare1 F d r i) y:= radical F d x r vp i y; rw [he,he,he,he]; change (inner ℝ _ _ +(inner ℝ _ _+(inner ℝ _ _+ inner ℝ _ _)))=_; rw [Neb,sum_inner]; simp [Fin.sum_univ_succ]; -- bracket associativity
lemma payloadF (y:E): (r • Lumi.pollen V 1 0 (uV y)) none = opus (Qua F d x r) y:=by
 rw [Pi.smul_apply,baseNeed,vp,show August x none=_ from (show August x none=sprinkle x Nest from rfl),wet0,add_zero]; exact rim ..
omit vp
-- symbolic prices S lens on Gaussian U.CQ. include F implicitly.Status.
noncomputable abbrev sell(V:Lumi.Duct CF.SU.group XiCore): ℝ := divanF V F d V.seen r
variable (t:ℝ)(k:0<t)
lemma koan : sell F d r (Korn x t k)= dawn t (Neb F d r):=by
 unfold sell divanF dawn; apply integral_congr_ae; refine Eventually.of_forall fun i=>?_; let V:=Korn x t k; change roseM t (Shekel _) = _; rw [payloadJ F d x r (V:=Korn x t k) rfl] -- tune v
lemma quin : sell F d r (Kayak x t k)= dawn t (Qua F d x r):=by unfold sell divanF dawn; apply integral_congr_ae; refine Eventually.of_forall fun i=>?_; let V:=Kayak x t k; change roseM t ((r • Lumi.pollen V 1 0 (uV i)) none)=_; rw [payloadF F d x r (V:=V) rfl]
lemma quoin : sell F d r (Nirv x t k)= dualC t (Neb F d r) (Qua F d x r):=by unfold sell divanF dualC; apply integral_congr_ae; refine Eventually.of_forall fun i=>?_; let V:=Nirv x t k; let f:= (Lumi.pollen V 1 0 (uV i)); change roseM t (Shekel (r • f)) * roseM t ((r • f) none)= _; unfold f; rw [payloadF F d x r (V:=V) rfl, payloadJ F d x r (V:=V) rfl] -- tune
noncomputable abbrev Amen(x:Cover)(t:ℝ)(h:0<t): ℝ:= sell F d r (Nirv x t h)- sell F d r (Korn x t h)*sell F d r (Kayak x t h)
variable (a₁: CF.SU.group.ColorIndex)
local notation "S₀"=> sineB F d a₁ a₁
include W A p hr
lemma suba (q o:Site n)(i:M):inner ℝ (beamsS F d q r i) (beamsS F d o r i)= r^2*songV (sineB F d a₁ a₁) (o-q):=by unfold beamsS; rw [real_inner_smul_left,real_inner_smul_right,stoutS F d W A p hr a₁,if_pos rfl, ←mul_assoc,←sq]
lemma loudS (i:M): inner ℝ (Neb F d r i) (Qua F d x r i)= r^2*(4*Herald spun (S₀) (wrap n x)):=by
 unfold Neb flare1 Qua Herald; rw [sum_inner]; simp_rw [suba F d W A p hr r a₁]; rw [←Finset.mul_sum]; congr 1; rw [Fintype.card_fin,Nat.cast_ofNat,←mul_assoc, mul_inv_cancel₀ (by norm_num),one_mul] -- tune pargs `q o`!
abbrev CostW (ρ b:ℝ):ℝ:= Real.sqrt (b^2*(1/ρ)) -- θmax b
abbrev PortZ(ρ b:ℝ):=4*CostW ρ b
variable (p₂:0≤r)(z:r≤ β)
include p₂ z a₁
lemma beamB(i:M)(x:Site n): ‖beamsS F d x r i‖ ≤ CostW ρ β :=by
 apply Real.le_sqrt_of_sq_le; rw [← real_inner_self_eq_norm_sq, suba F d W A p hr r a₁, sub_self]; let R':= gateZ F d W A p hr a₁; exact le_trans (mul_le_mul_of_nonneg_left (le_of_abs_le (life_spend R' 0)) (sq_nonneg _)) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ p₂ z _) (by positivity))
lemma crewC(i:M) : ‖Neb F d r i‖ ≤ PortZ ρ β∧ ‖Qua F d x r i‖ ≤ PortZ ρ β:=by
 have he(x:Site n):= beamB F d W A p hr r a₁ p₂ z i x; refine ⟨(norm_sum_le ..).trans ((sum_le_sum (f:=fun y:Fin 4=>‖flare1 F d r y i‖) (fun i _=> he _)).trans_eq ?_), (he _).trans ?_⟩;
 · rw [sum_const,nsmul_eq_mul,card_univ, Fintype.card_fin, Nat.cast_ofNat]; -- goal after
 apply le_mul_of_one_le_left (Real.sqrt_nonneg _) (show 1≤(4:ℝ) from by norm_num)
-- if herald >c high. 
abbrev magic(α z:ℝ):= 2*(α^2*(4*z))^2
omit p₂
variable {c:ℝ}
lemma sunB (v₀:0<α)(p₀:α≤r)(h:0 < c)(v:c≤|Herald spun (sineB F d a₁ a₁) (wrap n x)|): magic α c ≤ Nir (Neb F d r) (Qua F d x r) :=by
 let N:=N₀; let J:=Πx; have hp: α^2*(4*c) ≤ |inner ℝ (N a₁) (J a₁)|:= by
    rw [show inner ℝ (N a₁) (J a₁)=_ from loudS F d W A p hr x r a₁ a₁,abs_mul, abs_mul 4, abs_of_nonneg (sq_nonneg r), abs_of_nonneg (by norm_num:(0:ℝ)≤4)]
    exact mul_le_mul (pow_le_pow_left₀ v₀.le p₀ 2) (mul_le_mul_of_nonneg_left v (by norm_num)) (by positivity) (sq_nonneg _)
 have hz:magic α c ≤ 2*(inner ℝ (N a₁) (J a₁))^2:= mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (b:=|inner ℝ (N a₁) (J a₁)|) (by positivity: 0 ≤ α^2*(4*c)) hp 2).trans_eq (sq_abs ..)) zero_le_two -- order .b named
 -- $Nonempty` instance from i requires letI
 letI : Nonempty CF.SU.group.ColorIndex:= ⟨a₁⟩; exact hz.trans (exhaust N J a₁ a₁)
-- sector ask: Need choose cutoff t after explicit a/r.ctor.
omit z a₁ W A F p hr -- F maybe contains d? include works later
lemma CuspW [Nonempty CF.SU.group.ColorIndex] (ℓ:ℕ)(σ ρ K β α:ℝ)(u:0<ρ)(a:0<α): ∃ c t₀:ℝ,0<c∧0<t₀∧∃ N M':ℕ, ∀{n:Side}{u:Stage}{P:Bed}{R:PathData CF.SU.group}{Δ C:ℝ}(F:Floor P u.clip n ρ C), R.Bounds u.clip u.width u.paths Δ  →  Attached P R  →  P.metric.strip σ K  →  0<σ → ∀ r:ℝ,α ≤ r → r ≤ β  →  N ≤ n.val  →  ∃ x∈ marketZ M', lapse ℓ x ∧∀ t:ℝ,∀ h:0<t,t ≤ t₀ →  c ≤  Amen F ‹0<ρ› r x t h :=by
 obtain ⟨b,t,M1,N,V'⟩:= spinster spun ℓ σ ρ K; let y:= magic α b; let E':=PortZ ρ β; have hy:0<y:=by unfold y magic; positivity
 let E₀:= genial CF.SU.group.ColorIndex E'; have he:0 ≤ E₀:= gen_p _ (mul_nonneg (by norm_num: (0:ℝ)≤4) (Real.sqrt_nonneg _)); let D:= y/2/(E₀+1); have ht:0<E₀+1:= add_pos_of_nonneg_of_pos he zero_lt_one
 refine ⟨y/2,D,half_pos hy,div_pos (half_pos hy) ht,N,M1,?_⟩; intro n u' P R Δ C F Q S v' p r p₀ q v; let i:= Classical.arbitrary CF.SU.group.ColorIndex; let A':= sineB F u i i; obtain ⟨x,s',w₂,k⟩:= V' (gateZ F u Q S v' p i) v; let Y:= Neb F u r; let Z:= Qua F u x r; refine ⟨x,s',w₂,fun t' t'₀ v₂=>?_⟩
 have hp:y≤ Nir Y Z:= sunB F u Q S v' p x r i q a p₀ t k.le; have hc(i'): ‖Y i'‖ ≤ E' ∧ ‖Z i'‖≤ E':= crewC F u Q S v' p x r i (a.le.trans p₀) q i'; unfold Amen; rw [koan,quin,quoin] ; have he:t'*E₀≤ y/2:= (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) t'₀.le).trans ((le_div_iff₀ ht).mp v₂); linarith only [thrift t' t'₀ Y Z E' (fun i=>(hc i).1) (fun i=>(hc i).2),hp,he] -- `$le_of_sub` remove
#print axioms CuspW
end WinkQ
end YM.SU5.FiniteGaugeData.LapisQ
