import YM.CF.Tye.Jaws
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tye
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "Y"=> clue S s b M
local notation "V"=> shiftZ g M
local notation "F"=> cedar M
variable (h:K.Funds S T)(hp:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hv:120 ≤ radiusB x)(hz:0 < m)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(ht: LocalRatio A.vita)(hi:0 < A.rota)(hm:4*A.rota < A.vita.radius)(hb:0 < A.beta)
local notation "d"=> Domain N B
local notation "d'"=> Domain P B
local notation "L"=> Stores.till x
local notation "Z"=> mid N B
local notation "j'"=> A.loft
local notation "q"=> A.trot
local notation "Q"=> A.LawQ
local notation "L'"=> A.post
local notation "J"=> A.vita
local notation "R"=> A.rota
local notation "v'"=> A.room
local notation "H"=> A.hot
local notation "β"=> A.beta
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "X"=> kist M
variable (f:Sweep (mid N B))(W U': Rent0 G e)(i:Site (Domain N B))
variable (ph:S.ratio=ratio G)(t:tyke G A.LawQ)(xw:A.Beds.val=(1,1))
local notation "W'"=> male e G f W
local notation "N'"=> rot f M
local notation "A'"=> clue S f.s (Facet.pasta f) M
local notation "Λ"=> chart f
local notation "Ω"=> M.key.dome (j'*radiusB x)
variable (ρ:∀ M:Monk SU.group S, Chir M x→WaveK (m:=m) A M)(σ:ℝ) (pu:Chir M x)
local notation "mB"=> M.key
local notation "W₀"=> Palot.leaf (Site d)
variable (k: Sweep (mid N B))(r': Palot.leaf (Site (Domain N B)))
abbrev chute(f: Sweep (mid N B)):= Equiv.ofBijective (trunk (N:=N) (B:=B) f.s (Facet.pasta f)) ⟨bright_inj ..,Finite.injective_iff_surjective.mp (bright_inj ..)⟩
lemma goldM(v:Site d):(chart (f*k)) v=chart f (chart k v):=(Spire.stirP f k v).symm -- implicit coercion?
lemma goldB : chute (f*k) r'=chute f (chute k r'):= by apply Subtype.ext; change r'.val.image _=(r'.val.image _).image _; rw [image_image]; exact image_congr fun i _=> goldM ..
lemma wind_p : massX A M r'=massX A (rough M 0) r':=rfl -- no ζ guaranteed
include pu ρ h hA hB hz hv
lemma mass_b(i:Site d)(j:ℕ) : penR T x q v' L' N' j i= penR T x q v' L' M j (Λ i):=by
 have hv₀: penR T x q v' L' A' j i= penR T x q v' L' M j (Λ i):=by
    unfold penR; rw [beds_s T M _ _ _ _ h (ρ M pu).gap hv hz, kist_s,tit_s T _ _ q h]
    rfl -- tune
 rw [←hv₀]; unfold rot dice; split; next z=> unfold penR; rw [beds_f T _ _ _ _ _ h hA (ρ A' (sing_b M f.s (Facet.pasta f) pu)).gap hv hz]; rfl
 rfl
lemma mass_f(r:Ready T x)(t':1000≤radiusB x)(u:Portus A (rot f M))(v:Portus A M): ∑ i:W₀,massX A (rot f M) i=∑ i:W₀,massX A M i:=by
 rw [summons A _ r t' u, summons A _ r t' v]; refine tsum_congr fun j=>?_ ; exact sum_equiv (chart f) (by simp) (fun i _=> mass_b A M h hv hz hA hB f ρ pu _ _)
omit pu ρ h hA hB hz hv
-- sym avg.V frozen. permits any β trial
section
variable{E:Type}[Fintype E](Xf:Sweep (mid N B)→Equiv.Perm E)(V₁:Monk SU.group S→E→ℂ)
def patrol (M:Monk SU.group S)(z:E):ℂ:= (Fintype.card (Sweep Z):ℝ)⁻¹ • ∑ v:Sweep Z, payZ v (V₁ (rough (rot v M) 0) ((Xf v).symm z))
lemma porch (h:∀ f k i,Xf (f*k) i=Xf f (Xf k i))(u:E): patrol Xf V₁ (rot f M) u=payZ f (patrol Xf V₁ M (Xf f u)):=by
 unfold patrol; rw [← din_t,map_smul,map_sum]; apply congrArg; conv_rhs=> rw [← Equiv.sum_comp (Equiv.mulLeft f)]
 refine sum_congr rfl fun i _=>?_ ; rw [din_t]; change payZ i _=payZ f (payZ (f*i) _); have hC: (Xf i).symm u=(Xf (f*i)).symm (Xf f u):=by apply (Xf (f*i)).injective; rw [h f i,(Xf i).apply_symm_apply,Equiv.apply_symm_apply]
 rw [crewX M f i,hC,←warX,izard]; rfl
set_option maxHeartbeats 600000 in
lemma portE (h:∀ f,∑ i,V₁ (rot f M) i=payZ f (∑ i,V₁ M i))(h':∀ f i,V₁ (rough (rot f M) 0) i=V₁ (rot f M) i): ∑ i,patrol Xf V₁ M i=∑ i,V₁ M i:=by
 unfold patrol; simp_rw [←Finset.smul_sum,h']; rw [sum_comm]; have he(f:Sweep Z):(∑ i,payZ f (V₁ (rot f M) ((Xf f).symm i)))=∑ i,V₁ M i:=by
    rw [Equiv.sum_comp (Xf f).symm (fun i=>payZ f (V₁ (rot f M) i))]; simp_rw [← din_t]; rw [←map_sum,h,din_t,izard]
 rw [Finset.sum_congr (f:=fun v:Sweep Z=> (∑ i,payZ v _)) (g:=fun _=>∑ i,V₁ M i) rfl (fun i _=> he i), Finset.sum_const,card_univ, (Nat.cast_smul_eq_nsmul ℝ _ _).symm, smul_smul, inv_mul_cancel₀ (by positivity),one_smul] -- metavar trouble
end
-- Choose actual fiscal averages
abbrev marble(i:Site d):ℂ:=↑(footS A M i)-booth A M i
abbrev mare := patrol (fun f:Sweep Z=> chart f) (marble A) M
abbrev mace := patrol (fun f:Sweep Z=>chute f) (fun M w=> (massX A M w:ℂ)) M
lemma civic: mare A N' i=payZ f (mare A M (Λ i)):= porch M f _ _ (fun f k i=>goldM ..) i
lemma vaultT: mace A N' r'=payZ f (mace A M (chute f r')):= porch M f _ _ (fun f k i=>goldB ..) r'
variable {U₁ U₂ U₃ U₄ U₅ U₆:ℝ}{n:ℕ}{Φ:nomA N P B→ℂ}
variable (P':Client A M W)(K_: Thu T x A.unit A.post A.LawQ A.hot K n U₁ U₂ U₃ U₄ U₅ U₆ Φ)(hf:A.post+76≤A.loft)
lemma pin_z(f:Sweep N)(r:ℝ): payZ f (r:ℂ)=r:=by unfold payZ cSignX; split; simp; rfl
include P' K_ hf xw pu ρ h ph t hA hB ht hi hm hv hz
lemma profit (p:∀ f:Sweep Z,Client A (rot f M) (male e G f W)): ∑ i, mare A M i=∑ i,marble A M i:=by
 refine portE M _ _ ?_ (fun _ _=>rfl); intro f; unfold marble; rw [sum_sub_distrib,sum_sub_distrib,← Complex.ofReal_sum,← Complex.ofReal_sum, foot_v A M h hA hB f, lens_s A M h hv hz hA hB ht hi hm f W ph t xw P' K_ hf ρ pu (p f),← din_t f ((_:ℂ)-_),map_sub,din_t,din_t,pin_z] -- tune order
omit P' K_ hf xw t ph ht hi hm
lemma purchase(r:Ready T x)(t':1000≤radiusB x)(h':Portus A M)(p:∀ f:Sweep Z,Portus A (rot f M)) : ∑ i,mace A M i=∑ i,(massX A M i:ℂ):= by
 apply portE M; swap; · intro f i; exact congrArg Complex.ofReal (wind_p ..).symm
 intro f; rw [← Complex.ofReal_sum,←Complex.ofReal_sum,pin_z,mass_f A M h hv hz hA hB f ρ pu r t' (p f) h']
end YM.CF.Tye
