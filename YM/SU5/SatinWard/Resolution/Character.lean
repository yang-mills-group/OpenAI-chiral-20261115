import YM.SU5.SatinWard.Resolution.Motion
import SatinThinFrost
/-!
# Adapting Waxy's stabilizer average (SatinThin{Frost,Homage}) to the physical characters
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
variable {N n B:Side}{P:BudgetPoint}{h A C d Q:ℝ}{L:ℕ}


structure SweepSign(n:Side) where
 group : Subgroup (Sweep n)
 fits : group ≤ twoPlanes n
 translations (c:Site n) : Sweep.mk 1 c false ∈ group
 sgn : Sweep n→ℝ
 mult {s t} (h:s∈group)(g:t∈group) : sgn (s*t) = sgn s * sgn t
 sq {s}(h:s∈group) : sgn s * sgn s=1
 space (c:Site n) : sgn (Sweep.mk 1 c false)=1

lemma SweepSign.abs_sgn (χ:SweepSign n){s:Sweep n}(h:s∈χ.group) : |χ.sgn s|=1:= by
 have e:= χ.sq h
 rcases le_or_gt 0 (χ.sgn s) with h|h
 · rw [abs_of_nonneg h]; nlinarith
 · rw [abs_of_neg h]; nlinarith
section
open Classical
namespace SweepSign
variable (χ:SweepSign n) (x y z:Site n) (s:Sweep n)
abbrev ways (χ:SweepSign n)(x y:Site n): Finset (Sweep n):=univ.filter (fun s=>s∈χ.group ∧ Earlier s x y)
lemma ways_iff : s∈ ways χ x y ↔ s∈χ.group ∧ Earlier s x y:=by simp [ways]
lemma anyWay : (ways χ x y).Nonempty:=⟨Sweep.mk 1 (x-y) false,(ways_iff ..).2 ⟨χ.translations _,earlier_translate ..⟩⟩
abbrev reprice (χ:SweepSign n) (x y:Site n) :ℝ:= ((ways χ x y).card:ℝ)⁻¹
lemma reprice_pos : 0< reprice χ x y:= inv_pos.mpr (by exact_mod_cast card_pos.mpr (anyWay χ x y))
lemma reprice_pr (r:ℝ) : reprice χ x y*((ways χ x y).card * r)=r:= inv_mul_cancel_left₀ (by exact_mod_cast (card_pos.mpr (anyWay χ x y)).ne') _
lemma sameWay (g:s∈χ.group)(w: Earlier s x y) (j:Sweep n): j ∈ ways χ y z ↔ s*j∈ ways χ x z:=by
 rw [ways_iff,ways_iff]; constructor; exact fun k=> ⟨χ.group.mul_mem g k.1,w.prod k.2⟩
 intro t; rw [← inv_mul_cancel_left s j]; exact ⟨χ.group.mul_mem (χ.group.inv_mem g) t.1,w.backward.prod t.2⟩
lemma reprice_eq (g:s∈χ.group)(w: Earlier s x y): reprice χ y z=reprice χ x z:=by
 rw [reprice,reprice,card_equiv (Equiv.mulLeft s)]; intro i; exact sameWay χ x y z s g w i -- check
end SweepSign
end
namespace Waxy
open SweepSign
variable {V:Type*}[AddCommGroup V][Module ℝ V](P:Sweep n→ V →ₗ[ℝ] V)
  (multE:∀ s t:Sweep n,∀ k:V,P (s*t) k= P s (P t k)) (x y z:Site n)

variable (χ : SweepSign n) (L: V)
abbrev alleyS (P:Sweep n→ V→ V)(D:V): Site n→ V:=fun i=> reprice χ i y • ∑ s∈ ways χ i y,χ.sgn s • P s D
noncomputable abbrev orbitAverage : Site n→V:= alleyS y χ (fun s=>P s) L
section
include multE
/- With reference y. -/
lemma orbitAvg_c (s:Sweep n)(p:s∈χ.group)(q: Earlier s x z): P s (orbitAverage P y χ L z)= χ.sgn s • orbitAverage P y χ L x:=by
 rw [orbitAverage,alleyS,reprice_eq χ x z y s p q,map_smul,map_sum]; simp_rw [map_smul]; rw [smul_comm (χ.sgn s),Finset.smul_sum (r:=χ.sgn s)]
 refine congrArg (fun v:V=> reprice χ x y • v) (sum_equiv (Equiv.mulLeft s) (sameWay χ x z y s p q) (fun i (ii:i∈ways χ z y)=>?_)); rw [← multE]; change _= χ.sgn s • χ.sgn (s*i) • _; rw [χ.mult p ((ways_iff ..).mp ii).1,smul_smul,←mul_assoc,χ.sq p,one_mul]; rfl
end

def SignBent (χ:SweepSign n)(P:Sweep n→ V →ₗ[ℝ] V) (a:Site n→ V): Prop:=∀ s∈χ.group,∀ x y, Earlier s x y→ P s (a y)=χ.sgn s • a x
lemma orbitAvg_owned (a:Site n→V)(h:SignBent χ P a) : orbitAverage P y χ (a y)=a:=by
 funext i; unfold orbitAverage alleyS; have q:(ways χ i y).card • a i=∑ s∈ways χ i y,χ.sgn s • P s (a y):=by
    rw [←sum_const]; refine sum_congr rfl fun j (_r:j∈ways χ i y)=>?_ ; obtain ⟨l,p⟩:=(ways_iff ..).mp _r; rw [h j l i y p,smul_smul,χ.sq l,one_smul]
 rw [show (fun s: Sweep n=> ((P s): V→ V))=fun s v=>P s v from rfl] -- tune redundant
 rw [←q]; unfold reprice; rw [←Nat.cast_smul_eq_nsmul ℝ]; exact inv_smul_smul₀ (by exact_mod_cast (card_pos.mpr (anyWay χ i y)).ne') _

lemma orbitAvg_E (o: Site n)(z:RegBudget n): SignBent χ Eρ (orbitAverage Eρ o χ z):=by
 apply fun s h x y t=> orbitAvg_c Eρ (fun s t x=> ?_) x o y χ z s h t
 funext i U; change suit_Y _ (x (moveHub _ i) (flashA _ U))=suit_Y _ (suit_Y _ _); rw [moon_Y,mul_inv_rev]; simp only [Function.comp_apply,step_k,lights] -- step index order s,t
lemma orbitAvg_F (o: Site n)(z:Copy n): SignBent χ Fρ (orbitAverage Fρ o χ z):=by
 apply fun s h x y t=> orbitAvg_c Fρ (fun s t x=> ?_) x o y χ z s h t
 funext U; change suit_Y _ (x (yellA _ U))=suit_Y _ (suit_Y _ _); rw [moon_Y,mul_inv_rev]; simp only [Function.comp_apply,yell_t]
lemma orbitAvg_K (o: Site n)(z:Cusp n): SignBent χ Kρ (orbitAverage Kρ o χ z):=by
 apply fun s h x y t=> orbitAvg_c Kρ (fun s t x=> ?_) x o y χ z s h t
 funext i D U; change suit_Y _ (x (moldA _ i) (actY _ D) (yellA _ U))=suit_Y _ (suit_Y _ _); rw [moon_Y,mul_inv_rev]; simp only [hush_k,tape_B,Function.comp_apply,yell_t]
lemma orbitAvg_t (o: Site n)(z:ℂ): SignBent χ tρ (orbitAverage tρ o χ z):=by
 apply fun s h x y t=> orbitAvg_c tρ (fun s t x=> ?_) x o y χ z s h t
 simp only [offsetWt]; rw [mul_inv_rev,←warX]; unfold Spire.payZ; cases wageZ s⁻¹<;>cases wageZ t⁻¹<;>rfl -- unfolds? simplify

end Waxy
section Accounting
open Tap Mew Waxy
open SweepSign

lemma cost_shape_translation (x y: Site n)(U:ArcΦ):
    turnD (Sweep.mk 1 x false) U = turnD (Sweep.mk 1 y false) U := rfl

lemma average_ice (χ:SweepSign (mid N B))(V:HavenL (mid N B) P L)
    (o:Site (mid N B))(h0:0≤h)(F:Copy (mid N B))(E:RegBudget (mid N B))
    (K:Cusp (mid N B))(t:ℂ)(Y:ArcΦ)(p:Ice L o P h A Q C F E K t Y) :
  let X:=alleyS o χ turnD Y o
  (∀ g∈χ.group, turnD g X=χ.sgn g • X) ∧
  ∀ x:Site (mid N B),
    Ice L x P h (duty_Q P.order P.power*A) (strive_E P.order*Q) C
      (orbitAverage Fρ o χ F x) (orbitAverage Eρ o χ E x)
      (orbitAverage Kρ o χ K x) (orbitAverage tρ o χ t x) X := by
 intro X
 let Z:=alleyS o χ turnD Y
 have hT(x:Site (mid N B)): Ice L x P h (duty_Q P.order P.power*A) (strive_E P.order*Q) C
      (orbitAverage Fρ o χ F x) (orbitAverage Eρ o χ E x)
      (orbitAverage Kρ o χ K x) (orbitAverage tρ o χ t x) (Z x):= by
    let S:= ways χ x o
    have hp(s:Sweep (mid N B))(u:s∈S): Ice L x P h (duty_Q P.order P.power*A) (strive_E P.order*Q) C (χ.sgn s • Fρ s F) (χ.sgn s • Eρ s E) (χ.sgn s • Kρ s K) (χ.sgn s • tρ s t) (χ.sgn s • turnD s Y):=by
       obtain ⟨s',x'⟩:=(ways_iff ..).1 u
       have w:= realV x (χ.sgn s) (restoreTwo s (χ.fits s') x o x' h0 V p) h0
       rw [χ.abs_sgn s',one_mul,one_mul,one_mul] at w; exact w
    have hu:=realV x (reprice χ x o) (ice_sum x S _ _ _ _ _ _ _ _ hp h0) h0
    rw [abs_of_pos (reprice_pos ..)] at hu; simpa only [sum_const,nsmul_eq_mul,S,reprice_pr] using hu
 have moves(x:Site (mid N B))(y:Site (mid N B))(s:Sweep (mid N B))(hq:s∈χ.group)(h:Earlier s x y) : turnD s (Z y)=χ.sgn s • Z x:=by
    have hp:= wheelTwo s (χ.fits hq) x y h h0 V (hT y).axle; have hv:= real_E x (χ.sgn s) (hT x).axle h0
    have hu: base_Q s (orbitAverage Eρ o χ E y) = χ.sgn s • orbitAverage Eρ o χ E x:= orbitAvg_E χ o E s hq x y h
    rw [hu] at hp
    have hh:chose L P (Φrap (mid N B) x 10):=atRim V x; let W:= (Φrap (mid N B) x 10); have u:=(hp.flair W hh).2; rw [if_pos rfl] at u; have f:=(hv.flair W hh).2; rw [if_pos rfl] at f; exact u.symm.trans f
 have everywhere (x:Site (mid N B)): Z x = X := by
    have h₁:= moves x o _ (χ.translations _) (earlier_translate ..)
    have h₂:= moves o o _ (χ.translations _) (earlier_translate ..)
    rw [χ.space, one_smul] at h₁ h₂
    exact h₁.symm.trans h₂ -- translation rfl
 constructor
 · intro g hg; let i:Site (mid N B):=(castX g).mills _ o
   rw [← everywhere o]; have p:= moves i o g hg ((earlier_mills ..).mpr rfl)
   rwa [← show Z o= Z i from (everywhere o).trans (everywhere i).symm] at p
 · exact fun x=> everywhere x ▸ hT x

lemma castPal_smul (s t:Bool)(U:UNI SpinIdx)(Y:Pal)(r:ℝ): castPal s t U (r • Y)=r • castPal s t U Y:= by
 cases t <;> simp [castPal,Thera.jazz,singT,twist_formula]
lemma castPal_price (s t:Bool)(U:UNI SpinIdx)(Y:Pal): ‖castPal s t U Y‖=‖Y‖:= by
 cases t <;> simp only [castPal,Thera.jazz,Bool.false_eq_true,↓reduceIte,norm_neg,norm_star] <;>
   exact singN ..

def jetTurn (s:Sweep n)(X:partZ):partZ := (costDome s (0,X)).2
lemma turn_formula (s:Sweep n)(X:Dome): costDome s X = (castPal s⁻¹.charge (detX s⁻¹.s) (spinU s⁻¹.charge s⁻¹.s) X.1, jetTurn s X.2):= rfl
private lemma toll_sub(s:Signed)(a b:Bool)(U:UNI SpinIdx)(X Y:partZ): (coinArc s a b U (0,X-Y)).2=(coinArc s a b U (0,X)).2-(coinArc s a b U (0,Y)).2 := by
 cases b <;> (apply Prod.ext) <;> funext i <;> simp [coinArc,pal_sub,smul_sub]
lemma jetTurn_sub(s:Sweep n)(X Y:partZ): jetTurn s (X-Y)=jetTurn s X-jetTurn s Y:=toll_sub ..
private lemma toll_smul(s:Signed)(a b:Bool)(U:UNI SpinIdx)(X:partZ)(r:ℝ): (coinArc s a b U (0,r • X)).2=r • (coinArc s a b U (0,X)).2:=by
 cases b <;>  (apply Prod.ext) <;> funext i <;> simp [coinArc,castPal_smul,smul_comm r]
lemma jetTurn_smul(s:Sweep n)(X:partZ)(r:ℝ):jetTurn s (r • X)=r • jetTurn s X := toll_smul ..
open StressFlux
private lemma coin_bound (p:Signed)(a b:Bool)(U:UNI SpinIdx)(X:Dome) : ‖(coinArc p a b U X).2‖ ≤ ‖X.2‖:=by
 let T:=‖X.2‖
 have B(i:Axis)(u:Axis→ Pal)(g:‖u‖ ≤ T):‖sign p i • castPal a b U (u (p.perm i))‖ ≤ T:=by
    have z:‖sign p i‖=1:=by unfold sign; split<;>simp
    rw [norm_smul,z,one_mul]; exact (castPal_price ..).le.trans ((norm_le_pi_norm ..).trans g)
 unfold coinArc; rw [Prod.norm_def]; refine max_le ?_ ?_ <;> apply (pi_norm_le_iff_of_nonneg (norm_nonneg X.2)).mpr <;> intro i <;> apply B <;> split <;> first|exact norm_snd_le _|exact norm_fst_le _
lemma jetTurn_le(s:Sweep n)(X:partZ):‖jetTurn s X‖≤‖X‖:=coin_bound _ _ _ _ (0,X)

-- keep the three different allowances. Work on scale h^2 directly
private lemma reprice_bound {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
    (χ:SweepSign n)(o:Site n)(F:Sweep n→V)(K:V)(a e:ℝ)(z:0≤a)
    (h:∀ s∈ways χ o o,‖F s-K‖*a≤e): ‖reprice χ o o • (∑ s∈ways χ o o,F s)-K‖*a≤ e:= by
 let x:=reprice χ o o; let S:= ways χ o o; have he:0<x:= reprice_pos ..
 have eq: x • (∑ s∈S,F s)-K=x • ∑ s∈S,(F s-K):=by
    rw [Finset.sum_sub_distrib,smul_sub,sum_const,← Nat.cast_smul_eq_nsmul ℝ]; congr 1; exact (inv_smul_smul₀ (by exact_mod_cast (card_pos.mpr (anyWay χ o o)).ne') K).symm
 change ‖x • (∑ s∈S,F s)-K‖*a≤ _; rw [eq,norm_smul,Real.norm_of_nonneg he.le,mul_assoc]
 have hp:‖∑ s∈S,(F s-K)‖ *a ≤ S.card*e := calc
    _ ≤ (∑ s∈S,‖F s-K‖) *a:=mul_le_mul_of_nonneg_right (norm_sum_le ..) z
    _ ≤ _:= by rw [sum_mul]; exact (sum_le_sum h).trans (by rw [sum_const,nsmul_eq_mul]) -- tune
 exact (mul_le_mul_of_nonneg_left hp he.le).trans (reprice_pr ..).le

theorem reprice_alpha (χ : SweepSign n)(o:Site n)(R Y:ArcΦ)(W:∀ s∈χ.group,turnD s R=χ.sgn s • R)
    (L:Side)(h Q B V₀ V₁ V₂:ℝ)(P X:BudgetPoint)(t:ℝ)(p:αPrice L h Q B V₀ V₁ V₂ R Y P X (t:ℂ)):
    αPrice L h Q B V₀ V₁ V₂ R (alleyS o χ turnD Y o) P X (t:ℂ):=by
 let E:=alleyS o χ turnD Y o; let A:= ways χ o o; let u:= reprice χ o o
 have fix {s:Sweep n}(v:s∈A): R=χ.sgn s • turnD s R:=by
    have w:= ((ways_iff ..).1 v).1; rw [W s w,smul_smul,χ.sq w,one_smul]
 have sign {s:Sweep n}(v:s∈ A): ‖χ.sgn s‖=1:= χ.abs_sgn ((ways_iff ..).1 v).1
 let J:=κprobe naxR L h Q B (t:ℂ) R
 constructor
 · let T:=ζtap L P X (t:ℂ) R
   let F(s:Sweep n):= χ.sgn s • costSkate s Y.1
   change ‖E.1-T‖≤ V₀*J; rw [show E.1=u • ∑ s∈A,F s from ?_]
   · refine (mul_one _).symm.le.trans (reprice_bound χ o F T 1 _ zero_le_one (fun s v=>?_)) -- tune
     rw [mul_one]; unfold F; nth_rw 1 [show T=χ.sgn s • costSkate s T from ?_]; swap
     · unfold T ζtap; rw [Complex.coe_smul,Complex.coe_smul,cost_scale,cost_scale,smul_comm (χ.sgn s) _ _,smul_comm (χ.sgn s) _ _,← show R.1=χ.sgn s • costSkate s R.1 from congrArg Prod.fst (fix v)] -- occurrence loop
     rw [←smul_sub, ←cost_sub,norm_smul,sign v,one_mul]; exact (cost_contract ..).trans p.red
   unfold E alleyS; simp only [Prod.smul_fst,Prod.fst_sum]; rfl
 · let T:= ζVtap L (t:ℂ) R; let Cφ(s:Sweep n):= castPal s⁻¹.charge (detX s⁻¹.s) (spinU s⁻¹.charge s⁻¹.s)
   let F(s:Sweep n):=χ.sgn s • Cφ s Y.2.1
   change ‖E.2.1-T‖*h^2 ≤ V₁*J; rw [show E.2.1=u • ∑ s∈A,F s from ?_]
   · apply reprice_bound χ o F T (h^2) _ (sq_nonneg _)
     intro s v; change ‖χ.sgn s • castPal _ _ _ _ - T‖*h^2 ≤ _; nth_rw 1 [show T=χ.sgn s • castPal s⁻¹.charge (detX s⁻¹.s) (spinU s⁻¹.charge s⁻¹.s) T from ?_]; swap
     · unfold T ζVtap; rw [←Complex.ofReal_pow,Complex.coe_smul,Complex.coe_smul,castPal_smul,castPal_smul,smul_comm (χ.sgn s) _ _,smul_comm (χ.sgn s) _ _,← show R.2.1=χ.sgn s • (Cφ s R.2.1) from congrArg (Prod.fst ∘ Prod.snd) (fix v)] -- C def issue
     rw [←smul_sub,←pal_sub,norm_smul,castPal_price,sign v,one_mul]; exact p.violet
   unfold E alleyS; simp only [Prod.smul_snd,Prod.smul_fst,Prod.snd_sum,Prod.fst_sum]; rfl
 · let T:= ξtap L (t:ℂ) R; let F(s:Sweep n):=χ.sgn s • jetTurn s Y.2.2
   change ‖E.2.2-T‖*h^2 ≤ _; rw [show E.2.2=u • ∑ s∈A,F s from ?_]
   · apply reprice_bound χ o F T (h^2) _ (sq_nonneg _)
     intro s v; unfold F; nth_rw 1 [show T=χ.sgn s • jetTurn s T from ?_]; swap
     · unfold T ξtap; rw [←Complex.ofReal_mul,Complex.coe_smul,Complex.coe_smul,jetTurn_smul,jetTurn_smul,smul_comm (χ.sgn s) _ _,smul_comm (χ.sgn s) _ _,← show R.2.2=χ.sgn s • jetTurn s R.2.2 from congrArg (Prod.snd ∘ Prod.snd) (fix v)]
     rw [←smul_sub,←jetTurn_sub,norm_smul,sign v,one_mul]; exact (mul_le_mul_of_nonneg_right (jetTurn_le ..) (sq_nonneg _)).trans p.verd
   unfold E alleyS; simp only [Prod.smul_snd,Prod.snd_sum]; rfl
end Accounting
end YM.CF.QuadClock
