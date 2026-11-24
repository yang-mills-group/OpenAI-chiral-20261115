import GaugeFieldConstruction.MetricUpΛ
/-!
 # Canonical tensor extension

 Need SAME normalization both moment & generator. Improvement of M7 obtains proper law, could a priori change principal+mixing even in the given normalization. Need re-test. Cannot assume no order five mixing with the mixed leg! Four-by-four Ward equalities not S-conservation all Grades. We buy a smaller separator using div and translation tests together. Only requires U4 EXTERNAL; so smells live in T_S2.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S)
namespace FirstPackMars
open Wick Mirror Invoice Raster
variable (H:FirstPackMars p Y) (G:NSF.Table.Hierarchy (BellTableMars p Y)) (W:Blush S atTop u)
local notation "l₄"=> Calibration.lift four
open Row Record
local notation "J♦"=> p.J
local notation "JΔ"=> TotalStarsMars p
-- exact centering in money.
abbrev InVoiceCΛ (p:Ticket u C)(Y:AreaQc S):Prop:=∀ (x:ΧiMars),TerraMars p Y (n:=1) ![x] 0=x.1
include H G
lemma CoinTΛ (g:SO)(v:ΧiMars)(w:InVoiceCΛ p Y): (compassPiMars p g v).1=v.1:= by
 let F:Fin 1→ΧiMars:= ![v]
 have u:(0:Points 1)∈conf 1:= fun _ _ _=> Subsingleton.elim ..
 have ht:= VitaPiiotMars H G g 1 F 0 u
 have he: (compassPiMars p g) ∘ F=(![compassPiMars p g v]:Fin 1→ΧiMars):=by ext1 i; fin_cases i; rfl
 rw[he,show motionMoonMars g 0 (n:=1)=0 from ((VoyageMars g).map_zero : _)] at ht
 exact (w _).symm.trans (ht.trans (w v))
lemma TotCenterΛ (w:InVoiceCΛ p Y)(i j:Axis): centered (JΔ i j):=by
 let M:=LinearMap.fst ℂ ℂ (UG four × Fragment (UF four) × Fragment (UX four))
 have X(g:SO): M (unitsMars p g i j)=0:=by
    unfold unitsMars TensPitchMars pileMoonMars; simp_rw [map_sum,map_smul]; apply sum_eq_zero; intro a _; apply sum_eq_zero; intro b _; have hx:M (compassPiMars p g (J♦ a b))=0:=(CoinTΛ p Y H G g _ w).trans (p.taste a b).1; rw[hx,smul_zero]
 let A:=M.restrictScalars ℝ
 let D:=fun a:Axis=> if a=i then A else 0
 have E(f:Axis→ΧiMars) : ∑ a:Axis,D a (f a)=M (f i):=by rw[sum_eq_single i]; simp [D,A]; intro b _ u; simp[u,D]; simp
 change M _ = _; exact (E (fun a=>JΔ a j)).symm.trans (sumFrameRateMars D j 0 (fun g=>(E (fun a=>unitsMars p g a j)).trans (X g)))
omit H G in
private lemma signedParcelΛ (s:Signed)(i j:Axis): spinFrame four s (JΔ i j)=pay ((s.flip i).xor (s.flip j)) (JΔ (s.perm i) (s.perm j)):=by
 rw [totalImproperMars]; unfold pileMoonMars; simp_rw[parcelInvMars]; rw[sum_eq_single (s.perm i)]
 · rw[sum_eq_single (s.perm j)]; unfold parcelMars; change (_*_) • _=_; simp only [show s.ortho.val=s.matrix from rfl,Signed.matrix_at,↓reduceIte]; cases s.flip i <;> cases s.flip j <;> simp
   · intro b _ h; simp [parcelMars,show s.ortho.val=s.matrix from rfl,Signed.matrix_at,Ne.symm h]
   simp
 · intro b _ h; simp [parcelMars, show s.ortho.val=s.matrix from rfl,Signed.matrix_at,Ne.symm h]
 simp
abbrev AFluxΛ (w:InVoiceCΛ p Y): SymT:= by
 let X(j:Sym):= JΔ j.val.1 j.val.2
 have ht(i j:Axis): X (ordered i j)=TotalStarsMars p i j:=by
     unfold X ordered; split
     · exact totalSymMars p j i
     · rfl
 exact ⟨X,(fun i=> ⟨TotCenterΛ p Y H G w _ _, fun v=> totalFlavorMars p v _ _⟩), fun i s=>by rw [← ordered_same i]; simp_rw[ht,sym_turn,ht,fee_turn]; exact signedParcelΛ p s _ _⟩ -- needs constructor conjunction
lemma AFlameΛ (w:InVoiceCΛ p Y)(i j:Axis):pens (AFluxΛ p Y H G w) i j=TotalStarsMars p i j:=by
 unfold AFluxΛ pens ordered; split
 · exact totalSymMars p j i
 · rfl
-- price without dim5 smoothness
variable (w:InVoiceCΛ p Y)
local notation "MikeΦ"=>AFluxΛ p Y H G w
-- maybe illegal greek notation
abbrev RidgeπΛ := AFluxΛ p Y H G w - p.dawn.tect.val
lemma RidgeRentΛ(i j:Axis): pens (RidgeπΛ p Y H G w) i j= TotalStarsMars p i j - p.J i j:=
 (show pens (MikeΦ-p.dawn.tect.val) i j=pens MikeΦ i j- p.J i j from rfl).trans (by rw[AFlameΛ])
local notation "Z_Δ"=> RidgeπΛ p Y H G w
local notation "ΤΨ" a:max=> Fin.cons a
lemma PointOutΛ : ΑtraDivΛ (S:=S) (Z_Δ):=by
 intro a q f
 simp_rw [RidgeRentΛ, map_sub, LinearMap.sub_apply, sum_sub_distrib]; apply sub_eq_zero.mpr
 have hS (A:Axis→ΧiMars) (h:∀ x∈conf 2,(∑ i:Axis,D (direction front i) (TerraMars p Y ![q,A i]) x)=0): (∑ i:Axis, paid front i (S.spot (other (l₄ q)) front (l₄ (A i))) f)=0:=by
    let T(i:Axis):= TerraMars p Y ![q,A i]
    have hz(i v): S.spot (other (l₄ q)) front (l₄ (A i)) v=v.applyTo (T i):=by
        rw [roll_tie,io,show (![l₄ q,l₄ (A i)]:Fin 2→UV five)=l₄ ∘ ![q,A i] from by funext i; fin_cases i<;>rfl]; exact BillingMars ..
    simp_rw [Fathom.pays,hz]; unfold T; simp_rw [← currentMars]
    let X(i:Axis):= Analysis.D (direction front i) (T i)
    have hI(i:Axis):ContinuousOn (X i) (conf _):=fun x e=> (dSmooth (m:=∞) (TerraAt p Y _ x e) _ (by simp)).continuousAt.continuousWithinAt
    have he:= (YM.Test.weak_null (K:=fun s:Points 2=>∑ i:Axis,X i s) (continuousOn_finsetSum _ (fun i _=> hI i))).2 h f
    unfold YM.Test.applyTo at he; simp_rw [mul_sum] at he; rw [integral_finsetSum _ (fun j _=>f.smearing (hI j))] at he; exact he
 let F:Fin 2→ΧiMars:=![q,q]
 have hv(B:ΧiMars):update F front B=![q,B]:=by ext1 i; fin_cases i<;>simp[front,F]
 refine (hS _ (fun x h=>?_)).trans (hS _ (fun x h=>?_)).symm
 · have hz:=TotalDivergenceMars H G front F x h a; simp_rw[hv] at hz; exact hz
 have hz:= divMars p Y front F a x h; simp_rw [hv] at hz; exact hz
-- contour operation tested only at bulbs. iterate. via integrated ray lattice
lemma pointCardΛ (q:ΧiMars)(i j:Axis)(F:Fin n→ΧiMars)(b:Bulb): RyeMars (TerraMars p Y (Fin.cons q F)) (Payroll.ticket i) b j i= fun x=>FlossMars p Y F x b j q:=by
 ext1 x; unfold RyeMars WrapMars; apply integral_congr_ae; refine Eventually.of_forall fun z=> ?_; change (D _ _ _ * basis i i) • _=_; rw [show basis i i=1 by simp,mul_one]; rfl
lemma PointWardΛ : ΑtraMarkΛ (S:=S) Z_Δ:=by
 intro i x y f J H'
 let V:= (![y,x]:Fin 2→ΧiMars)
 let U(i:Axis):= pens Z_Δ i
 let D0:= {x|BreatherMars J front x}
 have h: tsupport f⊆D0:=fun x e=> ⟨f.tsupport_subset e,H'.bulb x e,H'.direct x e⟩
 rw [deconstant f]
 let B(j:Axis):=RyeMars (TerraMars p Y (Fin.cons (U j i) V)) (Payroll.ticket i) J j i
 let ℓ :Finset Axis:=Finset.univ
 have hx (j:Axis): S.tagged (tie (l₄ y) (l₄ x)) (prints Z_Δ j i) (lace f (J.LED j) (H'.cared j))=f.applyTo (B j):=by
    rw [show tie (l₄ y) (l₄ x)=l₄ ∘ V from (io ..).trans (by funext i; fin_cases i<;>rfl)]; unfold B; rw [SoilEarnMars _ (TerraSm p Y _) _ J _ _ front f H']; unfold prints; rw [← stratLMars, BillingMars p Y]; congr 1; ext1 p; change _= testcut _ _ _ _ _ _ _; simp only[testcut_v, Payroll.ticket,basis_eq,↓reduceIte,mul_one]; rfl
 change (∑ j:Axis,S.tagged _ (prints _ j i) _)=0; rw [sum_congr rfl (fun j _=>hx j)]
 have he(j:Axis):ContinuousOn (B j) D0:=SoilCanMars _ (TerraSm p Y _) _ _ _ _ _
 unfold YM.Test.applyTo; rw [← integral_finsetSum _ (fun j _=> paleM D0 (B j) (B j) (he j) f h (BreathingMars ..))]
 refine integral_eq_zero_of_ae (Eventually.of_forall fun z=>?_); change (∑ i:Axis,f z*B i z)=0; rw [← mul_sum]; by_cases v:z∈tsupport f; swap
 · rw[image_eq_zero_of_notMem_tsupport v,zero_mul]
 have hp:BreatherMars J front z:=h v
 rw [show (∑ j:Axis,B j z)=0 from ?_,mul_zero]
 have hy(j:Axis):B j z= FlossMars p Y V z J j (JΔ j i) - FlossMars p Y V z J j (J♦ j i):= by
    unfold B U; rw[pointCardΛ p Y H G, RidgeRentΛ]
    exact map_sub (FlintMars p Y V z J front hp j) _ _ -- tune dependencies
 rw [sum_congr rfl (fun j _=>hy j),sum_sub_distrib, ← PoemMoonMars p Y front V z J hp, ← OrbitFluxMars H G front V z J hp, sub_self]
include w W in
lemma TicketUnchangedΛ (i j):TotalStarsMars p i j=p.J i j:=by
 apply sub_eq_zero.mp
 rw [←RidgeRentΛ p Y H G w, NobodyBlankΛ p W _ (PointOutΛ p Y H G w) (PointWardΛ p Y H G w)]; rfl
#print axioms TicketUnchangedΛ
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
