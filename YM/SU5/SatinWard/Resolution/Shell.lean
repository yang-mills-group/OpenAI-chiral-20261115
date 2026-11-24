import YM.SU5.SatinWard.Resolution.Prominence
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
-- monetary discrepancy; include absolute comparator term.
structure Disp (r a:ℝ)(X Y:ℂ):Prop where
 nn:0≤a
 shadow : ‖Y‖ ≤ a
 amount : ‖X-Y‖ ≤ a/r
namespace Disp
section
variable {r v w:ℝ}{a b c d z:ℂ} (h:Disp r v a b) (u:Disp r w c d)
include h
lemma mono {W:ℝ}(p:v ≤ W)(q:r ≥ 0): Disp r W a b:= ⟨h.nn.trans p,h.shadow.trans p,h.amount.trans (div_le_div_of_nonneg_right p q)⟩
lemma increase (X:ℂ): Disp r (‖X‖*v) (X*a) (X*b):= ⟨mul_nonneg (norm_nonneg _) h.nn,(norm_mul X b).trans_le (mul_le_mul_of_nonneg_left h.shadow (norm_nonneg _)),by rw [←mul_sub,norm_mul,mul_div_assoc]; exact mul_le_mul_of_nonneg_left h.amount (norm_nonneg _)⟩ -- last rw wrong direction?
include u
lemma plus : Disp r (v+w) (a+c) (b+d):= ⟨add_nonneg h.nn u.nn,(norm_add_le ..).trans (add_le_add h.shadow u.shadow),by rw [show a+c-(b+d)=(a-b)+(c-d) from by abel,add_div]; exact (norm_add_le ..).trans (add_le_add h.amount u.amount)⟩
lemma times (w':1≤ r) : Disp r (3*v*w) (a*c) (b*d):=by
 have hp:=h.nn; have hh:=u.nn; have he:‖c‖ ≤ 2*w:= (norm_le_norm_sub_add _ d).trans ((add_le_add (u.amount.trans (div_le_self hh w')) u.shadow).trans_eq (two_mul w).symm)
 refine ⟨by positivity, (norm_mul b d).trans_le ((mul_le_mul h.shadow u.shadow (norm_nonneg _) hp).trans (by nlinarith [mul_nonneg hp hh])),?_⟩
 rw [show a*c-b*d=(a-b)*c+b*(c-d) from by ring]; apply (norm_add_le ..).trans
 rw [norm_mul,norm_mul]; have hv:0 ≤ v/r:=by positivity
 exact (add_le_add (mul_le_mul h.amount he (norm_nonneg _) hv) (mul_le_mul h.shadow u.amount (norm_nonneg _) hp)).trans_eq (by ring)
omit u h
lemma zero (r:ℝ): Disp r 0 0 0:= by constructor<;>simp
lemma SumD {ι:Type*}{X D:ι→ℂ} {a:ι→ℝ}(S:Finset ι)(h:∀ i∈S, Disp r (a i) (X i) (D i)): Disp r (∑ i∈S,a i) (∑ i∈S,X i) (∑ i∈S, D i):=by induction S using Finset.induction_on with| empty=> simp_rw [sum_empty];exact Disp.zero _| insert i S e ih=> simp only [sum_insert e]; exact (h i (mem_insert_self ..)).plus (ih fun j x=> h j (mem_insert_of_mem x))
end
end Disp
variable {R Q μ:ℝ}{d:Gaia}
lemma scape_sub (x y:Cover): scape (x-y)=scape x-scape y:=by rw [eq_sub_iff_add_eq,← scape_add,sub_add_cancel]
lemma endPaid (o:Cover)(x:Cover)(p:x∈pavilion o 2) : ‖scape (x-o)‖ ≤4:=by
 let W:= x-o; have h:‖shaftX W‖ ≤2:= (pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ)≤2)).2 fun i:Axis=> by
    have h:= (pav_v ..).mp p i; change |(((x i-o i):ℤ):ℝ)|≤2; exact_mod_cast (show |x i-o i|≤2 from abs_le.mpr (by omega))
 exact (Onyx.moor_z _).trans (by linarith)
structure Addressing (x y:Cover)(d:Gaia)(μ R Q:ℝ):Prop where
 r₀:0 ≤ μ
 lap: μ+8 ≤ R
 area:2≤‖d‖
 sizes:‖d‖≤Q
 meters:‖patchF (x-y) R - d‖ ≤ μ/R
namespace Addressing
variable {x y:Cover} (g: Addressing x y d μ R Q)
lemma pLease (g: Addressing x y d μ R Q): 1≤ R:=by linarith only [g.lap,g.r₀]
include g
lemma landed {a b:Cover} (p:a∈pavilion x 2)(q:b∈pavilion y 2) : ‖patchF (a-b) R-d‖≤ (μ+8)/R:=by
 have h:=g.pLease; let f(z:Cover):=scape z; let Z:=R⁻¹ • (f (a-x)-f (b-y)); have ht:patchF (a-b) R= patchF (x-y) R + Z:=by unfold Z patchF f; rw [←scape_sub,←smul_add,←scape_add]; congr 2; abel
 have he:‖Z‖ ≤8/R:=by
    unfold Z; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity:0≤R⁻¹)]; apply (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (endPaid _ _ p) (endPaid _ _ q))) (by positivity)).trans_eq; ring
 rw [ht,add_sub_right_comm,add_div]; exact (norm_add_le ..).trans (add_le_add g.meters he)
end Addressing
lemma sch_s (i j:Sage): ‖(sch (G:=SU.group) i j:ℂ)‖≤1:=by unfold sch; split_ifs<;> simp
include H
lemma Wclaim (Q μ:ℝ) (p:0≤μ): ∃ C:ℝ, 0≤C∧∀ (F D:PlaqAxes)(a b:Fin 4)(x y:Cover)(d:Gaia)(R:ℝ), Addressing x y d μ R Q →∀ (i j:Sage)(s:ℕ), Disp R C ((R:ℂ)^4* ↑(W s ((cornerT F x a).p,i) ((cornerT D y b).p,j))) ((sch (G:=SU.group) i j:ℂ)*specter F D d):=by
 have h:= fun (Q':PlaqAxes×PlaqAxes)=> sharpDisp H Q'.1 Q'.2 Q (μ+8) (by positivity)
 choose u e m using h; let U:= ∑ i:PlaqAxes×PlaqAxes,u i
 have hk (i):0≤u i:=(by linarith only [show 1≤u i from e i]); refine ⟨U,sum_nonneg (fun i _=>hk i),fun F D a b x y d R h i j s=>?_⟩
 let p:=(F,D); let uW:=u p; let X:=(cornerT F x a).p; let Y:=(cornerT D y b).p; let L:=X.1-Y.1; let K:=(sch (G:=SU.group) i j:ℂ); let Z:=(R:ℂ)
 obtain ⟨v,t⟩:= m p R h.pLease h.lap s L d h.area h.sizes (h.landed (ends_corner ..) (ends_corner ..)); let W':=wObj (W s) F D L;
 have ho: Disp R uW (Z^4* W') (specter F D d):= ⟨hk p,v,t⟩
 change Disp R U ((R:ℂ)^4 * (W s ((X.1,F),i) ((Y.1,D),j):ℂ)) _
 rw [show (W s _ _:ℂ)= K*W' from H.pigment F D i j s X.1 Y.1,mul_left_comm]
 exact (ho.increase K).mono ((mul_le_of_le_one_left (hk p) (sch_s ..)).trans (single_le_sum (fun i _=>hk i) (mem_univ p))) (zero_le_one.trans h.pLease)
abbrev sector2 (F G A B:PlaqAxes)(i j:Sage) (d:Gaia):ℂ:=
   ((sch (G:=SU.group) i j:ℂ)*specter F A d)*((sch (G:=SU.group) i j:ℂ)*specter G B d)+
   ((sch (G:=SU.group) i j:ℂ)*specter F B d)*((sch (G:=SU.group) i j:ℂ)*specter G A d)
omit H
lemma moments2scene (w:HorizonLens→ HorizonLens→ℝ) {p q a b:Face ℤ}(i j:Sage) {C R:ℝ}{P Q A B:ℂ} (e:1≤R) (p':Disp R C ((R:ℂ)^4*w (p,i) (a,j)) P)(q': Disp R C ((R:ℂ)^4*w (q,i) (b,j)) Q)(a': Disp R C ((R:ℂ)^4*w (p,i) (b,j)) A)(b':Disp R C ((R:ℂ)^4*w (q,i) (a,j)) B): Disp R (6*C*C) ((R:ℂ)^8*nextSea w p q a b i i j j) (P*Q+A*B):=by
 unfold nextSea; have ht: (3*C*C)+(3*C*C)=6*C*C:=by ring
 have h:= (p'.times q' e).plus (a'.times b' e); rw [ht] at h; refine Eq.subst (motive:=fun z=> Disp R (6*C*C) z (P*Q+A*B)) ?_ h; push_cast; ring
abbrev mintBody (F G A B:PlaqAxes)(d:Gaia):ℂ:= (Fintype.card Sage:ℂ)*(specter F A d*specter G B d+specter F B d*specter G A d)
lemma fuseColor (F G A B:PlaqAxes) (d:Gaia): ∑ i:Sage,∑ j:Sage, sector2 F G A B i j d=mintBody F G A B d:=by
 let C:= specter F A d*specter G B d+specter F B d*specter G A d; unfold mintBody; have he(i:Sage): ∑ j:Sage, sector2 F G A B i j d=C:=by
    rw [sum_eq_single i]; simp [sector2,C,sch]; intro j _ h; simp [sector2,sch,Ne.symm h]; simp
 simp_rw [he]; rw [sum_const,card_univ,nsmul_eq_mul]
include H
lemma scenery (Q μ:ℝ)(p:0≤μ):∃ C:ℝ,0≤C ∧∀ (x y:Cover)(d:Gaia)(R:ℝ), Addressing x y d μ R Q →∀ (s:ℕ)(F G A B:PlaqAxes), Disp R C ((R:ℂ)^8 * employ2 (W s) F G A B x y) (mintBody F G A B d):=by
 obtain ⟨C,z₀,v⟩:= Wclaim H Q μ p; let w:= ∑ _i:Sage,∑ _j:Sage,(6*C*C); let k:ℝ:=1/16; let K:ℝ:= ∑ _i:CupCoin,k*∑ _j:CupCoin,k*w
 have hw:0≤w:=sum_nonneg (fun i _=>sum_nonneg fun j _=>by nlinarith); have ht:0≤k:=by unfold k; positivity
 have he {x:ℝ}: ‖(x:ℂ)‖=|x|:=(Complex.norm_real x).trans (Real.norm_eq_abs x)
 refine ⟨K,sum_nonneg fun i _=> mul_nonneg ht (sum_nonneg fun i _=>mul_nonneg ht hw), fun x y d R h s F G A B=>?_⟩
 let Z:=W s; let X:=(R:ℂ); let Y:=mintBody F G A B d; let P'(i j:CupCoin):=Abacus.chroma Z (cornerT F x i.1) (cornerT G x i.2) (cornerT A y j.1) (cornerT B y j.2)
 have hh(i j:CupCoin): Disp R w (X^8* P' i j) Y:=by
    unfold Y P' Abacus.chroma; rw [← fuseColor]; simp_rw [mul_sum]; apply Disp.SumD; intro l _; apply Disp.SumD; intro m _; apply moments2scene Z l m h.pLease -- maybe args sets; rev.Cost
    · exact v _ _ _ _ _ _ _ _ h ..
    · exact v _ _ _ _ _ _ _ _ h ..
    · exact v _ _ _ _ _ _ _ _ h ..
    exact v _ _ _ _ _ _ _ _ h ..
 let K':ℂ:=k
 have ie: K'= 1/16:= by unfold K' k; push_cast; ring
 have hv(i j): Disp R (k*w) (K'*(X^8* P' i j)) (K'*Y):= by rw [show k*w=‖K'‖*w from (by rw [show ‖K'‖= k from (he.trans (abs_of_nonneg ht))])]; exact (hh i j).increase _
 have he'(U:ℂ): ∑ _i:CupCoin, K'*U= U:= by rw [sum_const, card_univ,nsmul_eq_mul,ie]; simp [CupCoin]
 have v'(i): Disp R (∑ _j:CupCoin,k*w) (∑ j:CupCoin,K'*(X^8* P' i j)) Y:=by
    conv_rhs=> rw [← he' Y]
    exact Disp.SumD univ fun j _=> hv i j
 -- use SlopeCharge.etc after
 have v'': Disp R K (∑ i:CupCoin,K' * ∑ j:CupCoin,K' * (X^8* P' i j)) (∑ _i:CupCoin,K'*Y):=by
    apply Disp.SumD; intro i _; have v':=(v' i).increase K'; rwa [show ‖K'‖= k from (he.trans (abs_of_nonneg ht))] at v'
 rw [he'] at v''; refine Eq.subst (motive:=fun z=> Disp R K z Y) ?_ v''; change _= X^8*∑ i:CupCoin,(1/16:ℂ)*∑ j:CupCoin,(1/16:ℂ)*P' i j
 rw [mul_sum]; apply sum_congr rfl; intro i _; rw [← mul_assoc (X^8) (1/16:ℂ),mul_sum,mul_sum]; apply sum_congr rfl; intro j _; rw [←ie]; ring
#print axioms scenery
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
