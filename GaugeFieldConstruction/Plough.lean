import GaugeFieldConstruction.Pleiad
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Heliac
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
variable {p:BudgetPoint} (o:Skye.Seat n)
open TableF.Lenten.Loden Haro Tap Hove Moto
attribute [local instance] opCStarAlgebra
open Dial Nacre Ember Fir Fock
open Work.F03 Taxi TableF Bank HushP ModuleB Flot RG Hake
open Layout Fren
local instance(I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance(I:Type)[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
open Module
-- selection across orientations with uniform norms. Use basis extension per orbit
abbrev Fibres(n:Side):Type:=Waves→ₗ[ℂ] Torches n
abbrev sectB {I X Y: Type}[Fintype I][AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y](B:Module.Basis I ℂ X)(F:I→Y):X→ₗ[ℂ]Y:=∑ i:I,(B.coord i).smulRight (F i)
lemma sect_B{i X Y: Type}[Fintype i][AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y](B:Module.Basis i ℂ X)(F:i→Y)(x:X): sectB B F x=∑ j:i, (B.coord j x) • F j:=LinearMap.sum_apply ..
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℂ X][FiniteDimensional ℂ X]
def coverp (i: X→ₗ[ℂ]Waves)(C:ℝ): Prop:=∀ {n p G z M a h c d}, Sundial n p G z M a h c d→0≤c→0≤d→∀ o:Seat n, ∃ F:X→ₗ[ℂ]Torches n,∀ x:X,Portage (F x) o p h a (i x) M (C*(1+c)*‖x‖) (C*d*‖x‖)
def coverz (i: X→ₗ[ℂ]Waves)(C:ℝ): Prop:=∀ {n p G z M a h c d}, Sundial n p G z M a h c d→0≤c→0≤d→∀ o:Seat n,∃ F:X →ₗ[ℂ] Torches n, ∀ x:X, Earner p G z M o a h (F x) (i x) (C*(1+c)*‖x‖) (C*d*‖x‖)
section
variable {I:Type}[Fintype I](B:Module.Basis I ℂ X)(U: X→ₗ[ℂ] Waves)
lemma daylight(x:X): U x=∑ i:I,B.coord i x • U (B i):=by nth_rw 1 [← B.sum_repr x]; rw [map_sum]; exact sum_congr rfl fun i _=> U.map_smul ..
abbrev vScale(C':I→ℝ) : ℝ:=∑ i:I,‖(B.coord i).toContinuousLinearMap‖ * C' i
private lemma vcp(i:I) : ‖(B.coord i).toContinuousLinearMap‖≥0:=by positivity -- TC ℝ missing.
lemma v_pos(C':I→ℝ)(p:∀ i,0 ≤ C' i) : 0 ≤ vScale B C':=sum_nonneg fun i _=> mul_nonneg (vcp B i) (p i)
lemma monk_C (C':I→ℝ)(p:∀ i,0 ≤ C' i)(c:ℝ)(h:0≤c)(x:X): (∑ i, ‖B.coord i x‖*(C' i*c)) ≤ vScale B C'*c*‖x‖:=by
 unfold vScale; simp_rw [sum_mul]; apply sum_le_sum; intro i _; let V: X→L[ℂ]ℂ:= (B.coord i).toContinuousLinearMap
 exact (mul_le_mul_of_nonneg_right (V.le_opNorm x) (mul_nonneg (p i) h)).trans_eq (by show ‖V‖* ‖x‖*(C' i*c)=‖V‖*C' i*c*‖x‖; ring)
end
lemma hinge_H(U:X→ₗ[ℂ] Waves)(p:∀ x,U x∈Resonance):∃ C:ℝ,0≤C∧ coverz U C:=by
 let I:=Fin (Module.finrank ℂ X); let B:=Module.finBasis ℂ X; choose b t g using fun i:I=> recoil (U (B i)) (p _)
 refine ⟨vScale B b,v_pos B b t,@fun n P G z M a h c d A hz hv o=>?_⟩; -- choose g structure may Skolem aggregate
 choose f hf using fun i:I=> g i A hz hv o; refine ⟨sectB B f, fun x=> ?_⟩
 let i:=A.poles; let l:=A.pact; let R:=A.high.le
 have he(j:I):b j*(1+c)=b j*(c+1):=by rw [add_comm]
 have ht(j:I):Earner P G z M o a h (B.coord j x • f j) (B.coord j x • U (B j)) (‖B.coord j x‖*(b j*(1+c))) (‖B.coord j x‖*(b j*d)):=by rw [he]; exact ⟨Foam i l R (hf j).1 _,KnotZ (hf j).2 _⟩  -- tune
 have hx:= Ear_flow univ _ _ _ _ (fun j _=>ht j) A.good.receipt l i R; rw [daylight B U,sect_B]; exact ⟨Fare_R hx.1 (monk_C B b t _ (add_nonneg zero_le_one hz) x) (monk_C B b t _ hv x) le_rfl,hx.2⟩ -- syntax daylight
lemma hinge_P(U:X→ₗ[ℂ] Waves):∃ C:ℝ,0≤C∧ coverp U C:=by
 let I:=Fin (Module.finrank ℂ X); let B:=Module.finBasis ℂ X; let f(j:I):=|bushRate| * ‖U (B j)‖; have hf(i):0 ≤ f i:=mul_nonneg (abs_nonneg _) (norm_nonneg _)
 refine ⟨vScale B f,v_pos B f hf,@fun n P G z M a h c d A hz hv o=>?_⟩; let i:=A.poles; let l:=A.pact; let R:=A.high
 choose g _ H using fun j:I=>Every_T (a:=a) (M:=M) (o:=o) (U (B j)) R ((by norm_num :20<(300:ℕ)).trans A.sideK) i l
 refine ⟨sectB B g,fun x=>?_⟩; have ht(j:I): Portage ((B.coord j x) • g j) o P h a (B.coord j x • U (B j)) M (‖B.coord j x‖*(f j*(1+c))) (‖B.coord j x‖*(f j*d)):= Foam i l R.le (Fare_R (H j) ((mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)).trans (le_mul_of_one_le_right (hf _) (le_add_of_nonneg_right hz))) (mul_nonneg (hf j) hv) le_rfl) _
 have hx:=tile_B univ _ _ _ _ (fun j _=>ht j) l i R.le; rw [daylight B U,sect_B]; exact Fare_R hx (monk_C B f hf _ (add_nonneg zero_le_one hz) x) (monk_C B f hf _ hv x) le_rfl
structure FireL (T:trans1 n)(z:ℂ)(o:Seat n)(p:BudgetPoint)(b a:ℝ)(M:Male)(f:Fibres n)(C D:ℝ):Prop where
 pay (X:Waves): Portage (f X) o p b a X M (C*‖X‖) (D*‖X‖)
 sale(X:Waves):X∈Resonance → KnotU (f X) o T z
private noncomputable def QproT{E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]{P Q:Submodule ℂ E}(p:IsCompl P Q): E→L[ℂ] P:=(P.projectionOnto Q p).toContinuousLinearMap
set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 500000 in
lemma unify {N:Type}[NormedAddCommGroup N][NormedSpace ℂ N][FiniteDimensional ℂ N] (Q':N →ₗ[ℂ] Waves)(K': X →ₗ[ℂ] Waves)(Y:Waves→L[ℂ]X)(V: Waves→L[ℂ]N) (hp:∀ x:Waves,K' (Y x)+Q' (V x)=x)(eV:∀ x∈Resonance,V x=0)(q:∀ i:X,K' i∈ Resonance):∃ C:ℝ,0≤C∧∀ {n p G z M a h c d}, Sundial n p G z M a h c d→0≤c→0≤d→∀ o: Seat n,∃ T:Fibres n, FireL G z o p h a M T (C*(1+c)) (C*d):=by
 obtain ⟨C',h,f⟩:=hinge_P Q'; obtain ⟨R,v,e⟩:=hinge_H K' q
 let L:= R*‖Y‖+ C'*‖V‖; refine ⟨L,?_ , @fun n p G z M a h' c d A hC hD o=>?_⟩; · unfold L; positivity
 obtain ⟨F,t⟩:= f A hC hD o; obtain ⟨T,g⟩:= e A hC hD o; let T0: Waves→ₗ[ℂ] Torches n:= (T.comp Y.toLinearMap) + (F.comp V.toLinearMap); refine ⟨T0, fun x=>?_, fun x j=>?_⟩
 · have he := Fence A.poles A.pact A.high.le (g (Y x)|>.1) (t (V x))
   have hx(c)(p:0≤c): R*c*‖Y x‖+ C'*c*‖V x‖ ≤ L*c*‖x‖:= (add_le_add (mul_le_mul_of_nonneg_left (Y.le_opNorm x) (mul_nonneg v p)) (mul_le_mul_of_nonneg_left (V.le_opNorm x) (mul_nonneg h p))).trans_eq (by unfold L; ring)
   have hy:=Fare_R he (hx _ (add_nonneg zero_le_one hC)) (hx _ hD) (le_refl a); have hh:=Eq.mp (show Portage _ _ _ _ _ _ _ _ _=Portage _ _ _ _ _ x _ _ _ from congrArg (fun i=> Portage (T0 x) o p h' a i M (L*(1+c)*‖x‖) (L*d*‖x‖)) (hp x)) hy; exact hh
 have hv : V x=0:=eV x j
 rw [show T0 x=T (Y x)+ F (V x) from rfl,hv,map_zero,add_zero]; exact (g (Y x)).2
lemma Shipping :∃ C:ℝ,0≤C∧∀ {n p G z M a h c d}, Sundial n p G z M a h c d→0≤c→0≤d→∀ o: Seat n,∃ T:Fibres n, FireL G z o p h a M T (C*(1+c)) (C*d):=by
 obtain ⟨Q,s⟩:= Submodule.exists_isCompl Resonance; let K:=Resonance; let Y:= QproT s; let V:=QproT s.symm; have hp(x:Waves): K.subtype (Y x)+Q.subtype (V x)=x:=Submodule.projection_add_projection_eq_self s x
 exact unify Q.subtype K.subtype Y V hp (fun x j=> Subtype.ext (Submodule.projection_apply_of_mem_right s.symm j)) fun i=>i.property
variable {T:trans1 n}{z:ℂ}{M:Male}{a h c d:ℝ}
variable (F:Seat n→Fibres n) (s:Sweep n)
-- average
lemma mass_L (X:Waves): 0 ≤ Layout.Fren.tilos:=abs_nonneg _
noncomputable def bowl(o:Seat n):Fibres n where
 toFun x:=tiro s (F (sh s⁻¹ o) (Mason s⁻¹ x))
 map_add' x y:=by rw [show Mason s⁻¹ (x+y)=Mason s⁻¹ x+Mason s⁻¹ y from sheen_plus ..,map_add,tiro_add]
 map_smul' v x:=by rw [payY_a,map_smul,tiro_P, show payZ s (payZ s⁻¹ v)=v from ?_,RingHom.id_apply]; rw [warX,mul_inv_cancel,ride_one] -- tune order
lemma bowl_t (X:Waves)(r:Sweep n):tiro r (bowl F s o X)=bowl F (s*r) (sh r o) (Mason r X):=by
 have he: sh (s*r)⁻¹ (sh r o)=sh s⁻¹ o:=by rw [azimuth,mul_inv_rev, ← mul_assoc, mul_inv_cancel,one_mul]
 change tiro _ (tiro _ _) = tiro _ _; rw [crown_D,he,sh_Pi] -- tune
private lemma roll_F(t:∀ o,FireL T z o p h a M (F o) c d)(x:Waves)(e:p.power≤3)(v:p.order≤6)(b:0≤h)(w:300<n.val)(c':0≤c)(d':0≤d): Portage (bowl F s o x) o p h a x M (CaseL*tilos*c*‖x‖) (CaseL*tilos*d*‖x‖):=by
 let z:= sh s⁻¹ o; let X:=Mason s⁻¹ x; let D:=F z X
 have he := (t z).pay X; have hp : Mason s X=x:= (by unfold X; rw [lands_t,inv_mul_cancel,lands_o]); have hx:=Fly s he v e b w
 have hA: sh s z=o:=azBack s o; change Portage (tiro s D) (sh s z) _ _ _ (Mason s X) _ _ _ at hx; rw [hA,hp] at hx
 have hh(c:ℝ)(p:0≤c): CaseL*(c*‖X‖) ≤ (CaseL*tilos * c) * ‖x‖:= (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sheen_norm _ _ x) p) (Nat.cast_nonneg _)).trans_eq (by ring)
 exact Fare_R hx (hh _ c') (hh _ d') le_rfl
lemma bowl_pay(t:∀ o, FireL T z o p h a M (F o) c d)(u:OrientL T z)(e:p.power≤3)(v:p.order≤6)(b:0≤h)(w:300 < n.val)(c':0≤c)(d':0≤d): FireL T z o p h a M (bowl F s o) (((CaseL:ℝ)*tilos)*c) (((CaseL:ℝ)*tilos)*d):=by
 let z:= sh s⁻¹ o; let Z:=F z; constructor
 · intro x; exact roll_F o F s t x e v b w c' d'
 intro x e; have hp:= (t z).sale _ (resonate s⁻¹ x e); let W:= Mason s⁻¹ x; let A:=F z W; have hx:KnotU (tiro s A) (sh s z) T _:=revel s hp ((t z).pay _) u; rw [show sh s z=o from azBack s o] at hx; exact hx -- tune o arg
abbrev SutB(o:Seat n): Fibres n:= (↑(Fintype.card (Sweep n)):ℂ)⁻¹ • ∑ i:Sweep n,bowl F i o
lemma sentB (W:Waves) : tiro s (SutB F o W) = SutB F (sh s o) (Mason s W):=by
 let v:ℂ:=(Fintype.card (Sweep n):ℂ)⁻¹
 unfold SutB; rw [LinearMap.smul_apply,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.sum_apply,tiro_P,show payZ s v=v from (?_)] -- tune
 · let A(i:Sweep n):= bowl F i o W; have he(K:Finset (Sweep n)):tiro s (∑ i∈K,A i)=∑ i∈K, tiro s (A i):=by
      induction K using Finset.induction_on with
      | empty=> rw [sum_empty,sum_empty]; exact Prod.ext (bornØ s) (funext fun i=>bornØ s)
      | @insert i K p ih=> rw [sum_insert p,sum_insert p,tiro_add, ih]
   rw [show tiro s _ = _ from (he univ)]; apply congrArg (v • ·); exact Fintype.sum_equiv (Equiv.mulRight s) _ _ fun i=>bowl_t o F i W s
 unfold payZ; cases wageZ s; rfl; change (starRingEnd ℂ) v=v; simp [v]
private lemma sTF(x:Waves): let v:ℂ:=(Fintype.card (Sweep n):ℂ)⁻¹; SutB F o x=v • ∑ i:Sweep n,bowl F i o x:=by intro v; unfold SutB; rw [LinearMap.smul_apply,LinearMap.sum_apply]
private lemma jetU (X:Waves):let v:ℂ:=(Fintype.card (Sweep n):ℂ)⁻¹; v • (∑ _i:Sweep n,X)=X:=by
 intro v; exact (show ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E](k:E),v •(∑ _i:Sweep n,k)=k from fun {_} _ _ P=>by rw [sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,show v*_ = 1 from inv_mul_cancel₀ mag_c,one_smul]) X
private lemma χSum(c:ℝ):let v:ℂ:=(Fintype.card (Sweep n):ℂ)⁻¹; ‖v‖*(∑ _i:Sweep n,c)=c:=by
 intro v; unfold v; rw [norm_inv,show (Fintype.card (Sweep n):ℂ)= ↑(Fintype.card (Sweep n):ℝ) from (by push_cast; rfl),Complex.norm_real,Real.norm_of_nonneg mag_h.le,sum_const,card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ mag_h.ne',one_mul]
variable (t:∀ o,FireL T z o p h a M (F o) c d)(u:OrientL T z)(e:p.power≤3)(v:p.order≤6)(b:0≤h)(w:300 < n.val)(c':0≤c)(d':0≤d)
include t u e v b w c' d'
private lemma StatB: FireL T z o p h a M (SutB F o) (((CaseL:ℝ)*tilos)*c) (((CaseL:ℝ)*tilos)*d):=by
 have hp(i:Sweep n):=bowl_pay o F i t u e v b w c' d'; constructor
 · intro x; let H:=fun i:Sweep n=> bowl F i o x; let L:=(CaseL:ℝ)*tilos; let A:=L*c*‖x‖; let D:=L*d*‖x‖; let r:ℂ:=(Fintype.card (Sweep n):ℂ)⁻¹; have he(i):Portage (H i) o p h a x M A D:= (hp i).pay x
   have hx:= Foam v e b (tile_B univ H (fun _=> x) (fun _=> A) (fun _=> D) (fun i _=> he i) e v b) r
   rw [show r • (_:Torches n)= SutB F o x from (sTF o F x).symm,show r • _ = x from jetU (n:=n) x,show ‖r‖* _= A from χSum (n:=n) A,show ‖r‖* _=D from χSum (n:=n) D] at hx; exact hx
 intro x k; let H(i:Sweep n):= bowl F i o x; let L:=(CaseL:ℝ)*tilos; let A:=L*c*‖x‖; let D:=L*d*‖x‖
 have hx(i): Earner p T z M o a h (H i) x A D := ⟨(hp i).pay x,(hp i).sale x k⟩; have ht:=Ear_flow univ H (fun _=>x) (fun _=> A) (fun _=>D) (fun i _=>hx i) u.receipt e v b
 exact (sTF o F x).symm ▸ KnotZ ht.2 (↑(Fintype.card (Sweep n)):ℂ)⁻¹ -- tune parenth
omit t u e v b w c' d'
lemma prices_at: ∃ K:ℝ,0≤K ∧∀ {n p G z M a h c d}, Sundial n p G z M a h c d→0≤c→0≤d→∃ T: Seat n→Fibres n,(∀ o:Seat n, FireL G z o p h a M (T o) (K*(1+c)) (K*d))∧ ∀ (s: Sweep n)(o:Seat n)(W:Waves),tiro s (T o W) = T (sh s o) (Mason s W):=by
 obtain ⟨C',g,t⟩:=Shipping; let L:=(CaseL:ℝ)*tilos; refine ⟨L*C',mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) g,@fun n p G z M a h c d q hp ht=>?_⟩; choose F e using t q hp ht; refine ⟨fun o=>SutB F o,fun o=> (?_: FireL _ _ _ _ _ _ _ _ _ _),fun s o W=> sentB o F s W⟩; rw [mul_assoc _ C',mul_assoc _ C']; exact StatB o F e q.good q.pact q.poles q.high.le q.sideK (mul_nonneg g (add_nonneg zero_le_one hp)) (mul_nonneg g ht)
#print axioms prices_at
end MastTin
end YM.CF.XGarden
end
