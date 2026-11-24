import YM.SU5.FiniteGaugeData.Brique.Dress
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Spire Tenant Fock Fock.Brique Tulip Dial Fir Buffered Skye Scree Nacre
open Paige Vault Cascade Branch
attribute [local instance] opCStarAlgebra
variable {N L B:Side} {σ : Window.Family} {S:Finset (Site N)} {R T U : Support (More N)} {t:List (Site N)} {k n j w:ℕ} {a b c e f r C d f₁ f₂:ℝ}
local notation "Μ" => Single N
-- global rotations already have Eq of frame: all sites allowed. Peg allows any fields ALL GUARD in Troy. 
variable {Z:Peg N}(O:Casing N Z.e (Z.Ft false) c C d)
section
variable {F:Pane N→Op (Single N)}
lemma Casing.coloredWT (H:Casing N e F a C d) (x:Pane N)(h:Guard x e)(g: Seat N→SU.E): F (gauge g x)= twist (tradew N g) (F x):= by
 obtain ⟨v,u,w,f,p,T⟩:=H; let V:= tradew N g
 let z:Openc (More N) d:= ⟨profile x,x,h.shrink u,by simpa⟩; let K:= f z.val
 have ht(i):F (gauge i x)= f ((forum N d).drive i z).val:=by rw [T, profile_g]; rfl
 have hx:F x=K:= T x; obtain ⟨F,C,p,t,q⟩:=p.lib; rw [ht,hx];
 have H:f ((forum N d).drive g z).val* V.val=V.val*K:=by dsimp only at q; rw [q ((forum N d).drive g z),show K=_ from q z,Finset.sum_mul,Finset.mul_sum]; exact sum_congr rfl fun i _=> (p i).frame g z
 rw [twist_formula, ← H, mul_assoc,show V.val*star V.val=1 from V.property.2,mul_one] -- tune
lemma globalWind (g:SU.E): gauge (globalH N g) (1:Pane N)=1:= by funext i; simp [Lattice.gauge,globalH]
lemma jewel (k:ℕ)(T:Interest N): blend k T false (1:Pane N)=funde k T.M N 1:=by
 have h:T.P.den (1:Pane N)=0:=by rw [←Moire.bloom_P,profile_trivial,Moire.bloom_zero]
 unfold blend shift₁ Kennel.capT; simp only [Bool.false_eq_true, ↓reduceIte, h,mul_zero,zero_mul,add_zero]; unfold spar; rw [profile_trivial]
end
variable {o:Seat N}{W:Pane N→ℂ} {F:Corset T R o}{Y: FC (Single N)}{X:Op (Single N)}
lemma twist_tap0 {P:Op Μ}{x:Wave Μ}(u:TapFn false P x)(g:Seat N→SU.E): TapFn false (twist (tradew N g) P) (acts (quantU (tradew N g)).val x):= Full.swirled u _ -- unused A!
lemma rot (P:Op Μ)(g:IsStarProjection P)(v:UNI Μ): IsStarProjection (twist v P):=by constructor; unfold IsIdempotentElem; rw [←map_mul,(show P*P=P from g.1)]; unfold IsSelfAdjoint; rw [←map_star,g.2.star_eq]
lemma shafted (g:Seat N→SU.E)(A: FC (Single N)) : acts (star (flipsP g A)) (mateK N)= acts (quantU (tradew N g)).val (acts (star A) (mateK N)):=by rw [Fock.swivel, show acts (quantU (tradew N g)).val (mateK N)=_ from Girt.mastC g, map_star]
lemma Etude.turn (p:Etude σ S T X a b Y)(g:Seat N→SU.E): Etude σ S T (twist (tradew N g) X) a b (flipsP g Y):= by
 refine ⟨?_,(twist_norm ..).trans_le p.weight, ?_⟩; · rw [←flips_one g, ←map_sub]; exact p.rays.wind g
 obtain ⟨A,t,H,v,e,s⟩:=p.prime; let U:=tradew N g; refine ⟨twist U A,t.twist_t U (shifter g _), rot _ H U, (trace_twist ..).trans v, ?_,?_⟩; · rw [shafted g Y]; exact twist_tap0 e g
 rw [←map_mul]; exact (twist_norm ..).trans_le s
lemma Stump.value (u:Stump R W)(p:S.image node ⊆ T) (z:T⊆R)(H:Etude σ S T X a b Y): Free R (cargo F W Y):=by
 have he:= H.rays.fines p sdiff_subset; apply delivered _ u z; exact sub_add_cancel Y (1:FC Μ) ▸ (he.add .one)
private abbrev sideEq (S:Support (More N)):= {x: Fields N | Agrees S x.1 x.2}
open scoped Classical
lemma knows (S:Support (More N)): MeasurableSet (sideEq S) := by
 unfold sideEq Agrees; -- structure?
 simp_rw [Set.setOf_forall]; exact MeasurableSet.iInter fun a=>MeasurableSet.iInter fun h=>MeasurableSet.iInter fun h=> (isClosed_eq ((continuous_apply _).comp continuous_fst) ((continuous_apply _).comp continuous_snd)).measurableSet
-- certificate relation for Crater expansion: uses BOTH link fields for WORKING marks. no approximation claimed by WP1 transfers etc but exact equality on true at x, mu, everywhere. Need propagate bounds via Mark opacity not `InTest` for Quest.buyRaw. 
noncomputable def cared (T:Support (More N))(F:Mark N): Mark N:= ((sideEq T).indicator F)
lemma cared_cost (g:Mark N)(R: Support (More N))(x:Fields N): ‖cared R g x‖≤‖g x‖:=by by_cases h:x∈ sideEq R <;> simp [cared,h]
lemma cared_area (F:Mark N)(v:Free R F)(p:U⊆R) : AtSupport false R (cared U F):= by
 have hv (x y:Fields N)(e: Agrees R x.1 y.1)(f: Agrees R x.2 y.2): (x∈ sideEq U) ↔ (y∈sideEq U):=by
    constructor <;> intro g i a b
    · exact (e i (p a) (p b)).symm.trans ((g i a b).trans (f i (p a) (p b)))
    exact (e i (p a) (p b)).trans ((g i a b).trans (f i (p a) (p b)).symm)
 refine ⟨Buffered.env_indicator _ (knows U) v.zone.env,fun x y e g=> ?_, fun i=>?_⟩
 · unfold cared; by_cases h:x∈ sideEq U; · rw [Set.indicator_of_mem h,Set.indicator_of_mem ((hv x y e g).1 h)]; exact v.zone.dep x y e g
   rw [Set.indicator_of_notMem h,Set.indicator_of_notMem (mt (hv x y e g).mpr h)]
 unfold cared; by_cases h:i∈ sideEq U; rw [Set.indicator_of_mem h]; exact v.zone.allV i; rw [Set.indicator_of_notMem h]; exact .empty _
structure CashMask (F:Corset T R o)(W:Pane N→ℂ)(U:Support (More N))(ε:ℝ)(Y:Loom N) : Prop where
 faces : Stump R W
 top (x:Pane N): W x ≠ 0 → Tulip.fare U (Tulip.profile (gauge (F.g x) x)) (1:Chin N) ≤ ε
 lamp (x:Orbit N): W x.1 ≠ 0 →Agrees U x.1 (Y x)
variable {Y':Loom N}(h:CashMask F W U (d*r) Y')
include h
lemma stampEq (A:FC Μ) (x:Orbit N) : let Y:=cargo F W A; let z:=Advance.drawn Y' x; cared U Y z= Y z:=by
 intro K z; unfold cared; by_cases p:W x.1=0; swap; · rw [Set.indicator_of_mem (h.lamp x p : z∈sideEq U)]
 exact Set.indicator_apply_eq_self.mpr (fun g=>by unfold K z cargo; change W x.1 • _=0; rw [p,zero_smul]) -- check
-- All required copy bills. 
include O in
lemma paid_copy (p:Etude σ S T (Z.Ft false (1:Pane N)) a b Y) (t:Lattice.halo w T ⊆ U)(e: 0 ≤ Z.e) (g:0≤ f₁)(q: a +(2*tailCost c C w+r*C) ≤ f-f₁)(u:U⊆R): Crater w f₁ f Z R (cared U (cargo F W Y)) S.card false := by
 refine Crater.intro' g fun x t' H=>?_ ; have hx:x∈ sideEq U:=by by_contra hv; apply H (Set.indicator_of_notMem hv _)
 rw [cared,Set.indicator_of_mem hx] at H ⊢; let P:=Z.Ft false; let v:= F.g x.1; have he : W x.1≠0:=fun t=> H (by unfold cargo; rw [t,zero_smul]); let y:= gauge v x.2
 have hw: Tulip.fare U (Tulip.profile y) 1 ≤ d*r:= (by
    let z:= h.top x.1 he; rw [show Tulip.fare U _ 1= Tulip.fare U (profile (gauge v x.1)) 1 from ?_]; exact z; apply sum_congr rfl; intro i p; apply congrArg (fun x=> ‖x-(1:Chin N) i‖); funext a; unfold profile; rw [ (Skye.tied U x.1 x.2 v v hx (fun i _=>rfl)) i (mem_filter.mp p).2.1 (mem_filter.mp p).2.2]) -- lhs y
 let r₀:= Z.e; have hv':Guard y r₀:= t'.cov v
 let K0:= 2*tailCost c C w+r*C; have hez : ‖cutM (modesIn N T)*(P y-P (1:Pane N))‖ ≤ K0:= shape_fee O w _ (1:Pane N) hv' (guard0 e) _ _ t (profile_trivial.symm ▸ hw)
 obtain ⟨P',j,ℓ,χ,D,q₁⟩:= p.prime; let Z₀:= twist (tradew N v⁻¹); let Z':=Z₀ P'; refine ⟨Z', rot _ ℓ _, T,t.trans u,j.twist_t _ (shifter v⁻¹ _), (trace_twist ..).trans χ,?_,?_⟩ -- order witness
 · let S' := acts (star (flipsP v⁻¹ Y)) (mateK N); have ht: Full Z' S':= by unfold S'; rw [shafted v⁻¹ Y]; exact twist_tap0 D v⁻¹
   intro k h; unfold cargo; rw [star_smul,act_smul,map_smul, show acts (creed false k) _ = _ from ht k h,smul_zero]
 have hz: P x.2= Z₀ (P y):=by rw [show P y=twist (tradew N v) (P x.2) from O.coloredWT x.2 t' v]; unfold Z₀; rw [Mono_tradew,twist_inv]
 have hk:‖P'*P y-P'*P 1‖ ≤ K0:= by rw [←mul_sub]; nth_rw 1 [←j.rightP]; rw [mul_assoc]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (ℓ.norm_le _)).trans hez)
 change ‖Z₀ P' * P _‖ ≤ _; rw [hz,←map_mul,show Z₀=_ from rfl]; refine le_trans (le_of_eq (twist_norm ..)) ?_; change ‖P'*P (1:Pane N)‖≤a at q₁; change a+K0 ≤ _ at q; exact le_trans (sub_le_iff_le_add'.mp ((norm_sub_norm_le ..).trans hk)) (by linarith only [q₁,q])
end YM.CF.Window.Brique
