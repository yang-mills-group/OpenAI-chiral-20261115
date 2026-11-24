import YM.CF.DPress.Yarn.Ledger
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Chaff Gloss Maize Tye RP RP.Str Brace
-- master provision. eventual data used for table. h pre-x global.
structure Source (P_:Campus C)(J:Robes M' V W) where
 b : ℕ
 ν : ℝ
 θFp : ℝ
 a0 : ℝ
 t : ℝ
 u0 : 0 < θFp
 uA : 0 < a0
 ut : 0 < t
 ox : Phase.Budget B d θFp
 pov : B=R.L^b
 pB : 0<b
 F0 : (m:Side)→Scroll m B (Brace.northZ m B)
 τF : ∀ m:Side, ScaleK a0 t (F0 m)
 KFp : ℝ→ℝ
 guard : SunK V C.w C.p C.i J C.h KFp F0
 lens: sizeK R.L 2 KFp
 ηstep : MoveX (p:=C.p) (k:=C.i) V U W C.q' C.w J.d J.n C.n₀ J.k J.roomX C.h
 front : VaultXU (p:=C.p) (k:=C.i) V U W C.q' C.w J.d J.n ν (Ntop P_) J.k J.roomX C.h
namespace Source
variable (D:Source P_ J)
def rank : ℕ→RankX
| 0 => none
| k+1=>some k
abbrev Access(j:ℕ)(f g R':ℝ):Prop := ∀ (N T: Side)(S:StepData (Domain N B) (Domain T B))(G:Ratio (mid N B) (mid T B)), Duty V C.w C.p C.i (Ntop P_) J C.q' C.h S G x R' (grant_B R.L x) f g 0 (rank j) (rank (j+1))
abbrev Down(P:Patch)(F:ℝ→ℝ):Prop:= ∀ᶠ x in atTop,0 ≤ F x∧∀ y,x≤y→ F y≤ F x
structure PermitAlias (i:ℕ)(F Z:ℝ→ℝ) :Prop where
 yes :Down R F ∧ sizeK R.L 2 F
 yesZ :Down R Z∧ sizeK R.L 2 Z
 lift : ∀ᶠ x:ℝ in atTop, ∃ v:ℝ,0 < v ∧ (i≠0→v=1) ∧ ∀ {N P:Side}(S:StepData (Domain N B) (Domain P B))(G:Ratio (mid N B) (mid P B)),Duty V C.w C.p C.i (Ntop P_) J C.q' C.h S G x v (grant_B R.L x) (F x) (Z x) 0 (rank i) (rank (i+1))
include D
lemma earn {F:ℝ→ℝ} (t:sizeK R.L 2 F)(v:Down R F)(i:ℕ): ∃ G, PermitAlias (J:=J) (P_:=P_) i G F:=by
 cases i with
 | zero=>
    obtain ⟨g,RK,hg,u⟩:= vault_U V C.w C.p C.i (Ntop P_) J C.q' C.h D.front F t (v.mono fun i p=>p.1); refine ⟨g,⟨⟨u.mono fun x i=>⟨i.2.1,i.2.2.1⟩,hg⟩,⟨v,t⟩,?_⟩⟩; filter_upwards [u] with x p; exact ⟨RK x,p.1,(fun g=>False.elim (g rfl)), p.2.2.2⟩ -- syntax
 | succ i=>
    obtain ⟨g,hg,u⟩:= move_Q V C.w C.p C.i (Ntop P_) J C.q' C.h D.ηstep (Nat.le_add_right ..) F t (v.mono fun i p=>p.1); refine ⟨g,⟨⟨u.mono fun x i=>⟨i.1,i.2.1⟩,hg⟩,⟨v,t⟩,?_⟩⟩; filter_upwards [u] with x p; exact ⟨1,zero_lt_one,(fun _=>rfl),fun S T=>p.2.2 S T i⟩
structure Pipe (X:Source P_ J)(E:ℕ→ℝ→ℝ) :Prop where
 enough :∀ᶠ x:ℝ in atTop,X.KFp x ≤ E (X.b+1) x
 lift :∀ i:ℕ,i ≤ X.b+1→Down R (E i)∧ sizeK R.L 2 (E i)
 access:∀ i:ℕ,i < X.b+1→ PermitAlias (P_:=P_) (J:=J) i (E i) (E (i+1))
lemma pipes : ∃ F,Pipe D F:=by
 obtain ⟨F0,p,t⟩:= govern_K R.L D.KFp D.lens; let P(i:ℕ):ℝ→ℝ:=F0
 obtain ⟨Y,h,v,u⟩:= LogH.book (fun _=>ℝ→ℝ) 0 (D.b+1) (by omega) (fun i V=>Down R V ∧ sizeK R.L 2 V) (G:=fun i f g=>PermitAlias (P_:=P_) (J:=J) i g f) F0 ⟨(t.mono fun x i=>i.2),p⟩ (fun i _ p v h=>by obtain ⟨Y,f⟩:=earn D h.2 h.1 i; exact ⟨Y,f.yes,f⟩);
 exact ⟨Y,⟨h.symm ▸ t.mono (fun x v=> v.1),fun i h=>v i (by omega) h,fun i h=>u i (by omega) h⟩⟩ -- h transport backwards
structure Price (Y: ℕ→ℝ→ℝ)(x:ℝ):Prop where
 move : ∀ i: Fin (D.b+1), ∃ R':ℝ,0 < R' ∧ (i.val≠0→R'=1) ∧∀ {N P:Side}(S:StepData (Domain N B) (Domain P B))(G:Ratio (mid N B) (mid P B)), Duty V C.w C.p C.i (Ntop P_) J C.q' C.h S G x R' (grant_B R.L x) (Y i x) (Y (i.val+1) x) 0 (rank i.val) (rank (i.val+1))
 wage : ∀ i:ℕ,i≤ D.b+1 → 0 ≤ Y i x ∧ ∀ y,x≤y → Y i y ≤ Y i x
 useF : D.KFp x≤ Y (D.b+1) x
 smallest : J.n ≤ radiusB x
 boot : ∀ (m:Side) (P:BudgetPoint)(A:Scree.Loom (CSide m B))(Z:Roof _ J.k J.roomX J.n A), hintF P C.p C.i x C.w → U.roundZ ≤ (CSide m B).val → J.n ≤ P.B → P.threshold ≤ J.k → 4*P.B< (Domain m B).val→∃ b:ℝ,∃ I:RegBudget (CSide m B), Lives_B (H:=C.h) V (D.F0 m) I (radiusB x) (D.KFp x) P A U b
 stim : (D.b+1:ℕ)*Real.sqrt x ≤ x/16
abbrev Workshop(D: Source P_ J)(Λ:Thrift A)(E:ℕ→ℝ→ℝ)(x:ℝ): Prop:= ∀ y:ℝ,x≤ y→Price D E y∧4*(Tew.tiny R y+E 0 y) ≤ Λ.w y
lemma bend : ∀ᶠ x:ℝ in atTop,(D.b+1:ℕ) *Real.sqrt x ≤ x/16:=by
 let t:= (↑(D.b+1):ℝ) -- beware coerces wrong
 filter_upwards [Real.tendsto_sqrt_atTop.eventually_ge_atTop (t*16),eventually_ge_atTop (0:ℝ)] with x p v; have hp:=Real.sqrt_nonneg x; have hv:= Real.sq_sqrt v; push_cast; change _≤_; unfold t at p; push_cast at p; nlinarith only [hv,hp,p]
variable {E':ℕ→ℝ→ℝ}
lemma calendars (p:Pipe D E') : ∀ᶠ x:ℝ in atTop,Price D E' x:=by
 let v:= D.b; filter_upwards [eventually_all.mpr (fun i:Fin (v+1)=> (p.access i.val i.isLt).lift),eventually_all.mpr (fun i:Fin (v+1+1)=> (p.lift i.val (Nat.lt_succ_iff.mp i.isLt)).1),p.enough, Work.E01.radiusB_tendsto.eventually_ge_atTop J.n,D.guard.pay,D.bend] with x h u f y Q b; exact ⟨h,fun i p=>u (⟨i,by omega⟩ : Fin (D.b+1+1)),f,y,Q,b⟩
lemma orders (A:Harvester P_) (u:ηD (A:=A)≤1/4)(r:20*A.μ<R.L.val): ∃ (Λ:Thrift A)(E:ℕ→ℝ→ℝ), Pipe D E ∧∀ᶠ x:ℝ in atTop, Thrift.Credit Λ x ∧ Workshop D Λ E x:=by
 obtain ⟨E,h⟩:= D.pipes; let t(x:ℝ):=4*(Tew.tiny R x+E 0 x); obtain ⟨k,Y⟩:= (show sizeK R.L 2 t from ((dev_R R).1.accrue (h.lift 0 (by omega)).2).scale _); let Z:= cone_t R.L k; have pZ(x): 0≤Z x:= mul_nonneg (sq_nonneg _) (pow_nonneg ((Scales.pos ..)|>.le) _)
 have spec: ∀ᶠ x:ℝ in atTop,t x≤ Z x:=Y.mono fun x v=> (le_abs_self _).trans v
 have he: ∀ᶠ x:ℝ in atTop,4*Tew.tiny R x ≤ Z x:=by filter_upwards [spec,(h.lift 0 (by omega)).1] with x p v; have hv:=v.1; unfold t at p; linarith
 obtain ⟨Λ,P,T⟩:= Thrift.EMark (A:=A) (fork_u ..) pZ (throatK ..) he u r; obtain ⟨p,H⟩:= eventually_atTop.mp ((D.calendars h).and spec); refine ⟨Λ,E,h,?_⟩; filter_upwards [T,eventually_ge_atTop p] with x v u; unfold Workshop; refine ⟨v,fun i w=>?_⟩ -- rw scope
 have he:=H i (u.trans w); exact ⟨he.1,P.symm ▸ he.2⟩
end Source
end FitD
end YM.CF.Py.Kay
